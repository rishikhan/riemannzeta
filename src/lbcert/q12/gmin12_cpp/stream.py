"""Python driver for gmin12_cpp/gmin_stream.cpp: CppGmin with the half-template starts generated in
C++, plus the cut-model LP in the core (lp_init / lp_ratio, see lp.inc).

StreamGmin(tab, q, threads) behaves like pipeline.cppgmin.CppGmin(tab, q, templates=
sep_window_search.half_templates(q)) without materializing the templates: gmin() runs the full
template search streaming in the core, prescreen(a, b, k) returns the k half-template starts with
the lowest F (sep_score's warm-round prescreen).  Memory is the table plus O(threads x keep).
"""
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT))
from pipeline import cppgmin as CG                    # noqa: E402
from pipeline.geometry import geom                    # noqa: E402

SRC = HERE / 'gmin_stream.cpp'
MAGIC_PRE = 0x53315052
MAGIC_LPI, MAGIC_LPR, MAGIC_LPS = 0x53314c49, 0x53314c52, 0x53314c53


def highs_prefix():
    p = os.environ.get('HIGHS_PREFIX')
    if not p:
        raise RuntimeError('set HIGHS_PREFIX to a HiGHS 1.12.0 install (include/highs, lib or lib64/libhighs.a)')
    return Path(p)


def build(q):
    """gmin_stream_lp_q<q> in $GMIN12LP_BINDIR (default ./bin), linked statically against
    $HIGHS_PREFIX."""
    bindir = Path(os.environ.get('GMIN12LP_BINDIR', HERE / 'bin'))
    bindir.mkdir(parents=True, exist_ok=True)
    out = bindir / ('gmin_stream_lp_q%d' % q)
    src_m = max(SRC.stat().st_mtime, (HERE / 'lp.inc').stat().st_mtime)
    if out.is_file() and out.stat().st_mtime >= src_m:
        return out
    hp = highs_prefix()
    lib = next(d for d in (hp / 'lib64', hp / 'lib') if (d / 'libhighs.a').is_file())
    cxx = os.environ.get('CXX', 'c++')
    flags = ['-std=c++17', '-O3', '-DNDEBUG', '-ffp-contract=off', '-pthread']
    extra = os.environ.get('GMIN12LP_CXXFLAGS', '').split()
    subprocess.check_call([cxx] + flags + extra + ['-DQQ=%d' % q, '-I' + str(hp / 'include' / 'highs'),
                           '-o', str(out), str(SRC), str(lib / 'libhighs.a'), '-lz', '-ldl'])
    return out


class StreamGmin(CG.CppGmin):
    def __init__(self, tab, q, threads=1, iters1=20, iters2=70, keep_stage1=500, nice=None,
                 stderr_path=None):
        self.q = int(q)
        self.G = geom(self.q)
        self.threads = int(threads)
        self.keep_stage1 = int(keep_stage1)
        self.symdup = False
        self.retries = 1
        self._own_dir = True
        self.dir = Path(tempfile.mkdtemp(prefix='gmin12lp_%d_' % os.getpid()))
        b = np.ascontiguousarray(tab.breaks, dtype=np.float64)
        rec = np.empty((len(b) - 1, 12), dtype=np.float64)
        for k in range(4):
            rec[:, k] = tab.cw[k]
            rec[:, 4 + k] = tab.cp[k]
            rec[:, 8 + k] = tab.cpp[k]
        rec.tofile(self.dir / 'coef.bin')
        b.tofile(self.dir / 'breaks.bin')
        (self.dir / 'spec.txt').write_text(
            f"q {q}\nnp {self.G.NP}\nntempl 0\ngen_half 1\niters1 {iters1}\niters2 {iters2}\n"
            f"keep_stage1 {keep_stage1}\nsymdup 0\nymax {float(tab.ymax).hex()}\n"
            f"hmax {float(tab.hmax).hex()}\ninv_h {float(tab.inv_h).hex()}\n")
        self._binary = build(self.q)
        self._cmd = [str(self._binary), 'serve', str(self.dir), str(self.threads)]
        if nice is not None:
            self._cmd = ['nice', '-n', str(int(nice))] + self._cmd
        self._stderr_path = stderr_path
        self.respawns = 0
        self.p = None
        self._spawn()

    def prescreen(self, a, b, k):
        a = np.ascontiguousarray(np.asarray(a, float))
        b = np.ascontiguousarray(np.asarray(b, float))
        self.p.stdin.write(struct.pack('<ii', MAGIC_PRE, int(k)))
        self.p.stdin.write(b.tobytes())
        self.p.stdin.write(a.tobytes())
        self.p.stdin.flush()
        (nk,) = struct.unpack('<i', self._rd(4))
        F = np.frombuffer(self._rd(8 * nk), dtype=np.float64).copy()
        g = np.frombuffer(self._rd(8 * nk * self.q), dtype=np.float64).reshape(nk, self.q).copy()
        return F, g

    def lp_init(self, Aeq, beq, bnds, hs_ratio, hs_gaps, mode=0):
        """The constraints of sep_window_search.lp_kappa; mode 0 cold (scipy's model), 1 warm."""
        q, nv = self.q, Aeq.shape[1]
        cols = [g for r_ in hs_gaps for g in (r_, q - 1 - r_)] if hs_ratio is not None else []
        lb = np.array([b[0] for b in bnds], float)
        ub = np.array([b[1] for b in bnds], float)
        self.p.stdin.write(struct.pack('<iiiii', MAGIC_LPI, nv, Aeq.shape[0], int(mode), len(cols)))
        self.p.stdin.write(struct.pack('<d', float(hs_ratio) if hs_ratio is not None else 0.0))
        for arr in (Aeq, beq, lb, ub):
            self.p.stdin.write(np.ascontiguousarray(arr, dtype=np.float64).tobytes())
        self.p.stdin.write(np.asarray(cols, dtype=np.int32).tobytes())
        self.p.stdin.flush()
        (st,) = struct.unpack('<i', self._rd(4))
        assert st == 0
        self._nv = nv

    def lp_ratio(self, new_rows, H, kappa0, steps=8):
        """Append the cut rows and run sep_window_search.model_ratio in the core -> (kappa, x | None)."""
        R = np.ascontiguousarray(np.asarray(new_rows, dtype=np.float64).reshape(-1, self._nv))
        self.p.stdin.write(struct.pack('<iii', MAGIC_LPR, len(R), int(steps)))
        self.p.stdin.write(struct.pack('<dd', float(H), float(kappa0)))
        self.p.stdin.write(R.tobytes())
        self.p.stdin.flush()
        (found,) = struct.unpack('<i', self._rd(4))
        (kappa,) = struct.unpack('<d', self._rd(8))
        x = np.frombuffer(self._rd(8 * self._nv), dtype=np.float64).copy()
        return np.float64(kappa), (x if found else None)

    def lp_stats(self):
        self.p.stdin.write(struct.pack('<ii', MAGIC_LPS, 0))
        self.p.stdin.flush()
        n, it, secs = struct.unpack('<ddd', self._rd(24))
        return dict(lp_count=int(n), lp_iters=int(it), lp_secs=secs)
