"""Driver for the threaded C++ minimizer core, `pipeline/cpp/gmin.cpp`.

WHAT MOVES.  Only the batched projected Newton and the between-stage selection
run in C++.  Everything else stays in numpy, so numpy's PCG64 stream is the one
that generates starts and nothing in C++ has to reproduce it:

    start generation      numpy
    finite filter         numpy
    argsort               numpy
    2e-3 dedup, nkeep     numpy
    cut extraction        numpy

The spline coefficients are dumped from the same `WTable` the numpy path would
evaluate, so the C++ side ingests scipy's own breakpoints and coefficients and
never re-derives a spline.

DIRECTION OF ERROR.  This is a minimization, so the value returned is an UPPER
bound on the true infimum of F.  It ranks windows and is not a certificate.

AGREEMENT is about 1e-13, not bitwise: reduction order, the LU rounding and the
0/1-matmul-versus-prefix-sum form of the pair distances each differ at 1e-16.
That is four orders below the 5e-8 scale at which this scorer's rankings
invert, and the certified path never reads it.

`pipeline/cpp/knots.cpp` evaluates the knots of the table in threads.  Its
output is bit-identical to numpy's, so the fitted spline coefficients are too
and no score can move.
"""
from __future__ import annotations

import os
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import numpy as np

from pipeline.geometry import geom
from pipeline.objective import template_starts
from pipeline.wtable import WTable

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
GMIN_SRC = HERE / "cpp" / "gmin.cpp"
KNOTS_SRC = HERE / "cpp" / "knots.cpp"
BINDIR = Path(os.environ.get("PIPELINE_BINDIR", "/tmp/pipeline_bin"))


def _cxx():
    """The C++ compiler for the SEARCH helpers, resolved rather than assumed.

    $PIPELINE_CXX wins, else the first of clang++ and g++ on PATH.  These build
    `pipeline/cpp/gmin.cpp` and `knots.cpp`, which are float search code.  Hardcoding clang++ broke
    on a machine that ships only gcc.
    """
    env = os.environ.get("PIPELINE_CXX")
    if env:
        return env
    for c in ("clang++", "g++"):
        if shutil.which(c):
            return c
    raise RuntimeError("no C++ compiler found: set PIPELINE_CXX")

MAGIC = 0x53313535

# No -ffast-math and nothing implying it.  -ffp-contract=off keeps the Horner
# form unfused, so it matches numpy's ((c0*t + c1)*t + c2)*t + c3 bit for bit.
FLAGS = ["-std=c++17", "-O3", "-DNDEBUG", "-ffp-contract=off", "-flto"]
KNOT_FLAGS = ["-std=c++17", "-O3", "-DNDEBUG", "-ffp-contract=off",
              "-shared", "-fPIC"]


class CoreDied(RuntimeError):
    """The core stopped answering.  Retried by the request methods."""


def arch_flag():
    m = subprocess.run(["uname", "-m"], capture_output=True, text=True).stdout.strip()
    return "-mcpu=native" if m in ("arm64", "aarch64") else "-march=native"


def _compile(src, out, flags, cxx, extra=()):
    BINDIR.mkdir(parents=True, exist_ok=True)
    cmd = [cxx, *flags, arch_flag(), *extra, "-o", str(out), str(src)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(f"build failed: {' '.join(cmd)}\n{r.stderr[-4000:]}")
    return out


def build_gmin(q, out=None, cxx=None, force=False):
    """Compile the minimizer core at compile-time geometry length q."""
    BINDIR.mkdir(parents=True, exist_ok=True)
    out = Path(out) if out else BINDIR / f"gmin_q{q}"
    if not force and out.is_file() and out.stat().st_mtime >= GMIN_SRC.stat().st_mtime:
        return out
    return _compile(GMIN_SRC, out, FLAGS, cxx or _cxx(), extra=[f"-DQQ={q}"])


def build_knots(out=None, cxx=None, force=False):
    """Compile the threaded knot evaluator to a shared library."""
    BINDIR.mkdir(parents=True, exist_ok=True)
    out = Path(out) if out else BINDIR / "libknots.dylib"
    if not force and out.is_file() and out.stat().st_mtime >= KNOTS_SRC.stat().st_mtime:
        return out
    return _compile(KNOTS_SRC, out, KNOT_FLAGS, cxx or _cxx())


# ----------------------------------------------------------------- the knots
_KLIB = None


def knots_lib(force=False):
    global _KLIB
    if _KLIB is None or force:
        import ctypes
        lib = ctypes.CDLL(str(build_knots(force=force)))
        lib.knots_wall.restype = None
        lib.knots_wall.argtypes = [
            ctypes.c_void_p, ctypes.c_int64,
            ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
            ctypes.c_int, ctypes.c_double, ctypes.c_double,
            ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]
        _KLIB = lib
    return _KLIB


def cpp_wall(coeff, omega, k0, threads=1):
    """The exact kernel's Wall, evaluated in threaded C++.

    coeff*pi, coeff*pi^2, omega/2 and k0^2 are formed HERE by numpy and passed
    in: they are single rounded values that numpy broadcasts, and
    (coeff*pi)*(rd-ld) is not coeff*(pi*(rd-ld)).  Recomputing them in C++
    would introduce a divergence that has nothing to do with the port.
    """
    lib = knots_lib()
    coeff = np.ascontiguousarray(np.asarray(coeff, float))
    omega = np.ascontiguousarray(np.asarray(omega, float))
    if len(coeff) > 64:
        raise ValueError(f"the knot evaluator takes at most 64 frequencies, "
                         f"not {len(coeff)}")
    hh = np.ascontiguousarray(omega / 2.0)
    cfpi = np.ascontiguousarray(coeff * np.pi)
    cfpi2 = np.ascontiguousarray(coeff * np.pi ** 2)
    k0 = float(k0)
    k02 = float(k0 ** 2)
    nf = len(coeff)
    nth = int(threads)

    def Wall(x):
        xa = np.ascontiguousarray(np.atleast_1d(np.asarray(x, float)))
        shp = xa.shape
        flat = xa.reshape(-1)
        n = flat.size
        w = np.empty(n)
        wp = np.empty(n)
        wpp = np.empty(n)
        lib.knots_wall(flat.ctypes.data, n, hh.ctypes.data, coeff.ctypes.data,
                      cfpi.ctypes.data, cfpi2.ctypes.data, nf, k0, k02,
                      w.ctypes.data, wp.ctypes.data, wpp.ctypes.data, nth)
        return w.reshape(shp), wp.reshape(shp), wpp.reshape(shp)

    return Wall


def cpp_table(coeff, omega, threads=1, ymax=34.0, h=1.0e-3):
    """A WTable whose knots are evaluated in threaded C++.

    The knot arrays are bit-identical to numpy's, so the fitted spline
    coefficients are too and no value moves.  The C++ evaluator materializes no
    large temporaries, so the whole table builds in one pass.

    WHY h IS 1e-3 AND NOT THE 2.5e-5 OF `WTable`.  The Newton sweep gathers one
    96-byte coefficient record per pair per evaluation, twice per iteration.  An
    index histogram over the real q=11 stage-1 path measures the reuse within a
    32-row group at 1.05 to 2.13, over a footprint of 184 to 366 KB drawn from
    90% of the table, so at h = 2.5e-5 the 130 MB table is far larger than any
    cache that holds it and most gathers miss.  At h = 1e-3 it is 3.3 MB and
    fits, worth 1.12x at q=11 and 1.19x at q=9, and the per-candidate table
    build drops from 0.22 s to 0.01 s.

    What that costs is below anything this scorer resolves.  At q=10 and q=11,
    at the cold bundle start and at converged weights, over three seeds, the
    minimum moves by at most 5.7e-14, four orders below the 5e-8 at which window
    rankings invert and the 1e-8 the bundle converges to.  The 24 cuts are the
    same 24: matched as sets, every cut has a partner within 5.7e-10, which is
    seven orders inside the 2e-3 dedup radius that decides whether two
    minimizers count as distinct.  Matching is modulo the reversal, because a
    minimizer and its reversal tie exactly and the two grids break that tie
    differently; the fundamental-domain cut already treats them as one point.

    This table is the float proxy and never the certificate.  `pipeline/tables.py`
    builds the outward-rounded tables the interval verifier reads, and nothing
    outside this module imports `pipeline/wtable.py`.
    """
    from pipeline.kernel import kernel_exact
    _, _, k0 = kernel_exact(coeff, omega)
    return WTable(coeff, omega, ymax=ymax, h=h,
                  knot_eval=cpp_wall(coeff, omega, k0, threads),
                  knot_chunk=10 ** 9)


# ------------------------------------------------------------------ the core
def write_spec(tab, q, outdir, iters1=20, iters2=70, keep_stage1=500,
               templates=None, symdup=False):
    """Dump the table's own spline coefficients and the start templates.

    coef.bin interleaves the twelve coefficients at one interval into one
    96-byte record (cw0..3, cp0..3, cpp0..3), so evaluating all three splines
    touches two adjacent cache lines instead of twelve scattered ones.
    """
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    b = np.ascontiguousarray(tab.breaks, dtype=np.float64)
    n1 = len(b) - 1
    rec = np.empty((n1, 12), dtype=np.float64)
    for k in range(4):
        rec[:, k] = tab.cw[k]
        rec[:, 4 + k] = tab.cp[k]
        rec[:, 8 + k] = tab.cpp[k]
    rec.tofile(outdir / "coef.bin")
    b.tofile(outdir / "breaks.bin")
    T = template_starts(q) if templates is None else templates
    T = np.ascontiguousarray(np.asarray(T, float))
    assert T.shape[1] == q, T.shape
    T.tofile(outdir / "starts.bin")
    G = geom(q)
    (outdir / "spec.txt").write_text(
        f"q {q}\n"
        f"np {G.NP}\n"
        f"ntempl {len(T)}\n"
        f"iters1 {iters1}\n"
        f"iters2 {iters2}\n"
        f"keep_stage1 {keep_stage1}\n"
        f"symdup {int(bool(symdup))}\n"
        f"ymax {float(tab.ymax).hex()}\n"
        f"hmax {float(tab.hmax).hex()}\n"
        f"inv_h {float(tab.inv_h).hex()}\n")
    return outdir


class CppGmin:
    """One long-lived core process per window, so the table loads once."""

    def __init__(self, tab, q, threads=1, iters1=20, iters2=70,
                 keep_stage1=500, symdup=False, templates=None, nice=None,
                 stderr_path=None, retries=1, workdir=None):
        self.q = int(q)
        self.G = geom(self.q)
        self.threads = int(threads)
        self.keep_stage1 = int(keep_stage1)
        self.symdup = bool(symdup)
        self.retries = int(retries)
        self._own_dir = workdir is None
        # The prefix carries the OWNING pid, so a cleanup sweep can check
        # whether the owner is alive rather than guess.
        self.dir = Path(workdir or tempfile.mkdtemp(
            prefix=f"pipeline_gmin_{os.getpid()}_"))
        write_spec(tab, self.q, self.dir, iters1, iters2, keep_stage1,
                   templates=templates, symdup=self.symdup)
        self._binary = build_gmin(self.q)
        self._cmd = [str(self._binary), "serve", str(self.dir), str(self.threads)]
        if nice is not None:
            self._cmd = ["nice", "-n", str(int(nice))] + self._cmd
        self._stderr_path = stderr_path
        self.respawns = 0
        self.p = None
        self._spawn()

    def _spawn(self):
        self._err = (open(self._stderr_path, "ab") if self._stderr_path
                     else subprocess.DEVNULL)
        self.p = subprocess.Popen(self._cmd, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=self._err)

    def _reap(self):
        if self.p is None:
            return
        try:
            self.p.kill()                   # by explicit handle, never by name
        except Exception:
            pass
        for h in (self.p.stdin, self.p.stdout):
            try:
                if h is not None:
                    h.close()
            except Exception:
                pass
        try:
            self.p.wait(timeout=10)
        except Exception:
            pass
        if self._err is not subprocess.DEVNULL:
            try:
                self._err.close()
            except Exception:
                pass
        self.p = None

    # ---------------------------------------------------------------- protocol
    def _rd(self, n):
        buf = self.p.stdout.read(n)
        if buf is None or len(buf) != n:
            raise CoreDied("the core died on a short read; pass stderr_path= "
                           "to see why")
        return buf

    def _one_newton(self, a, b, rs):
        self.p.stdin.write(struct.pack("<ii", MAGIC, len(rs)))
        self.p.stdin.write(b.tobytes())
        self.p.stdin.write(a.tobytes())
        self.p.stdin.write(rs.tobytes())
        self.p.stdin.flush()
        (nk,) = struct.unpack("<i", self._rd(4))
        F = np.frombuffer(self._rd(8 * nk), dtype=np.float64).copy()
        g = np.frombuffer(self._rd(8 * nk * self.q),
                          dtype=np.float64).reshape(nk, self.q).copy()
        return F, g

    def newton(self, a, b, rstarts):
        """Stage 1, selection, the reversal duplication and stage 2.

        SURVIVES A CORE DEATH.  A request is a pure function of (a, b,
        rstarts) and the spec directory, and the spec directory outlives the
        process, so a core that dies can be respawned and the same request
        resubmitted for the same answer.  A deterministic crash still
        propagates: the identical input reaches a freshly loaded core, so a
        request that kills the core kills it again and the retry budget runs
        out.
        """
        a = np.ascontiguousarray(np.asarray(a, float))
        b = np.ascontiguousarray(np.asarray(b, float))
        rs = np.ascontiguousarray(np.asarray(rstarts, float))
        assert a.shape == (self.G.NP,) and b.shape == (self.q,)
        assert rs.ndim == 2 and rs.shape[1] == self.q
        for attempt in range(self.retries + 1):
            try:
                return self._one_newton(a, b, rs)
            except (CoreDied, BrokenPipeError, OSError, ValueError,
                    struct.error) as e:
                if attempt >= self.retries:
                    raise
                pid = self.p.pid if self.p is not None else None
                self._reap()
                self._spawn()
                self.respawns += 1
                sys.stderr.write(
                    f"[{time.strftime('%Y-%m-%dT%H:%M:%S')}] the core pid={pid} "
                    f"died ({type(e).__name__}: {e}); respawned as "
                    f"pid={self.p.pid} and resubmitting the identical request "
                    f"(attempt {attempt + 2} of {self.retries + 1})\n")
                sys.stderr.flush()

    def gmin(self, a, b, seed=0, n_rand=6000, nkeep=24):
        """Global minimization of F over g >= 0.  -> (f, argmin, cutset).

        An UPPER bound on the true infimum.  `cutset` holds the nkeep lowest
        distinct local minimizers, which become cutting planes.
        """
        q = self.q
        rng = np.random.default_rng(seed)
        bmin = max(float(np.min(b)), 1e-12)
        hi = min(1.5 * (0.02 / bmin), 8.0)
        rs = rng.uniform(0.05, hi, (n_rand, q))
        F, g = self.newton(a, b, rs)
        ok = np.isfinite(F)
        F, g = F[ok], g[ok]
        keep, kf = [], []
        for idx in np.argsort(F):
            gi = g[idx]
            if any(np.max(np.abs(gi - k)) < 2e-3 for k in keep):
                continue
            keep.append(gi)
            kf.append(F[idx])
            if len(keep) >= nkeep:
                break
        keep = np.array(keep)
        return float(kf[0]), keep[0].copy(), keep

    # ------------------------------------------------------------------ close
    def close(self):
        if self.p is not None and self.p.poll() is None:
            try:
                self.p.stdin.write(struct.pack("<ii", 0, 0))
                self.p.stdin.flush()
                self.p.stdin.close()
                self.p.wait(timeout=30)
                self.p = None
            except (BrokenPipeError, ValueError, subprocess.TimeoutExpired):
                pass
        self._reap()
        if self._own_dir and self.dir.exists():
            shutil.rmtree(self.dir, ignore_errors=True)

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()
        return False
