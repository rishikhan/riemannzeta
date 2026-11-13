"""Float-only tree building for Q-gap models (Q up to 16), used for leaf-count sizing at q = 9..12.

* setup(model, pts, engine_lib): model, HSChecker (half-space row on), engine with the q9hs options.
* FloatBuilder: q9hs TreeBuilder2 where a node is a leaf when the C++ float LP margin is >= 0
  (no exact certificate, no anchors recorded, so a subtree is a deterministic function of its box).
  The split word carries AXB = (Q + NP - 1).bit_length() axis bits (6 at q <= 9, 7 at q = 10..12),
  so it is 1 + AXB + 3 bits.
* Exact sampling: exact.py builds certified leaves on chosen boxes with LeafSolverHS and replays them.
"""
import ctypes
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
for d in ('q9hs', 'q9', 'gen'):
    sys.path.insert(0, os.path.join(LB, d))
import hs                                    # noqa: E402
import qgen                                  # noqa: E402
from core import root_state, children        # noqa: E402
import gen_treeshs as G                      # noqa: E402
from treehs import TreeBuilder2              # noqa: E402

SO = 'libengine.dylib' if sys.platform == 'darwin' else 'libengine.so'


def setup(model, pts, lib=None, eng_path=None, half=True):
    M = pickle.load(open(model, 'rb')) if isinstance(model, str) else model
    C = hs.HSChecker(M)
    C.half = half
    P = pickle.load(open(pts, 'rb')) if isinstance(pts, str) else pts
    G.LIB = lib or os.path.join(HERE, 'cpp', SO)
    eng_path = eng_path or (model + '.eng' if isinstance(model, str) else '/tmp/fb12.eng')
    if not os.path.exists(eng_path):
        qgen.dump(M, C, P, eng_path + '.tmp')
        os.replace(eng_path + '.tmp', eng_path)
    E = G.EngineHS(eng_path, M.Q, M.NP)
    tbf = np.zeros(M.KB // 256 + 1, dtype=np.int64)      # variance off: the table is not read
    E.set_opts(half, False, tbf, getattr(M, 'VD', 1e9))
    L = E.lib
    if hasattr(L, 'eng_float_tree'):
        L.eng_float_tree.restype = ctypes.c_int
        L.eng_float_tree.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_int, ctypes.c_double,
                                     ctypes.c_int64, ctypes.c_int, ctypes.c_void_p]
        L.eng_decide.restype = ctypes.c_int
        L.eng_decide.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_double, ctypes.c_int, ctypes.c_int,
                                 ctypes.c_double] + [ctypes.c_void_p] * 4
        L.eng_leaf_margin.restype = ctypes.c_double
        L.eng_leaf_margin.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        L.eng_cache_clear.argtypes = [ctypes.c_void_p]
    return M, C, P, E


TREE_RC = {1: 'leaf budget exceeded', 2: 'depth limit', 3: 'no split'}


def cpp_tree(tb, s):
    """Whole float subtree in C++ (cpp/builder.inc); same choices as FloatBuilder.node."""
    E = tb.E
    st = E.flat(s)
    out = np.zeros(5, dtype=np.int64)
    if tb.pen > 0:
        E.set_pen(tb.shared, tb.pen)
    t0 = time.time()
    rc = E.lib.eng_float_tree(E.h, st.ctypes.data, tb.k if tb.lookahead else 0, tb.nthreads, tb.stall,
                              tb.leaf_budget, tb.max_depth, out.ctypes.data)
    tb.stats.update(leaves=int(out[0]), refl=int(out[1]), splits=int(out[2]), maxdepth=int(out[3]),
                    evals=int(out[4]), secs=time.time() - t0)
    if rc:
        raise RuntimeError(TREE_RC[rc])
    return tb.stats


def cpp_decide(tb, s, m):
    """One split decision in C++ -> (ax, md, x, y) or None."""
    E = tb.E
    st = E.flat(s)
    o = np.zeros(2, dtype=np.int32)
    v = np.zeros(2)
    ok = E.lib.eng_decide(E.h, st.ctypes.data, m, tb.k if tb.lookahead else 0, tb.nthreads, tb.stall,
                          o[0:].ctypes.data, o[1:].ctypes.data, v[0:].ctypes.data, v[1:].ctypes.data)
    return (int(o[0]), int(o[1]), float(v[0]), float(v[1])) if ok else None


def cpp_leaf_margin(E, s):
    st = E.flat(s)              # keep the array alive across the call
    return E.lib.eng_leaf_margin(E.h, st.ctypes.data)


def axis_bits(M):
    return (M.Q + M.NP - 1).bit_length()


class FloatBuilder(TreeBuilder2):
    """Leaf = float LP margin >= gate."""

    def __init__(self, C, E, **kw):
        super().__init__(C, None, E, **kw)
        self.ls = type('LS', (), {'last_var': False})()
        self.AXB = axis_bits(self.M)

    def certify(self, s):
        return 0, 0, 0.0, None

    def note_anchors(self, s, payload, isvar=False):
        pass

    # node() of TreeBuilder2 writes a 10-bit split word; only the stats matter for float counts,
    # and the word is rewritten with AXB axis bits here.
    def node(self, s, out, depth, m=None):
        st = self.stats
        st['maxdepth'] = max(st['maxdepth'], depth)
        if self.leaf_budget and st['leaves'] + st['refl'] > self.leaf_budget:
            raise RuntimeError('leaf budget %d exceeded' % self.leaf_budget)
        if s[1][self.M.Q - 1] < s[0][0]:
            st['refl'] += 1
            return
        if m is None:
            m = self.margin(s)
        if m < self.gate and self.pen > 0:
            mr = self.E.margin_raw(s)
            if mr >= self.gate:
                m = mr
        if m >= self.gate:
            st['leaves'] += 1
            if self.progress and st['leaves'] % self.progress == 0:
                print('  .. leaves %d refl %d splits %d depth %d maxdepth %d %.0fs'
                      % (st['leaves'], st['refl'], st['splits'], depth, st['maxdepth'],
                         time.time() - self.t0), flush=True)
            return
        if depth >= self.max_depth:
            raise RuntimeError('depth limit')
        best = self.decide(s, m, depth)
        _, a, md, x, y = best
        q, left, right = self.kids(s, a, md)
        st['splits'] += 1
        self.node(left, out, depth + 1, x)
        self.node(right, out, depth + 1, y)

    def decide(self, s, m, depth):
        best = self.choose(s)
        if best is not None and depth >= self.stall_depth and m < 0 and best[0] - m < self.stall * (-m):
            r = max(range(self.M.Q), key=lambda r: s[1][r] - s[0][r])
            if s[1][r] - s[0][r] >= 2:
                cands = [t for t in self.scan(s) if t[1] == r]
                if cands:
                    best = cands[0]
        if best is None:
            raise RuntimeError('no split')
        return best

    screen = 0          # > 0: two-stage scan, modes 0 and 1 on every axis, all modes on the best `screen` axes

    def scan(self, s):
        if not self.screen:
            return super().scan(s)
        k = self.key(s)
        r = self.cache.get(k)
        if r is not None:
            return r
        nax = self.M.Q + self.M.NP
        st1 = [(a, m) for a in range(nax) for m in (0, 1)]
        out = self._eval(s, st1)
        axes = []
        for t in out:
            if t[1] not in axes:
                axes.append(t[1])
            if len(axes) >= self.screen:
                break
        out += self._eval(s, [(a, m) for a in axes for m in range(2, 8)])
        out.sort(key=lambda t: -t[0])
        if len(self.cache) > 20000:
            self.cache.clear()
        self.cache[k] = out
        return out

    def _eval(self, s, axmd):
        ml, mr = self.E.splits(s, axmd, self.nthreads)
        self.stats['evals'] += 2 * len(axmd)
        out = [(min(x, y), a, m, x, y) for (a, m), x, y in zip(axmd, ml, mr) if x > -1e8]
        out.sort(key=lambda t: -t[0])
        return out

    def kids(self, s, a, md):
        return self.E.children(s, a, md)

    def build(self, s):
        self.t0 = time.time()
        if self.pen > 0:
            self.E.set_pen(self.shared, self.pen)
        self.node(s, None, 0)
        self.stats['secs'] = time.time() - self.t0
        return self.stats


def shared0(P):
    return {x for x in P if x % 256 == 0 and P[x]}


# ------------------------------------------------------------------ exact replay in C++ (cpp/replay.inc)
def _u128(v):
    v = int(v)
    assert 0 <= v < 1 << 128
    return [v & 0xFFFFFFFFFFFFFFFF, v >> 64]


def replay_setup(E, M, axb=None, wbits=None):
    L = E.lib
    L.eng_replay_setup.argtypes = [ctypes.c_void_p] + [ctypes.c_int] * 6 + [ctypes.c_void_p] * 4
    L.eng_replay.restype = ctypes.c_int64
    L.eng_replay.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int64, ctypes.c_int64, ctypes.c_void_p,
                             ctypes.c_int, ctypes.c_void_p]
    sig = np.array(_u128(M.SIG), dtype=np.uint64)
    cn = np.array(_u128(M.cN), dtype=np.uint64)
    bs = np.array(sum((_u128(b) for b in M.BS), []), dtype=np.uint64)
    ta = np.array(sum((_u128(t[2]) for t in M.TS), []), dtype=np.uint64)
    E._rp = (sig, cn, bs, ta)
    L.eng_replay_setup(E.h, M.FS, M.LB, M.QB, M.YFUEL, axis_bits(M) if axb is None else axb,
                       wbits or M.WMASK.bit_length(), sig.ctypes.data, cn.ctypes.data, bs.ctypes.data, ta.ctypes.data)


def replay(E, bits, nbits, pos, s, fuel=400):
    """Exact walk of a tree stream (Python int of nbits bits) from pos -> (end or 0, leaves, refl, failpos)."""
    nw = (nbits + 64 + 1023) // 64 + 16
    words = np.frombuffer(int(bits).to_bytes(8 * nw, 'little'), dtype=np.uint64).copy()
    st = E.flat(s)
    out = np.zeros(3, dtype=np.int64)
    end = E.lib.eng_replay(E.h, words.ctypes.data, len(words), pos, st.ctypes.data, fuel, out.ctypes.data)
    return int(end), int(out[0]), int(out[1]), int(out[2])
