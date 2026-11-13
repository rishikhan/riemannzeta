"""Shared state for the certificate generator: the replay model and checker, closure
splits, and the walk over an existing certificate's trees.

The generator reuses src/lbcert/replay.py as the exact reference: every quantity a
leaf or table relies on is computed with replay's Checker, so a generated certificate
is correct by construction exactly when replay accepts it.
"""
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
import replay  # noqa: E402

A031 = Path(os.environ.get('A031', ROOT / 'third_party' / 'attempt-031' / 'Solution.lean'))
SC = 32768
Q = 8


def load(path=A031):
    M = replay.load_model(str(path))
    return M, replay.Checker(M)


def axis_bounds(M, s, ax):
    """(i, j, lo, hi) of split axis ax in state s."""
    if ax < M.Q:
        return ax, ax + 1, s[0][ax], s[1][ax]
    i, j = M.PR[ax - M.Q]
    return i, j, s[2][ax - M.Q], s[3][ax - M.Q]


def cut_point(C, lo, hi, md):
    if md >= 2:
        return C.fracQ(lo, hi, md)
    if md == 1:
        return C.bcutL(64, lo, hi)
    return (lo + hi) >> 1


def children(C, s, ax, md):
    """The checker's two children of a split (splitAx), as (q, left, right)."""
    M = C.M
    i, j, lo, hi = axis_bounds(M, s, ax)
    q = cut_point(C, lo, hi, md)
    left = C.cuB(s, C.colB(s, i), C.rowB(s, M.BB + q, j))
    right = C.cuB(s, C.colB(s, j), C.rowB(s, replay.nsub(M.BB, q), i))
    return q, left, right


def root_state(C, idx):
    return C.matC(C.rootState(idx))


def collect(C, bits, pos, s, out, depth=0, cuts=None):
    """Walk one tree of an existing certificate; append (kind, pos, state, word, depth) for
    every leaf and return the end position (mirrors walkC without the leaf check)."""
    if cuts:
        for (cp, cst, ce) in cuts:
            if cp == pos:
                out.append(('cut', pos, s, cst, depth))
                return ce
    w = bits(pos)
    if w & 1:
        ax = (w >> 1) & 63
        md = (w >> 7) & 7
        q, left, right = children(C, s, ax, md)
        pp = collect(C, bits, pos + 10, left, out, depth + 1, cuts)
        if pp == 0:
            return 0
        return collect(C, bits, pp, right, out, depth + 1, cuts)
    L, U = s[0], s[1]
    if U[7] < L[0]:
        out.append(('refl', pos, s, None, depth))
        return pos + 1
    variance = ((w >> 1) & 1) == 1
    n, _ = C.mleaf(w >> 2, s, variance)
    out.append(('leaf', pos, s, (w >> 2, variance, n), depth))
    return pos + 2 + n if n else 0
