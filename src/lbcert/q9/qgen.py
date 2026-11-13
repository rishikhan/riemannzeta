"""Q-gap generalisation of the generator in ../gen (read-only imports).

* QChecker: replay.Checker with the two places that assume 8 gaps / 28 pairs made generic:
  the reflection leaf test reads U_{Q-1}, and the multiplier record's pair index has
  PB = NP.bit_length() bits (5 for NP = 28, 6 for NP = 36), so an entry is 1 + PB + 1 + QB bits
  and any index c >= NP terminates the list.  For Q = 8 both are the attempt-031 semantics.
* layout(): PR, SL, TS, ADJ for Q gaps in attempt-031's order (lexicographic pairs, adjacent
  terms carry k = 0, zero-weight pairs have no TS entry).
* int_weights(): gen/build_model.int_weights for Q gaps and an arbitrary zero-pair set.
* dump()/Engine: cengine.py with Q and NP written first (cpp/engine.cpp reads them).
* LeafSolverQ: leaf.LeafSolver with the generic multiplier record and MAXBITS = WMASK bits - 2.
"""
import ctypes
import os
import struct
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, '..', 'gen')
sys.path.insert(0, GEN)
from core import replay                      # noqa: E402
import cengine as CE8                        # noqa: E402
from leaf import LeafSolver                  # noqa: E402

nsub = replay.nsub
SA = 8388608000000000000000000000000
LIB = os.path.join(HERE, 'cpp', 'libengine.dylib' if sys.platform == 'darwin' else 'libengine.so')


def pair_bits(NP):
    return NP.bit_length()


class QChecker(replay.Checker):
    def ydec(self, s, qb, w, fuel, o):
        L, U, A, B = s
        Q, NP = self.M.Q, self.M.NP
        PB = pair_bits(NP)
        P = [0] * Q; S = [0] * Q; Cp = 0; Cm = 0
        n = 0
        for _ in range(fuel):
            if ((w >> o) & 1) != 1:
                o = o + 1
                break
            c = (w >> (o + 1)) & ((1 << PB) - 1)
            o1 = o + 1 + PB
            if not c < NP:
                o = o1 + qb + 1
                break
            Y = self.M.SIG * ((w >> (o1 + 1)) & nsub(1 << qb, 1))
            sd = (w >> o1) & 1
            Ylo = 0 if sd == 1 else Y
            Yhi = Y if sd == 1 else 0
            i, j = self.PR_(c)
            sL = sum(L[i:j])
            for r in range(i, j):
                P[r] += Ylo; S[r] += Yhi
            Cp += Ylo * nsub(sL, A[c]) + Yhi * nsub(B[c], sL)
            Cm += Ylo * nsub(A[c], sL) + Yhi * nsub(sL, B[c])
            o = o1 + qb + 1
            n += 1
        return o, P, S, Cp, Cm, n

    def leafStep(self, pos, w, s, rec, depth):
        # replay.Checker.leafStep with U_{Q-1} in the reflection test.  It must not call the
        # parent: the parent tests U[7] < L[0] first, which for Q = 9 turns real leaves into
        # 1-bit reflection leaves and desynchronises the walk.
        L, U = s[0], s[1]
        if U[self.M.Q - 1] < L[0]:
            if rec is not None:
                rec['refl'] += 1
                rec['depths'].append(depth)
            return pos + 1
        variance = ((w >> 1) & 1) == 1
        n, det = self.mleaf(w >> 2, s, variance, want_detail=rec is not None)
        if rec is not None:
            rec['leaves'] += 1
            rec['depths'].append(depth)
            rec['var'] += 1 if variance else 0
            rec['margins'].append((det['rhs'] - det['lhs'], pos, variance, det['nmul'],
                                   [t[0] for t in det['terms']], tuple(s[0]), tuple(s[1])))
        if n == 0:
            if rec is not None:
                rec['fail'].append((pos, det['info'], det['lhs'], det['rhs']))
            return 0
        return pos + 2 + n


def layout(Q, AW):
    """AW: {(i, j): integer weight} for all 0 <= i < j <= Q -> PR, SL, TS, ADJ."""
    PR = [(i, j) for i in range(Q + 1) for j in range(i + 2, Q + 1)]
    kidx = {p: k for k, p in enumerate(PR)}
    TS, ADJ = [], []
    for i in range(Q + 1):
        for j in range(i + 1, Q + 1):
            if j == i + 1:
                ADJ.append(len(TS))
                TS.append((i, j, AW[(i, j)], 0))
            elif AW[(i, j)]:
                TS.append((i, j, AW[(i, j)], kidx[(i, j)]))
    SL = [0] * (Q + 1) ** 2
    for a in range(Q + 1):
        for b in range(a + 1, Q + 1):
            SL[a * (Q + 1) + b] = a if b == a + 1 else Q + kidx[(a, b)]
    return PR, SL, TS, ADJ


def int_weights(Q, b, A, b0min, zero=()):
    """Integer weights x SA: palindromic, zero pairs 0, span sums exactly 2 SA, b_0 = b_{Q-1} >= b0min.
    b: Q floats; A: {(i, j): float} over all pairs."""
    pairs = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
    mir = lambda p: (Q - p[1], Q - p[0])
    zero = set(zero) | {mir(p) for p in zero}
    AW = {}
    for p in pairs:
        AW[p] = 0 if p in zero else int(round((A[p] + A[mir(p)]) / 2 * SA))
    for s in range(1, Q + 1):
        ps = [(i, i + s) for i in range(Q + 1 - s)]
        diff = 2 * SA - sum(AW[p] for p in ps)
        mid = [p for p in ps if p == mir(p)]
        if mid and diff:
            AW[mid[0]] += diff
        elif diff:
            assert diff % 2 == 0, (s, diff)
            p = max((p for p in ps if p not in zero and p[0] < mir(p)[0]), key=lambda p: AW[p])
            AW[p] += diff // 2
            AW[mir(p)] += diff // 2
        assert sum(AW[p] for p in ps) == 2 * SA and all(AW[p] >= 0 for p in ps)
    for p in pairs:
        assert AW[p] == AW[mir(p)]
    BS = [int(round((b[r] + b[Q - 1 - r]) / 2 * SA)) for r in range(Q)]
    BS[0] = BS[Q - 1] = max(BS[0], b0min)
    return BS, AW


# ------------------------------------------------------------------ C++ engine
def dump(M, C, pts, path):
    """cengine.dump with Q and NP in front (cpp/engine.cpp eng_load)."""
    tmp = path + '.body'
    CE8.dump(M, C, pts, tmp)
    body = open(tmp, 'rb').read()
    os.remove(tmp)
    open(path, 'wb').write(struct.pack('<qq', M.Q, M.NP) + body)


class Engine(CE8.Engine):
    def __init__(self, path, Q, NP):
        lib = ctypes.CDLL(LIB)
        lib.eng_load.restype = ctypes.c_void_p
        lib.eng_load.argtypes = [ctypes.c_char_p]
        lib.eng_margin.restype = ctypes.c_double
        lib.eng_margin.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        lib.eng_margin_raw.restype = ctypes.c_double
        lib.eng_margin_raw.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        lib.eng_splits.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p,
                                   ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]
        lib.eng_children.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_int,
                                     ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        lib.eng_set_pen.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_double]
        self.lib = lib
        self.Q, self.NP = Q, NP
        self.h = lib.eng_load(path.encode())
        assert self.h, path

    def unflat(self, a):
        a = [int(x) for x in a]
        Q, NP = self.Q, self.NP
        return (a[:Q], a[Q:2 * Q], a[2 * Q:2 * Q + NP], a[2 * Q + NP:])

    def children(self, s, ax, md):
        st = self.flat(s)
        NS = 2 * self.Q + 2 * self.NP
        l = np.zeros(NS, dtype=np.int64); r = np.zeros(NS, dtype=np.int64); q = np.zeros(1, dtype=np.int64)
        self.lib.eng_children(self.h, st.ctypes.data, ax, md, l.ctypes.data, r.ctypes.data, q.ctypes.data)
        return int(q[0]), self.unflat(l), self.unflat(r)


# ------------------------------------------------------------------ leaves
class LeafSolverQ(LeafSolver):
    def __init__(self, C, pt, **kw):
        super().__init__(C, pt, **kw)
        self.PB = pair_bits(self.M.NP)
        self.MAXBITS = self.M.WMASK.bit_length() - 2

    def encode_mult(self, q):
        PB, QB = self.PB, self.M.QB
        bits = 0
        o = 0
        for (cidx, sd, qi) in q[:self.M.YFUEL - 1]:
            rec = 1 | (cidx << 1) | (sd << (1 + PB)) | (qi << (2 + PB))
            bits |= rec << o
            o += 2 + PB + QB
        o += 1
        return bits, o
