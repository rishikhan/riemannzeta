#!/usr/bin/env python3
"""Q-gap certificate model for a sep_window_search result (best_q9_j16.json format).

    python build9.py WINDOW.json OUTDIR [--c-offset 6e-7] [--zero-pairs 0-2] [--wmask-bits 1024]
                     [--workers 20] [--no-pts]

The window is c = [1, xfree...] rounded to numerators over 1e9 (J = len(xfree) corrections:
CE, CJ, FAR and the nearOn bound 2J of the cell evaluator).  Weights x = (b_0..b_{Q-1}, a_ij over
all pairs in lexicographic order) are quantised with qgen.int_weights; zero pairs (and their
mirrors) are forced to 0 and get no TS slot.  The floor target is c = eps - c_offset, as gen does.
Tables (pyramids, regions, tangent points) are rebuilt for the window; the root cover is
rootcov/cover.py's maximal cover with attempt-031's band cut on gaps 1 and Q-2 (v2max layout).

Writes OUTDIR/model.pkl, OUTDIR/pts.pkl, OUTDIR/spec.json.
"""
import argparse
import json
import math
import os
import pickle
import sys
from fractions import Fraction as Fr
from math import prod

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'q9'))
sys.path.insert(0, os.path.join(HERE, '..', 'rootcov'))
import qgen                                   # noqa: E402
from qgen import replay, SA                   # noqa: E402
import tables as T                            # noqa: E402
import window_patch as WP                     # noqa: E402
import cover as CV                            # noqa: E402

BASE = os.path.join(HERE, '..', 'gen', 'work', 'v2', 'model.pkl')
G1 = [39936, 51168]


def int_weights(Q, b, A, b0min, zero=()):
    """qgen.int_weights, except that a zero self-mirror pair never takes the span's rounding
    remainder (qgen gives it to the middle pair even when that pair is zero)."""
    pairs = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
    mir = lambda p: (Q - p[1], Q - p[0])
    zero = set(zero) | {mir(p) for p in zero}
    AW = {p: 0 if p in zero else int(round((A[p] + A[mir(p)]) / 2 * SA)) for p in pairs}
    for s in range(1, Q + 1):
        ps = [(i, i + s) for i in range(Q + 1 - s)]
        diff = 2 * SA - sum(AW[p] for p in ps)
        mid = [p for p in ps if p == mir(p) and p not in zero]
        if mid and diff:
            AW[mid[0]] += diff
        elif diff:
            if diff % 2:
                raise ValueError('odd remainder on span %d with a zero middle pair' % s)
            p = max((p for p in ps if p not in zero and p[0] < mir(p)[0]), key=lambda p: AW[p])
            AW[p] += diff // 2
            AW[mir(p)] += diff // 2
        assert sum(AW[p] for p in ps) == 2 * SA and all(AW[p] >= 0 for p in ps)
    BS = [int(round((b[r] + b[Q - 1 - r]) / 2 * SA)) for r in range(Q)]
    BS[0] = BS[Q - 1] = max(BS[0], b0min)
    return BS, AW


def hw_floor(c):
    """window_patch.hw_floor for J = len(c) - 1 corrections."""
    J = len(c) - 1
    pam = sum(Fr(c[n + 1], 10 ** 9) ** 2 * (Fr(1, 2) - 1 / (4 * WP.PIU ** 2 * (n + 1) ** 2)) for n in range(J))
    e = Fr(3, 2) - WP.COSU / (2 * WP.R2 * WP.SINL) - pam / (2 * WP.SINL ** 2)
    return math.floor(e * 10 ** 40)


def window_tables(c):
    J = len(c) - 1
    CE = [(j, abs(c[j]), (-((-1) ** j) * c[j]) > 0) for j in range(1, J + 1)]
    CJ = {j: (abs(c[j]), c[j] < 0) for j in range(1, J + 1)}
    return CE, CJ


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('window')
    ap.add_argument('outdir')
    ap.add_argument('--c-offset', type=float, default=6e-7)
    ap.add_argument('--zero-pairs', default='')
    ap.add_argument('--wmask-bits', type=int, default=1024)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--no-pts', action='store_true')
    ap.add_argument('--kb', type=int, default=1048576)
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    W = json.load(open(a.window))
    c = [10 ** 9] + [int(round(v * 1e9)) for v in W['xfree']]
    J = len(c) - 1
    x = W['x']
    Q = next(q for q in range(2, 20) if q + q * (q + 1) // 2 == len(x))
    pairs = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
    A = {p: x[Q + k] for k, p in enumerate(pairs)}
    zero = {tuple(int(t) for t in s.split('-')) for s in a.zero_pairs.split(',') if s}
    eps = W['eps']
    cN = int(Fr(eps - a.c_offset) * SA)
    smax_end = a.kb - 1
    b0min = -(-cN * 32768 // smax_end)
    BS, AW = int_weights(Q, x[:Q], A, b0min, zero)

    M = pickle.load(open(BASE, 'rb'))
    M.Q = Q
    M.PR, M.SL, M.TS, M.ADJ = qgen.layout(Q, AW)
    M.NP = len(M.PR)
    M.cAMn = {j: c[j] for j in range(J + 1)}
    CE, CJ = window_tables(c)
    M.G['CE'] = [list(t) for t in CE]
    M.G['FAR'] = list(CE)
    M.G['CJ'] = CJ
    M.G['nearK'] = 2 * J
    M.KB = a.kb
    M.cN = cN
    M.BS = BS
    M.TBL = []
    M.WMASK = (1 << a.wmask_bits) - 1
    C = qgen.QChecker(M)
    blocks = {j: 8 for j in range(16, 512)}
    M.TOP, BK = T.build_pyramid(C, blocks)
    M.BKv = {j: BK.get(j, 0) for j in range(512)}
    M.TOPD, BKD = T.build_pyramid(C, blocks, deriv=True)
    M.BKDv = {j: BKD.get(j, 0) for j in range(512)}
    C = qgen.QChecker(M)
    M.REG = T.build_regions(C)
    C = qgen.QChecker(M)
    SMAX = []
    for r in range(Q):
        sm = min(smax_end, -(-cN * 32768 // BS[r]))
        if r in (0, Q - 1):
            sm = smax_end
        SMAX.append(sm)
    M.SMAX = SMAX
    COV = []
    for r in range(Q):
        aadj = M.TS[M.ADJ[r]][2]
        COV.append(CV.build_cover(C, cN, aadj, SMAX[r], interior=True,
                                  splits=G1 if r in (1, Q - 2) else ()))
    M.COV = COV
    ok = CV.check(C, M, COV, SMAX)
    hwin = all(cN * 4 <= M.TS[M.ADJ[r]][2] for r in range(Q))
    win = all(C.winOk(i) for i in range(16))
    try:
        pv = replay.pv_check(M)
    except Exception as e:      # the Lean check is written for 12 corrections
        pv = 'error %r' % (e,)
    nb = [len(CV.bad_of(cv)) for cv in COV]
    hw = hw_floor(c)
    B = sum(BS)
    kappa = (Fr(hw, 10 ** 40) - Fr(B, SA)) / (1 - Fr(cN, SA))
    print('Q', Q, 'J', J, 'NP', M.NP, 'terms', len(M.TS), 'cover+hS', ok, 'hwin', hwin, 'winOk', win, 'pv', pv)
    print('bad segments', nb, 'roots', prod(nb))
    for r in range(Q):
        print(' gap', r, 'SMAX', SMAX[r], 'bad', CV.bad_of(COV[r]), 'good', sum(1 for s in COV[r] if s[2]))
    print('cN', cN, 'c', cN / SA, 'B', B / SA, 'hw', hw, 'kappa', float(kappa))
    pickle.dump(M, open(os.path.join(a.outdir, 'model.pkl'), 'wb'))
    spec = dict(window=c, Q=Q, J=J, cN=cN, BS=BS, AW={'%d,%d' % k: v for k, v in AW.items()}, COV=COV,
                SMAX=SMAX, nbad=nb, roots=prod(nb), eps=eps, H_float=W['H'], hw=hw, B=B,
                kappa=[kappa.numerator, kappa.denominator], kappa_float=float(kappa), zero_pairs=sorted(zero),
                c_offset=a.c_offset, kb=a.kb, wmask_bits=a.wmask_bits, pv=str(pv), winOk=win, hwin=hwin)
    json.dump(spec, open(os.path.join(a.outdir, 'spec.json'), 'w'), indent=1)
    if not a.no_pts:
        pts = T.precompute_points(M, C, grid=8, workers=a.workers,
                                  tmp=os.path.join(os.path.abspath(a.outdir), 'mc.pkl'))
        pickle.dump(pts, open(os.path.join(a.outdir, 'pts.pkl'), 'wb'))
        print('points', len(pts), 'nonzero', sum(1 for v in pts.values() if v))


if __name__ == '__main__':
    main()
