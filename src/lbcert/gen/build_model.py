#!/usr/bin/env python3
"""Patched replay model for a new window and weights: window literals of the cell
evaluator, integer weights over SA, regenerated tables, root cover and floor target.

    python build_model.py WINDOW.json OUTDIR [--c-target C] [--workers 8]

Writes OUTDIR/model.pkl, OUTDIR/pts.pkl and OUTDIR/spec.json (weights, cN, cover).
"""
import argparse
import json
import os
import pickle
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import load, replay          # noqa: E402
import tables as T                     # noqa: E402

SA = 8388608000000000000000000000000
PAIRS = [(i, j) for i in range(9) for j in range(i + 1, 9)]


def window_tables(c):
    """CE, CJ, FAR of AMW.G for numerators c[0..12] over 1e9 (c[0] = 1e9)."""
    CE = []
    for j in range(1, 13):
        flag = (-((-1) ** j) * c[j]) > 0
        CE.append((j, abs(c[j]), flag))
    CJ = {j: (abs(c[j]), c[j] < 0) for j in range(1, 13)}
    return CE, CJ


def int_weights(b, pairs, b0min):
    """Integer weights x * SA: palindromic, a_02 = a_68 = 0, span sums exactly 2 SA,
    b_0 = b_7 >= b0min."""
    A = {}
    for (i, j, v) in pairs:
        A[(i, j)] = v
    AW = {}
    for (i, j) in PAIRS:
        ii, jj = 8 - j, 8 - i
        v = (A[(i, j)] + A[(ii, jj)]) / 2
        AW[(i, j)] = int(round(v * SA))
    AW[(0, 2)] = AW[(6, 8)] = 0
    for (i, j) in PAIRS:
        assert AW[(i, j)] == AW[(8 - j, 8 - i)]
    for s in range(1, 9):
        ps = [(i, i + s) for i in range(9 - s)]
        tot = sum(AW[p] for p in ps)
        diff = 2 * SA - tot
        # adjust the self-symmetric pair if any, else the largest symmetric couple
        mid = [p for p in ps if p == (8 - p[1], 8 - p[0])]
        if mid and diff:
            AW[mid[0]] += diff
        elif diff:
            assert diff % 2 == 0, (s, diff)
            p = max((p for p in ps if p not in [(0, 2), (6, 8)] and p[0] < 8 - p[1]), key=lambda p: AW[p])
            AW[p] += diff // 2
            AW[(8 - p[1], 8 - p[0])] += diff // 2
        assert sum(AW[p] for p in ps) == 2 * SA and all(AW[p] >= 0 for p in ps)
    BS = [int(round((b[r] + b[7 - r]) / 2 * SA)) for r in range(8)]
    BS[0] = BS[7] = max(BS[0], b0min)
    return BS, AW


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('window')
    ap.add_argument('outdir')
    ap.add_argument('--c-target', type=float, default=None)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--kb', type=int, default=1048576)
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    W = json.load(open(a.window))
    c = W['window']['numerators']
    assert len(c) == 13 and c[0] == 10 ** 9 and W['window']['denominator'] == 10 ** 9
    eps = W['float']['eps']
    ct = a.c_target if a.c_target is not None else eps
    cN = int(Fraction(ct) * SA)
    smax_end = a.kb - 1
    b0min = -(-cN * 32768 // smax_end)
    BS, AW = int_weights(W['position_pressure']['float'], W['pair_weights']['float'], b0min)

    M, C = load()
    M.cAMn = {j: c[j] for j in range(13)}
    CE, CJ = window_tables(c)
    M.G['CE'] = [list(t) for t in CE]
    M.G['FAR'] = list(CE)
    M.G['CJ'] = CJ
    M.KB = a.kb
    M.cN = cN
    M.BS = BS
    M.TS = [(i, j, AW[(i, j)], k) for (i, j, _, k) in M.TS]
    M.TBL = []
    C = replay.Checker(M)
    # pyramids
    blocks = {j: 8 for j in range(16, 512)}
    M.TOP, BK = T.build_pyramid(C, blocks)
    M.BKv = {j: BK.get(j, 0) for j in range(512)}
    M.TOPD, BKD = T.build_pyramid(C, blocks, deriv=True)
    M.BKDv = {j: BKD.get(j, 0) for j in range(512)}
    C = replay.Checker(M)
    M.REG = T.build_regions(C)
    C = replay.Checker(M)
    # root cover: bad segments cut as in attempt-031
    cuts = {1: [39936, 51168], 2: [45568], 3: [44544], 4: [44544], 5: [45568], 6: [39936, 51168]}
    COV, SMAX = [], []
    for r in range(8):
        aadj = M.TS[M.ADJ[r]][2]
        sm = min(smax_end, -(-cN * 32768 // BS[r]))
        if r in (0, 7):
            sm = smax_end
        COV.append(T.build_cover(C, cN, aadj, sm, splits=cuts.get(r, ())))
        SMAX.append(sm)
    M.COV, M.SMAX = COV, SMAX
    ok = all(C.coverChk(cN, M.TS[M.ADJ[r]][2], 16384, SMAX[r], COV[r]) for r in range(8))
    hS = all(cN * 32768 <= BS[r] * SMAX[r] for r in range(8))
    hwin = all(cN * 4 <= M.TS[M.ADJ[r]][2] for r in range(8))
    print('cover ok', ok, 'hS', hS, 'hwin', hwin, 'win', all(C.winOk(i) for i in range(16)))
    print('pv', replay.pv_check(M))
    for r in range(8):
        print(r, [s for s in COV[r] if not s[2]], 'good segs', sum(1 for s in COV[r] if s[2]))
    pickle.dump(M, open(os.path.join(a.outdir, 'model.pkl'), 'wb'))
    pts = T.precompute_points(M, C, grid=8, workers=a.workers)
    pickle.dump(pts, open(os.path.join(a.outdir, 'pts.pkl'), 'wb'))
    spec = dict(window=c, cN=cN, BS=BS, AW={'%d,%d' % k: v for k, v in AW.items()}, COV=COV, SMAX=SMAX,
                eps=eps, H=W['float']['H'], kb=a.kb)
    json.dump(spec, open(os.path.join(a.outdir, 'spec.json'), 'w'), indent=1)
    print('points', len(pts), 'cN', cN, 'c', cN / SA, 'B', sum(BS) / SA)


if __name__ == '__main__':
    main()
