#!/usr/bin/env python3
"""Extend a q12x model's kernel tables from x < 2^19 (16 SC) to x < 2^20 (32 SC).

    python extend_model.py SRC_WORK OUT_WORK [--workers 20] [--plv 21] [--nreg 32] [--no-pts]

The Lean checker's pyramid has 20 levels (lb(lo, hi) = 0 once hi > 2^19) and 16 convexity regions
(tangent points only below about 15.5 SC), so every pair at distance >= 16 SC counts 0 in a leaf.  This
script copies SRC_WORK's model and raises the pyramid to PLV levels (domain 2^(PLV-1)) and the region
count to NREG (replay.Checker, gen/tables.py and cpp/engine.cpp read M.PLV / M.NREG, default 20 / 16).
Blocks, regions and tangent points below the old domain are kept as they are; only the new ones are
computed (blocks j = 512 .. 2^(PLV-11) - 1 at finest level 8 as build9 does, regions k = 16 .. NREG - 1,
tangent points of those regions on build9's grid of 8).  Writes OUT_WORK/{model.pkl, pts.pkl,
model.pkl.eng, exact.txt, root_*.box, spec.json}.

This is a generator-side prototype: the Lean checker would need the same change (FORMAT.md, PROGRESS.md).
"""
import argparse
import os
import pickle
import shutil
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
for d in ('', 'gen', 'q9', 'q9hs'):
    sys.path.insert(0, os.path.join(LB, d))
import qgen                                   # noqa: E402
import tables as T                            # noqa: E402


def top_of(BK, PLV, fw, mn):
    """TOP word from the block roots (gen/tables.py build_pyramid's loop, PLV levels)."""
    mask = (1 << fw) - 1
    cur = [(BK.get(j, 0) >> 5) & mask for j in range(1 << (PLV - 11))]
    TOP = 0
    for l in range(11, PLV):
        nxt = [mn(cur[2 * i], cur[2 * i + 1]) for i in range(len(cur) // 2)]
        for i, v in enumerate(nxt):
            TOP |= v << (fw * ((1 << (PLV - 1 - l)) + i))
        cur = nxt
    return TOP


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src')
    ap.add_argument('out')
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--plv', type=int, default=21)
    ap.add_argument('--nreg', type=int, default=32)
    ap.add_argument('--no-pts', action='store_true')
    ap.add_argument('--fine', default='', help='value-pyramid blocks rebuilt with a finer finest level, '
                    '"j0-j1:r,..." (block j covers x in [1024 j, 1024 j + 1024); build9 uses r = 8, 256-unit cells)')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    M = pickle.load(open(os.path.join(a.src, 'model.pkl'), 'rb'))
    P = pickle.load(open(os.path.join(a.src, 'pts.pkl'), 'rb'))
    PLV0, NREG0 = getattr(M, 'PLV', 20), getattr(M, 'NREG', 16)
    assert a.plv >= PLV0 and a.nreg >= NREG0
    M.PLV, M.NREG = a.plv, a.nreg
    C = qgen.QChecker(M)
    t0 = time.time()
    nb0, nb = 1 << (PLV0 - 11), 1 << (a.plv - 11)   # blocks of 2^10 units: level 10 has 2^(PLV-11) entries
    for deriv in (False, True):
        fw, mn = (64, T.pmin) if deriv else (32, min)
        leaf = T.dmax_cell if deriv else T.vmax_cell
        BK = dict(M.BKDv if deriv else M.BKv)
        # the TOP loop reproduces the source model's word at its own level count
        assert top_of(BK, PLV0, fw, mn) == (M.TOPD if deriv else M.TOP)
        for j in range(nb0, nb):
            BK[j] = T.build_block(C, j, 8, leaf, fw, mn)
        if not deriv:
            for spec in filter(None, a.fine.split(',')):
                rng, r = spec.split(':')
                j0, j1 = map(int, rng.split('-'))
                for j in range(j0, j1 + 1):
                    BK[j] = T.build_block(C, j, int(r), leaf, fw, mn)
        if deriv:
            M.BKDv, M.TOPD = BK, top_of(BK, a.plv, fw, mn)
        else:
            M.BKv, M.TOP = BK, top_of(BK, a.plv, fw, mn)
    M.n_BK_blocks = sum(1 for v in M.BKv.values() if v)
    M.n_BKD_blocks = sum(1 for v in M.BKDv.values() if v)
    print('pyramids: %d blocks (%d nonzero), %.0f s' % (nb, M.n_BK_blocks, time.time() - t0), flush=True)
    C = qgen.QChecker(M)
    t0 = time.time()
    A1, B1, ch1 = T.build_regions(C, kmin=NREG0)
    m20 = (1 << 20) - 1
    A0, B0, ch0 = M.REG
    Ap = sum(((A0 if k < NREG0 else A1) >> (20 * k) & m20) << (20 * k) for k in range(a.nreg))
    Bp = sum(((B0 if k < NREG0 else B1) >> (20 * k) & m20) << (20 * k) for k in range(a.nreg))
    M.REG = (Ap, Bp, list(ch0) + list(ch1[NREG0:]))
    C = qgen.QChecker(M)
    assert C.rgOk()
    for k in range(a.nreg):
        print('  region %2d [%d, %d]' % (k, C.rgA(k), C.rgB(k)))
    print('regions: %.0f s' % (time.time() - t0), flush=True)
    if not a.no_pts:
        t0 = time.time()
        Pn = T.precompute_points(M, C, grid=8, workers=a.workers, tmp=os.path.join(os.path.abspath(a.out), 'mc.pkl'),
                                 kmin=NREG0)
        P = dict(P)
        P.update(Pn)
        print('points: %d new (%d nonzero), %.0f s' % (len(Pn), sum(1 for v in Pn.values() if v), time.time() - t0),
              flush=True)
    C = qgen.QChecker(M)
    # table integrity as the checker states it (replay: top_ok, blk, topD_ok, dblk, hR), new blocks and points
    assert C.topOk(M.TOP, C.BK) and C.topOk2(M.TOPD, C.BKD) and C.rgOk()
    assert all(C.blockOk(C.BK(j), j) and C.blockOk2(C.BKD(j), j) for j in range(nb0, nb))
    for spec in filter(None, a.fine.split(',')):
        j0, j1 = map(int, spec.split(':')[0].split('-'))
        assert all(C.blockOk(C.BK(j), j) for j in range(j0, j1 + 1))
    if not a.no_pts:
        bad = [x for x, w in Pn.items() if w and not (C.pt3e(x, C.trip(C.pwD(x, w))) and C.ivOk(32, 4, x, C.pwD(x, w)))]
        assert not bad, bad[:5]
    print('checks: top_ok, topD_ok, hR, new blocks, new points pass', flush=True)
    pickle.dump(M, open(os.path.join(a.out, 'model.pkl'), 'wb'))
    pickle.dump(P, open(os.path.join(a.out, 'pts.pkl'), 'wb'))
    qgen.dump(M, C, P, os.path.join(a.out, 'model.pkl.eng'))
    for f in os.listdir(a.src):
        if f in ('exact.txt', 'spec.json') or (f.startswith('root_') and f.endswith('.box')):
            shutil.copy(os.path.join(a.src, f), os.path.join(a.out, f))
    print('wrote', a.out)


if __name__ == '__main__':
    main()
