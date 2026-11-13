#!/usr/bin/env python3
"""Final tangent-point table from xgen usage files: hull intervals and per-point piece count n.

    python ptable.py MODEL.pkl PTS.pkl OUT_PREFIX USAGE [USAGE ...]

USAGE rows (xgen check --usage): x count minEL maxEU.  For every used point x the word of PTS.pkl keeps
its value / slope fields, and its interval is cut to the usage hull [minEL, maxEU] (q9ptt/selwords.py);
n is the cheapest piece count in NS (counted in pyramid lookups, lb + lbDr) for which the exact
tcheckPZC check ivOk(n, 4, x, word) passes.  A point whose hull fails for every n keeps its maximal
interval.  Every word is checked with pt3e and ivOk.
Writes OUT_PREFIX.lean.txt (x stored_word n, the q9 hull_final.txt format) and OUT_PREFIX.xgen.txt
(x V P M A B, the table format of xgen check --table).
"""
import os
import pickle
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
for d in ('q9hs', 'q9', 'gen', ''):
    sys.path.insert(0, os.path.join(LB, d))
import hs                                     # noqa: E402

NS = (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64)


def main():
    model, pts, outp = sys.argv[1:4]
    M = pickle.load(open(model, 'rb'))
    P = pickle.load(open(pts, 'rb'))
    C = hs.HSChecker(M)
    cnt = Counter()
    lb0, lbd0 = C.lb, C.lbDr

    def lb(lo, hi):
        cnt['n'] += 1
        return lb0(lo, hi)

    def lbDr(lo, hi):
        cnt['n'] += 1
        return lbd0(lo, hi)
    C.lb, C.lbDr = lb, lbDr
    use = {}
    for f in sys.argv[4:]:
        for ln in open(f):
            x, c, a, b = map(int, ln.split())
            c0, a0, b0 = use.get(x, (0, a, b))
            use[x] = (c0 + c, min(a0, a), max(b0, b))
    tab = {}
    kept = 0
    look = 0
    for x in sorted(use):
        v = C.pwD(x, P[x])
        X = C.trip(v)
        A, B = C.ivA(v), C.ivB(v)
        _, Lm, Um = use[x]
        assert A <= Lm <= x <= Um <= B, (x, A, Lm, Um, B)
        best = None
        for lo, hi in ((Lm, Um), (A, B)):
            w2 = X | ((x - lo) << 96) | ((hi - x) << 116)
            for n in NS:
                cnt['n'] = 0
                if C.ivOk(n, 4, x, C.pwD(x, w2)):
                    if best is None or cnt['n'] < best[0]:
                        best = (cnt['n'], n, w2)
            if best is not None:
                break
            kept += 1
        assert best is not None, x
        look += best[0]
        assert C.pt3e(x, C.trip(C.pwD(x, best[2]))), x
        tab[x] = (best[2], best[1])
    with open(outp + '.lean.txt', 'w') as f:
        for x in sorted(tab):
            f.write('%d %d %d\n' % (x, tab[x][0], tab[x][1]))
    with open(outp + '.xgen.txt', 'w') as f:
        for x in sorted(tab):
            v = C.pwD(x, tab[x][0])
            f.write('%d %d %d %d %d %d\n' % (x, v & 0xFFFFFFFF, (v >> 32) & 0xFFFFFFFF, (v >> 64) & 0xFFFFFFFF,
                                             C.ivA(v), C.ivB(v)))
    print('points %d, kept maximal interval %d, ivOk lookups %.2f per point, uses %d'
          % (len(tab), kept, look / max(1, len(tab)), sum(u[0] for u in use.values())))


if __name__ == '__main__':
    main()
