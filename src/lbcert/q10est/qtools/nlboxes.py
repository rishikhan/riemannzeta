#!/usr/bin/env python3
"""Boxes around the near-lattice minima of the table F, for xgen tree.

    python nlboxes.py TMIN.json OUTDIR [--top 20] [--widths 64,512] [--gfile G.txt]

For each of the best `top` local minima g (gaps in SC units) and each half-width w (units of 1/32768):
gaps round(g * 32768) +- w, pair-sum bounds A, B = sums of L, U over the pair's gaps (pairs of span >= 2 in
lexicographic order), reversed first when g_11 < g_0 (the half rule).  Writes OUTDIR/nl_<i>_w<w>.box and,
with --gfile, the minima as gap vectors (one per line) for wdiag.
"""
import argparse
import json
import os

Q, SC = int(os.environ.get("FQ", 12)), 32768
PR = [(i, j) for i in range(Q + 1) for j in range(i + 2, Q + 1)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tmin')
    ap.add_argument('out')
    ap.add_argument('--top', type=int, default=20)
    ap.add_argument('--widths', default='64,512')
    ap.add_argument('--gfile')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    mins = json.load(open(a.tmin))['minima'][:a.top]
    if a.gfile:
        with open(a.gfile, 'w') as f:
            for _, g in mins:
                f.write(' '.join('%.9f' % v for v in g) + '\n')
    for i, (fv, g) in enumerate(mins):
        gi = [round(v * SC) for v in g]
        if gi[-1] < gi[0]:
            gi = gi[::-1]
        for w in map(int, a.widths.split(',')):
            L = [x - w for x in gi]
            U = [x + w for x in gi]
            A = [sum(L[i0:j0]) for i0, j0 in PR]
            B = [sum(U[i0:j0]) for i0, j0 in PR]
            with open(os.path.join(a.out, 'nl_%d_w%d.box' % (i, w)), 'w') as f:
                f.write(' '.join(map(str, L + U + A + B)) + '\n')


if __name__ == '__main__':
    main()
