#!/usr/bin/env python3
"""Per-term cell-lb loss at given points, from wdiag's term lines.

    python cellloss.py SPEC.json WDIAG.out [--thr 1e-8]

For each row (one gap vector) and term n with pair distance E (units of 1/32768): loss_n = ta_n (W(E) -
lb(E, E + 1)), the cost of a term range one unit wide with no tangent point inside, where only the
value pyramid's cell lb is left.  Prints per row the margins line, the total loss, the largest terms,
and per value-pyramid block (j = E // 1024) the summed loss over all rows; blocks whose largest single
loss exceeds --thr, each widened by --pad blocks, are listed as extend_model.py's --fine set
(written to --fine-out if given).
"""
import argparse
import json
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __import__('os').path.dirname(__file__))
from fmin12 import window, Fn, PAIRS, Q, SC          # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('wdiag')
    ap.add_argument('--thr', type=float, default=1e-8)
    ap.add_argument('--quiet', action='store_true')
    ap.add_argument('--fine-out')
    ap.add_argument('--pad', type=int, default=0, help='widen each candidate block run by this many blocks')
    ap.add_argument('--maxspan', type=int, default=99, help='only terms with j - i <= maxspan')
    a = ap.parse_args()
    spec = json.load(open(a.spec))
    c, om = window(spec)
    F = Fn(c, om, np.zeros(Q), np.zeros(len(PAIRS)), 0.0)
    W = lambda E: float((F.k(np.array([E / SC]))[0][0] / F.k0) ** 2)
    blk_sum, blk_max = defaultdict(float), defaultdict(float)
    rows, cur = [], None
    for ln in open(a.wdiag):
        v = ln.split()
        if v[0] == 'row':
            cur = dict(head=ln.strip(), terms=[])
            rows.append(cur)
        elif v[0] == 't':
            n, i, j, E = map(int, v[1:5])
            ta, lb1, lb4, dp = float(v[5]), float(v[6]), float(v[7]), int(v[8])
            if j - i > a.maxspan:
                continue
            loss = ta * (W(E) - lb1)
            cur['terms'].append((loss, n, i, j, E, dp))
            blk_sum[E // 1024] += loss
            blk_max[E // 1024] = max(blk_max[E // 1024], loss)
    for r in rows:
        tot = sum(t[0] for t in r['terms'])
        if not a.quiet:
            print(r['head'], ' cell-loss total %.3e' % tot)
            for t in sorted(r['terms'], reverse=True)[:6]:
                print('   loss %.3e term %d (%d,%d) E %d = %.4f SC block %d, nearest point %d' % (
                    t[0], t[1], t[2], t[3], t[4], t[4] / SC, t[4] // 1024, t[5]))
    print('blocks by summed loss:')
    for j, s in sorted(blk_sum.items(), key=lambda kv: -kv[1])[:40]:
        print('  block %4d [%.3f, %.3f) SC  sum %.3e  max %.3e' % (j, j * 1024 / SC, (j + 1) * 1024 / SC, s, blk_max[j]))
    sel = set()
    for j, mx in blk_max.items():
        if mx > a.thr:
            sel.update(range(max(0, j - a.pad), j + a.pad + 1))
    runs = []
    for j in sorted(sel):
        if runs and j == runs[-1][1] + 1:
            runs[-1][1] = j
        else:
            runs.append([j, j])
    fine = ','.join('%d-%d:2' % tuple(r) for r in runs)
    print('fine candidates (max loss > %.1e, padded by %d): %s' % (a.thr, a.pad, fine))
    if a.fine_out:
        open(a.fine_out, 'w').write(fine + '\n')

if __name__ == '__main__':
    main()
