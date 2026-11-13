#!/usr/bin/env python3
"""Tree-size estimate for a new model from leaf-uniform subtree samples of the m12r_p trees.

    python estsum.py ESTDIR RESULTS.txt [OLDMODEL_RESULTS.txt]

ESTDIR/p<k>.list: "i oldleaves depth leafindex" (xsample2, root k); RESULTS.txt: runboxes.sh output on the new
model ("p<k>_<i> rc R leaves refl fails maxdepth user_s check").  Each sampled old leaf maps to the lowest
subtree around it with >= S0 old leaves; r = new / old for that subtree (leaves + reflection leaves).  Per root,
the estimate is old_total x mean(r) (a leaf-weighted mean of local ratios), with the standard error of the mean.
Roots without samples (1, 3, 4, 5, 7: 15,320 old leaves in all) are scaled by the pooled mean.
Most m12r_p subtrees were built on m12r (far pairs beyond 16 SC count 0), so OLDMODEL_RESULTS (the same boxes
rebuilt on m12r_xf with the same binary) gives the like-for-like comparison: the same estimate for the old model
rebuilt today, and the ratio of the two.
"""
import math
import os
import sys
from collections import defaultdict

OLD = {0: 1146185, 1: 3764, 2: 1054703, 3: 5185, 4: 46, 5: 3233, 6: 939131, 7: 3111, 8: 1194382}


def read(res):
    new, cpu, fails, bad = {}, {}, {}, []
    for ln in open(res):
        v = ln.split()
        if len(v) < 9 or not v[0].startswith('p'):
            continue
        if v[2] != '0':
            bad.append(ln.strip())
            continue
        new[v[0]] = int(v[3]) + int(v[4])
        fails[v[0]] = int(v[5])
        cpu[v[0]] = float(v[7])
    return new, cpu, fails, bad


def main():
    est, res = sys.argv[1], sys.argv[2]
    for f in sys.argv[2:]:
        print('==', f)
        report(est, *read(f))


def report(est, new, cpu, fails, bad):
    rs, tot_new, tot_old, out = defaultdict(list), 0.0, 0, []
    allr = []
    for k in sorted(OLD):
        p = os.path.join(est, 'p%d.list' % k)
        if not os.path.exists(p):
            continue
        for ln in open(p):
            i, old = ln.split()[:2]
            key = 'p%d_%s' % (k, i)
            if key in new:
                rs[k].append(new[key] / int(old))
                allr.append(new[key] / int(old))
    pooled = sum(allr) / len(allr)
    total, var = 0.0, 0.0
    print('root  n   mean r   se      old leaves   new estimate')
    for k in sorted(OLD):
        r = rs.get(k)
        if r:
            m = sum(r) / len(r)
            se = math.sqrt(sum((x - m) ** 2 for x in r) / (len(r) - 1) / len(r)) if len(r) > 1 else 0
        else:
            m, se = pooled, 0.0
        e = OLD[k] * m
        total += e
        var += (OLD[k] * se) ** 2
        print('%4d %3d  %6.3f  %6.3f  %11d  %12.0f' % (k, len(r or []), m, se, OLD[k], e))
    print('total old %d, new estimate %.0f +- %.0f (ratio %.3f)' % (sum(OLD.values()), total, math.sqrt(var),
                                                                   total / sum(OLD.values())))
    n_old = sum(int(l.split()[1]) for k in OLD if os.path.exists(os.path.join(est, 'p%d.list' % k))
                for l in open(os.path.join(est, 'p%d.list' % k)) if 'p%d_%s' % (k, l.split()[0]) in new)
    print('sampled subtrees %d: old leaves %d, new leaves %d, certify failures %d (%.2f %% of new leaves), '
          'CPU %.0f s (%.3f s per new leaf)' % (len(new), n_old, sum(new.values()), sum(fails.values()),
                                                100.0 * sum(fails.values()) / max(1, sum(new.values())),
                                                sum(cpu.values()), sum(cpu.values()) / max(1, sum(new.values()))))
    if bad:
        print('non-zero rc:', *bad, sep='\n  ')


if __name__ == '__main__':
    main()
