#!/usr/bin/env python3
"""`xgen select` of one root, split over parallel xgen processes.

    python selpar.py MODEL.pkl ENG EXACT BOX IN OUT --allowed A [--xgen X] [--procs 8] [--part-leaves 20000]
                     [--tmp DIR]

The tree IN is cut into subtrees of at most --part-leaves leaves (xsplit.parts: the start state of each part
comes from the checker's split functions); each part runs `xgen select` from its own box, and OUT is the
skeleton records with every part's output in place.  xgen select treats every leaf on its own (re-certify
with anchors restricted to A when the leaf uses a point outside A, else keep it), so the parts give a valid
select of the whole tree; a certificate can differ from a whole-tree run only where the LP's warm start
depends on the previous leaf.  Prints xgen's summary line with the totals.
"""
import argparse
import os
import pickle
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xsplit                                 # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    for x in ('model', 'eng', 'exact', 'box', 'inp', 'out'):
        ap.add_argument(x)
    ap.add_argument('--allowed', required=True)
    ap.add_argument('--xgen', default=os.path.join(HERE, 'cpp_race', 'xgen'))
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--part-leaves', type=int, default=20000)
    ap.add_argument('--tmp', default=None)
    a = ap.parse_args()
    t0 = time.time()
    M = pickle.load(open(a.model, 'rb'))
    Q, NP = M.Q, M.NP
    v = list(map(int, open(a.box).read().split()))
    s0 = (v[:Q], v[Q:2 * Q], v[2 * Q:2 * Q + NP], v[2 * Q + NP:])
    lines = [ln.rstrip('\n') for ln in open(a.inp) if ln.strip() and ln[0] != '#']
    cuts, flat = xsplit.parts(M, s0, lines, a.part_leaves)
    tmp = tempfile.mkdtemp(prefix='selpar_', dir=a.tmp or os.path.dirname(os.path.abspath(a.out)))
    jobs = []
    for n, (i, j, d) in enumerate(cuts):
        if j - i == 1 and lines[i][0] != 'L':
            continue                                  # a reflection record: nothing to select
        b = os.path.join(tmp, 'p%d.box' % n)
        f = os.path.join(tmp, 'p%d.nodes' % n)
        open(b, 'w').write(' '.join(map(str, flat[i])) + '\n')
        with open(f, 'w') as fh:
            fh.write('\n'.join(lines[i:j]) + '\n')
        jobs.append((n, i, j, b, f, os.path.join(tmp, 'p%d.out' % n)))
    jobs.sort(key=lambda x: -(x[2] - x[1]))

    def run(job):
        n, i, j, b, f, o = job
        c = subprocess.run([a.xgen, 'select', a.eng, a.exact, b, f, o, '--allowed', a.allowed],
                           capture_output=True, text=True)
        return n, c.returncode, c.stdout.strip(), c.stderr[-500:]
    res = {}
    with ThreadPoolExecutor(a.procs) as pool:
        for n, rc, out, err in pool.map(run, jobs):
            assert rc == 0, (n, out, err)
            w = out.split()
            res[n] = (int(w[w.index('leaves') + 1]), int(w[w.index('changed') + 1]), int(w[w.index('kept') + 1]))
    byn = {x[0]: x for x in jobs}
    leaves = changed = kept = 0
    with open(a.out + '.tmp', 'w') as fo:
        k = 0
        for n, (i, j, d) in enumerate(cuts):
            fo.write('\n'.join(lines[k:i]) + ('\n' if i > k else ''))
            if n in byn:
                for ln in open(byn[n][5]):
                    if ln.strip() and ln[0] != '#':
                        fo.write(ln)
                l_, c_, k_ = res[n]
                leaves += l_; changed += c_; kept += k_
            else:
                fo.write('\n'.join(lines[i:j]) + '\n')
            k = j
        fo.write('\n'.join(lines[k:]) + ('\n' if len(lines) > k else ''))
        fo.write('# select changed %d kept %d\n' % (changed, kept))
    os.rename(a.out + '.tmp', a.out)
    shutil.rmtree(tmp)
    print('# select ok 1 leaves %d changed %d kept %d secs %.2f parts %d' % (leaves, changed, kept, time.time() - t0,
                                                                           len(jobs)))


if __name__ == '__main__':
    main()
