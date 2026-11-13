#!/usr/bin/env python3
"""Shared tangent-point table for a set of finished roots, final exact checks, and the Lean inputs.

    python finalize.py WORK --roots 4,1 [--min-use 2] [--rounds 2] [--procs 8] [--no-select] [--par] [--xgen X] [--fuel F]

1. Usage of every point by the generated trees (xgen check --usage on WORK/r<k>/tree.nodes).
2. Selection (q9ptt select9 at q = 12): A = grid points (x % 256 == 0) plus the points used by at least
   --min-use leaf terms over all roots; every leaf that uses a point outside A is re-certified with anchors
   restricted to A (xgen select, exact check per leaf); a leaf that fails keeps its certificate (its points
   stay).  Further rounds repeat with A = the points still in use with at least --min-use uses.
3. Table: ptable.py on the final usage (hull intervals, per-point n).
4. Checks against the final table: xgen check --table (C++) and pycheck.py --table (Python mirror).
5. WORK/trees.pkl ({k: dict(idx, bits, nbits)}), WORK/table.lean.txt, WORK/summary.json.

--par (roots of about 10^6 leaves): the roots are handled one at a time, each split over --procs processes:
selection through selpar.py (xgen select per subtree; the same output as one xgen select) and the Python check
through pycheck_par.py --lowmem --table (the same exact walk as pycheck.py, per subtree).  The usage and C++
checks stay whole-root xgen runs (--procs of them at once).
"""
import argparse
import json
import os
import pickle
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xio                                    # noqa: E402
import fb12                                   # noqa: E402

XGEN = os.path.join(HERE, 'cpp_race', 'xgen')


def usage(W, k, tree, table=None):
    out = os.path.join(W, 'r%d' % k, 'usage.txt')
    cmd = [XGEN, 'check', os.path.join(W, 'model.pkl.eng'), os.path.join(W, 'exact.txt'),
           os.path.join(W, 'root_%d.box' % k), tree, '--usage', out]
    if table:
        cmd += ['--table', table]
    c = subprocess.run(cmd, capture_output=True, text=True)
    assert c.returncode == 0, (k, c.stdout, c.stderr[:500])
    u = {}
    for ln in open(out):
        x, n, a, b = map(int, ln.split())
        u[x] = n
    return u, out, c.stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('work')
    ap.add_argument('--roots', required=True)
    ap.add_argument('--min-use', type=int, default=20)
    ap.add_argument('--rounds', type=int, default=3)
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--no-select', action='store_true')
    ap.add_argument('--par', action='store_true', help='per-root parallel select and Python check (large roots)')
    ap.add_argument('--xgen', default=None, help='xgen binary (default cpp_race/xgen)')
    ap.add_argument('--fuel', type=int, default=None, help='walk fuel of pycheck_par (default its own, 400)')
    a = ap.parse_args()
    global XGEN
    if a.xgen:
        XGEN = os.path.abspath(a.xgen)
    W = os.path.abspath(a.work)
    ks = [int(x) for x in a.roots.split(',')]
    eng, ex = os.path.join(W, 'model.pkl.eng'), os.path.join(W, 'exact.txt')
    t0 = time.time()
    cur = {k: os.path.join(W, 'r%d' % k, 'tree.nodes') for k in ks}
    log = {}
    with ThreadPoolExecutor(a.procs) as pool:
        U = dict(zip(ks, pool.map(lambda k: usage(W, k, cur[k]), ks)))
    tot = Counter()
    for k in ks:
        tot.update(U[k][0])
    log['points_generated'] = len(tot)
    P = pickle.load(open(os.path.join(W, 'pts.pkl'), 'rb'))
    grid = {x for x in P if x % 256 == 0 and P[x]}
    if not a.no_select:
        for rnd in range(a.rounds):
            A = grid | {x for x, n in tot.items() if n >= a.min_use}
            ap_ = os.path.join(W, 'allowed_%d.txt' % rnd)
            open(ap_, 'w').write('\n'.join(map(str, sorted(A))) + '\n')

            def sel(k):
                out = os.path.join(W, 'r%d' % k, 'tree_sel%d.nodes' % rnd)
                if a.par:
                    cmd = [sys.executable, os.path.join(HERE, 'selpar.py'), os.path.join(W, 'model.pkl'), eng, ex,
                           os.path.join(W, 'root_%d.box' % k), cur[k], out, '--allowed', ap_, '--xgen', XGEN,
                           '--procs', str(a.procs)]
                else:
                    cmd = [XGEN, 'select', eng, ex, os.path.join(W, 'root_%d.box' % k), cur[k], out, '--allowed', ap_]
                c = subprocess.run(cmd, capture_output=True, text=True)
                assert c.returncode == 0, (k, c.stdout, c.stderr[:500])
                print('  select root', k, c.stdout.strip(), flush=True)
                return out, c.stdout.strip()
            with ThreadPoolExecutor(1 if a.par else a.procs) as pool:
                R = dict(zip(ks, pool.map(sel, ks)))
            for k in ks:
                cur[k] = R[k][0]
            with ThreadPoolExecutor(a.procs) as pool:
                U = dict(zip(ks, pool.map(lambda k: usage(W, k, cur[k]), ks)))
            tot = Counter()
            for k in ks:
                tot.update(U[k][0])
            log['round%d' % rnd] = dict(allowed=len(A), points=len(tot), select={k: R[k][1] for k in ks})
            print('round', rnd, 'allowed', len(A), 'points in use', len(tot), flush=True)
    # final table
    pref = os.path.join(W, 'table')
    c = subprocess.run([sys.executable, os.path.join(HERE, 'ptable.py'), os.path.join(W, 'model.pkl'),
                        os.path.join(W, 'pts.pkl'), pref] + [U[k][1] for k in ks], capture_output=True, text=True)
    assert c.returncode == 0, c.stderr[-2000:]
    log['ptable'] = c.stdout.strip()
    print(log['ptable'], flush=True)
    # checks against the final table
    M = pickle.load(open(os.path.join(W, 'model.pkl'), 'rb'))
    roots = fb12.G.roots_of(M)
    trees = {}
    summ = {}

    def fin(k):
        u, _, cs = usage(W, k, cur[k], pref + '.xgen.txt')
        return cs

    def pyfin(k):
        if a.par:
            cmd = [sys.executable, os.path.join(HERE, 'pycheck_par.py'), os.path.join(W, 'model.pkl'),
                   os.path.join(W, 'pts.pkl'), os.path.join(W, 'root_%d.box' % k), cur[k], '--table', pref + '.lean.txt',
                   '--lowmem', '--procs', str(a.procs)] + (['--fuel', str(a.fuel)] if a.fuel else [])
        else:
            cmd = [sys.executable, os.path.join(HERE, 'pycheck.py'), os.path.join(W, 'model.pkl'),
                   os.path.join(W, 'pts.pkl'), os.path.join(W, 'root_%d.box' % k), cur[k], '--table', pref + '.lean.txt']
        py = subprocess.run(cmd, capture_output=True, text=True)
        print('  pycheck root', k, py.stdout.strip()[:300], flush=True)
        return py.returncode == 0, py.stdout.strip()
    with ThreadPoolExecutor(a.procs) as pool:
        FC = dict(zip(ks, pool.map(fin, ks)))
    with ThreadPoolExecutor(1 if a.par else a.procs) as pool:
        FP = dict(zip(ks, pool.map(pyfin, ks)))
    F = {k: (FC[k],) + FP[k] for k in ks}
    for k in ks:
        bits, end = xio.zstream_lines(open(cur[k]), len(M.TS), fb12.axis_bits(M), M.NP.bit_length(), M.QB)
        trees[k] = dict(idx=roots[k], bits=bits, nbits=end)
        cs, pyok, pyout = F[k]
        summ[k] = dict(tree=os.path.relpath(cur[k], W), cpp_check=cs, py_ok=pyok, py=pyout, nbits=end)
        assert ' ok 1 ' in cs and pyok, (k, cs, pyout)
    pickle.dump(trees, open(os.path.join(W, 'trees.pkl'), 'wb'))
    import shutil
    for k in ks:
        shutil.copyfile(cur[k], os.path.join(W, 'r%d' % k, 'final.nodes'))
    log.update(roots=summ, secs=time.time() - t0)
    json.dump(log, open(os.path.join(W, 'summary.json'), 'w'), indent=1)
    print(json.dumps(log, indent=1))


if __name__ == '__main__':
    main()
