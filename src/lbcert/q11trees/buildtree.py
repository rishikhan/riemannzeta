#!/usr/bin/env python3
"""Complete exact tree set for a model with the production generator, split by two frontier levels.

    python buildtree.py W OUT [--roots all] [--procs 20] [--depth 10] [--depth2 8] [--budget 2000]
    python buildtree.py W OUT --assemble [--roots all] [--procs 9]

Per root k (OUT/r<k>/, the q12x run_root.py resplit layout, so xio.assemble reads it):
* top.nodes + jobs.txt: xgen frontier of root_<k>.box at --depth;
* job_<j>.nodes + job_<j>.jobs: xgen frontier of every root-level job box at --depth2;
* job_<j>.<s>.nodes: xgen tree of every sub-job under --budget leaves; a sub-job over the budget is split by a
  frontier at --depth2 into job_<j>.<s>.<t> (nested as needed).
Frontiers run without the race options; trees run with the production options.
A node file exists only when xgen finished it, so a rerun skips finished work.
--assemble: r<k>/tree.nodes (xio.assemble), then xgen check --usage (r<k>/check.txt, usage.txt) and
r<k>/stats.json (leaves, refl, fails, max depth from the tree; CPU from the stats lines and the logs of
over-budget attempts).
"""
import argparse
import glob
import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

LB = os.environ.get('LB', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.join(LB, 'q12x'))
import xio                                                      # noqa: E402

XGEN = os.environ.get('XGEN', os.path.join(LB, 'q12x', 'cpp_race', 'xgen'))
ENV = dict(os.environ, XG_FAILSCAN='1', XG_WIDE='4', XG_WIDE_NARROW='0.01', XG_WIDTHFIX='1', XG_CACHE='16000')
TREE_OPTS = ['--maxdepth', '400', '--race-stall', '0', '--race-cap', '300']


def run(cmd, log):
    with open(log, 'a') as f:
        return subprocess.run(['nice', '-n', '10'] + cmd, stdout=f, stderr=subprocess.STDOUT, env=ENV).returncode


def boxfile(R, jid, vals):
    bx = os.path.join(R, 'job_%s.box' % jid)
    with open(bx, 'w') as f:
        f.write(' '.join(vals) + '\n')
    return bx


def build(a):
    W = os.path.abspath(a.W)
    eng, ex = os.path.join(W, 'model.pkl.eng'), os.path.join(W, 'exact.txt')
    pool = ThreadPoolExecutor(a.procs)
    lock = threading.Lock()
    futs, fails = [], []
    t0 = time.time()

    def submit(*args):
        with lock:
            futs.append(pool.submit(*args))

    def frontier(R, jid, bx, depth):
        """frontier of box bx into job_<jid>.nodes / .jobs (jid '' = the root: top.nodes / jobs.txt); then
        every listed job as a tree job"""
        out = os.path.join(R, 'top.nodes' if jid == '' else 'job_%s.nodes' % jid)
        jobs = os.path.join(R, 'jobs.txt' if jid == '' else 'job_%s.jobs' % jid)
        if not os.path.exists(out):
            rc = run([XGEN, 'frontier', eng, ex, bx, out, jobs, '--depth', str(depth)],
                     os.path.join(R, 'frontier.log' if jid == '' else 'job_%s.log' % jid))
            if rc:
                fails.append((R, jid, 'frontier', rc))
                return
        pre = '' if jid == '' else jid + '.'
        for ln in open(jobs):
            v = ln.split()
            sid = pre + v[0]
            if jid == '':
                submit(frontier, R, sid, boxfile(R, sid, v[1:]), a.depth2)
            else:
                submit(tree, R, sid, boxfile(R, sid, v[1:]))

    def tree(R, jid, bx):
        out = os.path.join(R, 'job_%s.nodes' % jid)
        if os.path.exists(out):
            if os.path.exists(os.path.join(R, 'job_%s.jobs' % jid)):
                frontier(R, jid, bx, a.depth2)                  # resplit earlier: resume its parts
            return
        rc = run([XGEN, 'tree', eng, ex, bx, out, '--budget', str(a.budget)] + TREE_OPTS,
                 os.path.join(R, 'job_%s.log' % jid))
        if rc == 1 and os.path.exists(out + '.tmp') and 'rc 1 ' in open(out + '.tmp').read()[-400:]:
            frontier(R, jid, bx, a.depth2)
        elif rc:
            fails.append((R, jid, 'tree', rc))

    for k in a.roots:
        R = os.path.join(a.OUT, 'r%d' % k)
        os.makedirs(R, exist_ok=True)
        submit(frontier, R, '', os.path.join(W, 'root_%d.box' % k), a.depth)
    i = 0
    while True:
        with lock:
            if i >= len(futs):
                break
            f = futs[i]
        f.result()
        i += 1
        if i % 2000 == 0:
            print('%d tasks done, %.0f s' % (i, time.time() - t0), flush=True)
    print('tasks %d, failures %s, wall %.0f s' % (len(futs), fails, time.time() - t0), flush=True)


def assemble_one(W, OUT, k):
    R = os.path.join(OUT, 'r%d' % k)
    eng, ex, box = os.path.join(W, 'model.pkl.eng'), os.path.join(W, 'exact.txt'), os.path.join(W, 'root_%d.box' % k)
    nodes = xio.assemble(os.path.join(R, 'top.nodes'), R)
    leaves = refl = splits = maxd = 0
    stack = [0]                                                 # depth of the next node in preorder
    tree = os.path.join(R, 'tree.nodes')
    with open(tree, 'w') as f:
        for nd in nodes:
            d = stack.pop()
            maxd = max(maxd, d)
            if nd[0] == 'S':
                splits += 1
                stack += [d + 1, d + 1]
                f.write('S %d %d\n' % (nd[1], nd[2]))
            elif nd[0] == 'R':
                refl += 1
                f.write('R\n')
            else:
                leaves += 1
                f.write(' '.join(['L', str(len(nd[1]))] + [str(x) for t in nd[1] for x in t] + [str(len(nd[2]))]
                                 + [str(x) for y in nd[2] for x in y]) + '\n')
    assert not stack, 'tree %d incomplete' % k
    cpu = fails = wasted = 0.0
    files = [os.path.join(R, 'top.nodes')] + glob.glob(os.path.join(R, 'job_*.nodes'))
    for p in files:
        st = xio.stats_line(p) or {}
        cpu += st.get('secs', 0.0)
        fails += st.get('fails', 0.0)
    for p in glob.glob(os.path.join(R, 'job_*.log')):
        for ln in open(p):
            if ln.startswith('# rc 1 '):
                v = ln.split()
                wasted += float(v[v.index('secs') + 1])
    t = time.time()
    c = subprocess.run(['nice', '-n', '10', XGEN, 'check', eng, ex, box, tree, '--usage', os.path.join(R, 'usage.txt')],
                       capture_output=True, text=True)
    open(os.path.join(R, 'check.txt'), 'w').write(c.stdout + c.stderr)
    res = dict(root=k, leaves=leaves, refl=refl, splits=splits, maxdepth=maxd, fails=int(fails),
               cpu_secs=cpu + wasted, wasted_secs=wasted, files=len(files), check_secs=time.time() - t,
               check=[ln for ln in c.stdout.splitlines() if ln.startswith('# check')],
               check_ok=c.returncode == 0 and ' bad 0 ' in c.stdout)
    json.dump(res, open(os.path.join(R, 'stats.json'), 'w'), indent=1)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('W')
    ap.add_argument('OUT')
    ap.add_argument('--roots', default='all')
    ap.add_argument('--procs', type=int, default=20)
    ap.add_argument('--depth', type=int, default=10)
    ap.add_argument('--depth2', type=int, default=8)
    ap.add_argument('--budget', type=int, default=2000)
    ap.add_argument('--assemble', action='store_true')
    a = ap.parse_args()
    a.OUT = os.path.abspath(a.OUT)
    W = os.path.abspath(a.W)
    if a.roots == 'all':
        a.roots = sorted(int(f[5:-4]) for f in os.listdir(W) if f.startswith('root_') and f.endswith('.box'))
    else:
        a.roots = [int(x) for x in a.roots.split(',') if x]
    if not a.assemble:
        build(a)
        return
    with ThreadPoolExecutor(a.procs) as pool:
        rows = list(pool.map(lambda k: assemble_one(W, a.OUT, k), a.roots))
    for r in rows:
        print(json.dumps(r), flush=True)
    tot = {key: sum(r[key] for r in rows) for key in ('leaves', 'refl', 'fails', 'cpu_secs', 'wasted_secs')}
    tot.update(maxdepth=max(r['maxdepth'] for r in rows), all_check_ok=all(r['check_ok'] for r in rows))
    print('total', json.dumps(tot), flush=True)


if __name__ == '__main__':
    main()
