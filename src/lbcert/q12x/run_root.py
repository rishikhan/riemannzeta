#!/usr/bin/env python3
"""Orchestrator for one root: frontier, parallel subtree jobs (resumable), assembly, exact checks.

    python run_root.py WORK ROOT [--depth 6] [--procs 8] [--xgen cpp_race/xgen] [--nice 0] [--opts "--k 3"]
                       [--check] [--pycheck]

WORK holds model.pkl, pts.pkl, model.pkl.eng, exact.txt and root_<k>.box (xio.setup).  Files go to
WORK/r<ROOT>/: top.nodes + jobs.txt (xgen frontier at --depth), job_<id>.nodes (xgen tree, one process
per job; an existing job file is complete because xgen renames it into place only on success, so a rerun
skips it), tree.nodes (assembled), check.txt / usage.txt (xgen check), stats.json.
Every process is independent: no shared state besides the read-only inputs.
"""
import argparse
import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xio                                    # noqa: E402


def run(cmd, log):
    with open(log, 'a') as f:
        return subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT).returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('work'); ap.add_argument('root', type=int)
    ap.add_argument('--depth', type=int, default=6)
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--xgen', default=os.path.join(HERE, 'cpp_race', 'xgen'))
    ap.add_argument('--nice', type=int, default=0)
    ap.add_argument('--opts', default='')
    ap.add_argument('--fthreads', type=int, default=1, help='threads of the (sequential) frontier step')
    ap.add_argument('--part', default='0/1', help='i/N: run only jobs with id %% N == i (one slice per node)')
    ap.add_argument('--frontier-only', action='store_true')
    ap.add_argument('--budget', type=int, default=0, help='leaf budget per job; a job over it is resplit')
    ap.add_argument('--resplit-depth', type=int, default=4)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--pycheck', action='store_true')
    a = ap.parse_args()
    W = os.path.abspath(a.work)
    R = os.path.join(W, 'r%d' % a.root)
    os.makedirs(R, exist_ok=True)
    eng, ex, box = os.path.join(W, 'model.pkl.eng'), os.path.join(W, 'exact.txt'), os.path.join(W, 'root_%d.box' % a.root)
    pre = (['nice', '-n', str(a.nice)] if a.nice else []) + [a.xgen]
    opts = a.opts.split()
    top, jobs = os.path.join(R, 'top.nodes'), os.path.join(R, 'jobs.txt')
    t0 = time.time()
    if not os.path.exists(top):
        rc = run(pre + ['frontier', eng, ex, box, top, jobs, '--depth', str(a.depth), '--threads', str(a.fthreads)] + opts, os.path.join(R, 'frontier.log'))
        assert rc == 0, 'frontier failed'
    t_front = time.time() - t0
    jl = [ln.split() for ln in open(jobs)] if os.path.exists(jobs) else []
    if a.frontier_only:
        print('root %d: frontier with %d jobs' % (a.root, len(jl)))
        return
    pi, pn = map(int, a.part.split('/'))
    budget = ['--budget', str(a.budget)] if a.budget else []

    def boxfile(jid, vals):
        bx = os.path.join(R, 'job_%s.box' % jid)
        with open(bx, 'w') as f:
            f.write(' '.join(vals) + '\n')
        return bx

    def pending(jid, vals):
        """jobs (id, box) still to run under job jid (itself, or its sub-jobs when it was resplit)"""
        out = os.path.join(R, 'job_%s.nodes' % jid)
        sub = os.path.join(R, 'job_%s.jobs' % jid)
        if os.path.exists(out):
            if os.path.exists(sub):
                res = []
                for ln in open(sub):
                    v = ln.split()
                    res += pending('%s.%s' % (jid, v[0]), v[1:])
                return res
            return []
        return [(jid, boxfile(jid, vals))]
    todo = []
    for v in jl:
        if int(v[0]) % pn != pi:
            continue
        todo += pending(v[0], v[1:])
    print('root %d: %d top jobs, %d to run' % (a.root, len(jl), len(todo)), flush=True)
    done = [0]
    fails = []
    lock = threading.Lock()

    def one(jid, bx, pool, futs):
        out = os.path.join(R, 'job_%s.nodes' % jid)
        log = os.path.join(R, 'job_%s.log' % jid)
        rc = run(pre + ['tree', eng, ex, bx, out] + budget + opts, log)
        if rc == 1 and a.budget and os.path.exists(out + '.tmp') and 'rc 1 ' in open(out + '.tmp').read()[-400:]:
            # leaf budget exceeded: split this box into sub-jobs (frontier at --resplit-depth)
            rc = run(pre + ['frontier', eng, ex, bx, out, os.path.join(R, 'job_%s.jobs' % jid), '--depth',
                            str(a.resplit_depth)] + opts, log)
            if rc == 0:
                subs = [ln.split() for ln in open(os.path.join(R, 'job_%s.jobs' % jid))]
                with lock:
                    for v in subs:
                        sid = '%s.%s' % (jid, v[0])
                        futs.append(pool.submit(one, sid, boxfile(sid, v[1:]), pool, futs))
                print('  job %s resplit into %d' % (jid, len(subs)), flush=True)
        with lock:
            done[0] += 1
            if rc:
                fails.append(jid)
            if done[0] % 10 == 0 or rc:
                print('  job %s rc %d (%d done) %.0fs' % (jid, rc, done[0], time.time() - t0), flush=True)
        return rc
    with ThreadPoolExecutor(a.procs) as pool:
        futs = []
        with lock:
            for jid, bx in todo:
                futs.append(pool.submit(one, jid, bx, pool, futs))
        i = 0
        while True:
            with lock:
                if i >= len(futs):
                    break
                f = futs[i]
            f.result()
            i += 1
    assert not fails, 'job failures: %s' % fails
    missing = [v[0] for v in jl if pending(v[0], v[1:])]
    if missing:
        print('root %d: slice %s done, %d top jobs of other slices missing; not assembling' % (a.root, a.part, len(missing)))
        return
    t_jobs = time.time() - t0 - t_front
    # assemble and collect stats
    tree = os.path.join(R, 'tree.nodes')
    nodes = xio.assemble(top, R)
    agg = {}
    import glob
    for st in [xio.stats_line(top)] + [xio.stats_line(f) for f in glob.glob(os.path.join(R, 'job_*.nodes'))]:
        for k, v in (st or {}).items():
            agg[k] = agg.get(k, 0) + v
    with open(tree, 'w') as f:
        for nd in nodes:
            if nd[0] == 'S':
                f.write('S %d %d\n' % (nd[1], nd[2]))
            elif nd[0] == 'R':
                f.write('R\n')
            else:
                f.write(' '.join(['L', str(len(nd[1]))] + [str(x) for t in nd[1] for x in t] + [str(len(nd[2]))]
                                 + [str(x) for y in nd[2] for x in y]) + '\n')
    res = dict(root=a.root, depth=a.depth, jobs=len(jl), wall_frontier=t_front, wall_jobs=t_jobs,
               leaves=int(agg.get('leaves', 0)), refl=int(agg.get('refl', 0)), splits=int(agg.get('splits', 0)),
               fails=int(agg.get('fails', 0)), cpu_secs=agg.get('secs', 0), float_secs=agg.get('float_secs', 0),
               cert_secs=agg.get('cert_secs', 0), evals=int(agg.get('evals', 0)), opts=a.opts)
    wasted = 0.0
    for f in glob.glob(os.path.join(R, 'job_*.log')):
        for ln in open(f):
            if ln.startswith('# rc 1 '):
                wasted += float(ln.split()[ln.split().index('secs') + 1])
    res['wasted_secs'] = wasted
    res['cpu_secs'] += wasted
    res['leaves_per_core_sec'] = (res['leaves'] + res['refl']) / max(1e-9, res['cpu_secs'])
    if a.check:
        c = subprocess.run([a.xgen, 'check', eng, ex, box, tree, '--usage', os.path.join(R, 'usage.txt')],
                           capture_output=True, text=True)
        open(os.path.join(R, 'check.txt'), 'w').write(c.stdout + c.stderr)
        res['check'] = c.stdout.strip()
        res['check_ok'] = c.returncode == 0
    if a.pycheck:
        c = subprocess.run([sys.executable, os.path.join(HERE, 'pycheck.py'), os.path.join(W, 'model.pkl'),
                            os.path.join(W, 'pts.pkl'), box, tree], capture_output=True, text=True)
        res['pycheck'] = c.stdout.strip()
        res['pycheck_ok'] = c.returncode == 0
    json.dump(res, open(os.path.join(R, 'stats.json'), 'w'), indent=1)
    print(json.dumps(res, indent=1))


if __name__ == '__main__':
    main()
