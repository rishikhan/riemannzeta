#!/usr/bin/env python3
"""Login-node CMA-ES driver for the q = 12 window on Perlmutter; pm_worker.py does the evaluations.

    python pm_driver.py --run RUN --start final_q12.json --x0 refit96.json [--popsize 48]
                        [--sigma 9.5e-5] [--rounds 64] [--x0-mode nearest] [--ref96 0.67371174]

Each generation: ask, write RUN/gen.pkl (the pending population, so a restart re-uses it), write
one task per candidate to RUN/tasks/, wait for RUN/results/, tell, append every evaluation to
RUN/log.jsonl, save RUN/es.pkl.  Claims in RUN/running/ that have not been touched for --stale
seconds go back to RUN/tasks/.  The driver only coordinates.

Warm start (--x0-mode): 'best' uses the weights x of the best evaluation so far (RUN/x0_best.json;
initially --x0); 'nearest' uses the weights of the evaluated window (RUN/done/) nearest to the
candidate in xfree.  A resume with a different --popsize finishes the pending generation, then
restarts CMA at the current mean and sigma with the new population.

Stop rule: every --check-every generations the best evaluation so far is re-run at 96 rounds
(task rGGG, warm from its own weights, not waited for).  The run stops when the best 96-round
value has gained less than --tol over the last --stop-gens generations (--ref96: the 96-round
value at the start), at --max-gen, or at RUN/STOP.  Every generation line in the log counts the
side conditions that rejected candidates (fails) and the totals since the start (fails_total).
"""
import argparse
import collections
import json
import os
import pickle
import shutil
import time
from pathlib import Path

import numpy as np

KEEP = ('achieved', 'ceiling', 'H', 'B', 'eps', 'kappa_lb', 'fail', 'margins', 'secs', 'worker', 'x0')


def put_task(run, name, task):
    tmp = run / 'tasks' / (name + '.tmp')
    tmp.write_text(json.dumps(task))
    os.rename(tmp, run / 'tasks' / (name + '.json'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', required=True)
    ap.add_argument('--start', required=True)
    ap.add_argument('--x0', required=True)
    ap.add_argument('--popsize', type=int, default=48)
    ap.add_argument('--sigma', type=float, default=9.5e-5)
    ap.add_argument('--rounds', type=int, default=64)
    ap.add_argument('--x0-mode', choices=['best', 'nearest'], default='nearest')
    ap.add_argument('--q', type=int, default=12)
    ap.add_argument('--kb', type=int, default=4194304)
    ap.add_argument('--seed', type=int, default=2203)
    ap.add_argument('--max-gen', type=int, default=200)
    ap.add_argument('--stale', type=float, default=180)
    ap.add_argument('--tol', type=float, default=1e-7)
    ap.add_argument('--check-every', type=int, default=3)
    ap.add_argument('--stop-gens', type=int, default=6)
    ap.add_argument('--ref96', type=float, default=None, help='96-round best at the start')
    a = ap.parse_args()
    import cma
    run = Path(a.run)
    for d in ('tasks', 'running', 'results', 'done'):
        (run / d).mkdir(parents=True, exist_ok=True)
    log = open(run / 'log.jsonl', 'a')
    x0b = run / 'x0_best.json'
    if not x0b.exists():
        shutil.copy(a.x0, x0b)
    best = json.load(open(x0b))
    if (run / 'es.pkl').exists():
        es, gen, _ = pickle.load(open(run / 'es.pkl', 'rb'))
    else:
        d = json.load(open(a.start))
        xs = d['window']['xfree'] if 'window' in d else d['xfree']
        es = cma.CMAEvolutionStrategy(list(xs), a.sigma, {'popsize': a.popsize, 'seed': a.seed,
                                                          'verbose': -9})
        gen = 0
    st = json.load(open(run / 'stop_state.json')) if (run / 'stop_state.json').exists() else \
        dict(ref96=[[gen - 1, a.ref96]] if a.ref96 else [], checked=[], fails_total={})
    fails_total = collections.Counter(st['fails_total'])

    # index of evaluated windows for the nearest warm start
    PX, PN = [], []

    def index(path):
        try:
            r = json.load(open(path))
        except (OSError, ValueError):
            return
        if r.get('achieved', -1) > 0 and r.get('x') and path.name.startswith('g'):
            PX.append(np.asarray(r['xfree'], float))
            PN.append(str(path.resolve()))
    for p in sorted((run / 'done').glob('g*.json')):
        index(p)

    def x0_for(x):
        if a.x0_mode == 'best' or not PX:
            return str(x0b.resolve())
        return PN[int(np.argmin(np.sum((np.asarray(PX) - np.asarray(x)) ** 2, axis=1)))]

    def save_state():
        st['fails_total'] = dict(fails_total)
        (run / 'stop_state.tmp').write_text(json.dumps(st))
        os.replace(run / 'stop_state.tmp', run / 'stop_state.json')

    def collect_refs():
        for p in sorted((run / 'results').glob('r*.json')):
            r = json.load(open(p))
            g = int(p.stem[1:4])
            st['ref96'].append([g, r.get('achieved', -1.0)])
            log.write(json.dumps(dict(ref96_gen=g, source=r.get('source'), achieved=r.get('achieved'),
                                      ceiling=r.get('ceiling'), kappa_lb=r.get('kappa_lb'),
                                      secs=r.get('secs'))) + '\n')
            log.flush()
            print('ref96 gen', g, r.get('source'), r.get('achieved'), flush=True)
            os.replace(p, run / 'done' / p.name)
            save_state()

    def best96_at(g):
        v = [x for gg, x in st['ref96'] if gg <= g and x is not None]
        return max(v) if v else None

    while gen < a.max_gen and not (run / 'STOP').exists():
        if (run / 'gen.pkl').exists():
            g, X = pickle.load(open(run / 'gen.pkl', 'rb'))
            assert g == gen
            es.ask()                             # es.pkl predates this ask; tell needs one
        else:
            if es.popsize != a.popsize:          # restart at the same mean and sigma
                es = cma.CMAEvolutionStrategy(list(es.mean), es.sigma, {
                    'popsize': a.popsize, 'seed': a.seed + gen, 'verbose': -9})
                log.write(json.dumps(dict(gen=gen, restart_popsize=a.popsize, sigma=float(es.sigma))) + '\n')
            X = es.ask()
            pickle.dump((gen, X), open(run / 'gen.pkl', 'wb'))
        names = ['g%03d_i%02d' % (gen, i) for i in range(len(X))]
        for n, x in zip(names, X):
            if not (run / 'results' / (n + '.json')).exists() and not any((run / 'running').glob(n + '.*')) \
                    and not (run / 'tasks' / (n + '.json')).exists():
                put_task(run, n, dict(xfree=list(map(float, x)), x0=x0_for(x), rounds=a.rounds,
                                      q=a.q, kb=a.kb))
        t0 = time.time()
        while True:
            collect_refs()
            have = [(run / 'results' / (n + '.json')).exists() for n in names]
            if all(have) or (run / 'STOP').exists():
                break
            now = time.time()
            for c in (run / 'running').glob('*.*'):
                try:
                    if now - c.stat().st_mtime > a.stale:
                        n = c.name.split('.')[0]
                        if not (run / 'results' / (n + '.json')).exists():
                            os.rename(c, run / 'tasks' / (n + '.json'))
                            print('requeued', c.name, flush=True)
                        else:
                            c.unlink()
                except OSError:
                    pass
            time.sleep(5)
        if not all(have):
            break
        res = [json.load(open(run / 'results' / (n + '.json'))) for n in names]
        f = [r['achieved'] for r in res]
        es.tell(X, [-v for v in f])
        fails = collections.Counter(k for r in res for k in r.get('fail', []))
        fails_total.update(fails)
        for i, (x, r) in enumerate(zip(X, res)):
            e = dict(gen=gen, i=i, xfree=list(map(float, x)), rounds=a.rounds)
            e.update({k: r[k] for k in KEEP if k in r})
            log.write(json.dumps(e) + '\n')
        i = int(np.argmax(f))
        prev = best['achieved']
        if f[i] > prev:
            best = dict(res[i], gen=gen, i=i, rounds=a.rounds)
            tmp = run / 'best.tmp'
            tmp.write_text(json.dumps(best, indent=1))
            shutil.copy(tmp, run / 'best.json')
            os.replace(tmp, x0b)
        log.write(json.dumps(dict(gen=gen, gen_best=f[i], best=best['achieved'],
                                  best_kappa_lb=best.get('kappa_lb'), gain=max(best['achieved'] - prev, 0.0),
                                  nfail=sum(v < 0 for v in f), fails=dict(fails),
                                  fails_total=dict(fails_total), sigma=float(es.sigma),
                                  rounds=a.rounds, x0_mode=a.x0_mode,
                                  wall=round(time.time() - t0, 1), t=time.time())) + '\n')
        log.flush()
        print('gen', gen, 'gen_best %.10f best %.10f sigma %.3g wall %.0f fails %s' % (
            f[i], best['achieved'], es.sigma, time.time() - t0, dict(fails)), flush=True)
        for n in names:
            os.replace(run / 'results' / (n + '.json'), run / 'done' / (n + '.json'))
            index(run / 'done' / (n + '.json'))
        if (gen + 1) % a.check_every == 0:
            src = 'g%03d_i%02d' % (best['gen'], best['i']) if 'gen' in best else None
            if src and src not in st['checked']:
                st['checked'].append(src)
                put_task(run, 'r%03d' % gen, dict(xfree=best['xfree'], rounds=96, q=a.q, kb=a.kb,
                                                  x0=str((run / 'done' / (src + '.json')).resolve())))
            else:
                st['ref96'].append([gen, best96_at(gen)])
            save_state()
        gen += 1
        pickle.dump((es, gen, []), open(run / 'es.tmp', 'wb'))
        os.replace(run / 'es.tmp', run / 'es.pkl')
        (run / 'gen.pkl').unlink()
        g_now = max((gg for gg, _ in st['ref96']), default=None)
        if g_now is not None:
            old = best96_at(g_now - a.stop_gens)
            new = best96_at(g_now)
            if old is not None and new is not None and new - old < a.tol and \
                    any(gg <= g_now - a.stop_gens for gg, _ in st['ref96']) and \
                    g_now - min(gg for gg, _ in st['ref96']) >= a.stop_gens:
                print('stop: 96-round best gained %.2e over %d generations' % (new - old, a.stop_gens),
                      flush=True)
                break


if __name__ == '__main__':
    main()
