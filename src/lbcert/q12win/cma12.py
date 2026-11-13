#!/usr/bin/env python3
"""CMA-ES over the window coefficients with f = winobj.evaluate (float kappa after a full refit).

    python cma12.py --q 10 --out DIR [--start W.json] [--J 16] [--sigma 1e-4] [--popsize 12]
                    [--workers 6] [--threads 1] [--rounds 64] [--hours 11] [--resume]
    python cma12.py --q 12 --out DIR --batch FILE.json   (evaluate listed windows, no CMA)

Every evaluation is appended to DIR/log.jsonl (generation, index, xfree, achieved, ceiling, B,
eps, kappa_lb, failing side conditions, margins, seconds).  DIR/best.json holds the best window
in the window-search format (xfree, x, achieved, ...); DIR/es.pkl the CMA state after each
generation, so --resume continues with a different --workers / --threads.  Every evaluation uses
the same gmin seed, so differences between windows are not seed noise.  x0 (weights) for the
refit's first round is the start window's converged weights at this q (DIR/base.json).
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse                                  # noqa: E402
import json
import pickle
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

import winobj


def _eval(args):
    xf, q, rounds, threads, x0, kb = args
    try:
        return winobj.evaluate(list(map(float, xf)), q, rounds=rounds, threads=threads, x0=x0, kb=kb)
    except Exception as e:                       # a crashed refit counts as a failed window
        return dict(achieved=-1.0, fail=['error: %r' % e])


def record(gen, i, xf, r):
    keep = ('achieved', 'ceiling', 'H', 'B', 'eps', 'kappa_lb', 'fail', 'margins', 'secs')
    d = dict(gen=gen, i=i, xfree=list(map(float, xf)))
    d.update({k: r[k] for k in keep if k in r})
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--q', type=int, required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--start', default=str(winobj.ROOT / 'src/lbcert/q12win/work/final2_q12.json'))
    ap.add_argument('--J', type=int, default=16)
    ap.add_argument('--sigma', type=float, default=1e-4)
    ap.add_argument('--popsize', type=int, default=12)
    ap.add_argument('--workers', type=int, default=6)
    ap.add_argument('--threads', type=int, default=1)
    ap.add_argument('--rounds', type=int, default=64)
    ap.add_argument('--hours', type=float, default=11.0)
    ap.add_argument('--seed', type=int, default=1701)
    ap.add_argument('--kb', type=int, default=winobj.KB, help='end-gap floor KB (0: none)')
    ap.add_argument('--resume', action='store_true')
    ap.add_argument('--batch', default=None, help='JSON list of xfree vectors to evaluate')
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    log = open(out / 'log.jsonl', 'a')
    t_end = time.time() + 3600 * a.hours

    xs = winobj.load_xfree(a.start)
    x0w = (list(xs) + [0.0] * a.J)[:a.J]
    if (out / 'base.json').exists():
        base = json.load(open(out / 'base.json'))
    else:
        base = winobj.evaluate(x0w, a.q, rounds=a.rounds, threads=max(a.workers * a.threads, 1), kb=a.kb)
        base['xfree'] = x0w
        (out / 'base.json').write_text(json.dumps(base, indent=1))
        log.write(json.dumps(record(-1, 0, x0w, base)) + '\n')
        log.flush()
    xw = base.get('x')

    if a.batch:
        X = json.load(open(a.batch))
        with Pool(a.workers) as pool:
            res = pool.map(_eval, [(x, a.q, a.rounds, a.threads, xw, a.kb) for x in X], chunksize=1)
        for i, (x, r) in enumerate(zip(X, res)):
            log.write(json.dumps(record(-2, i, x, r)) + '\n')
            r['xfree'] = list(map(float, x))
            (out / ('batch_%d.json' % i)).write_text(json.dumps(r, indent=1))
        log.flush()
        return

    import cma
    best = json.load(open(out / 'best.json')) if (out / 'best.json').exists() else dict(base)
    if a.resume and (out / 'es.pkl').exists():
        es, gen0 = pickle.load(open(out / 'es.pkl', 'rb'))
    else:
        es = cma.CMAEvolutionStrategy(x0w, a.sigma, {'popsize': a.popsize, 'seed': a.seed,
                                                     'verbose': -9})
        gen0 = 0
    gen = gen0
    with Pool(a.workers) as pool:
        while time.time() < t_end and not es.stop():
            X = es.ask()
            res = pool.map(_eval, [(x, a.q, a.rounds, a.threads, xw, a.kb) for x in X], chunksize=1)
            f = [r['achieved'] for r in res]
            es.tell(X, [-v for v in f])
            for i, (x, r) in enumerate(zip(X, res)):
                log.write(json.dumps(record(gen, i, x, r)) + '\n')
            i = int(np.argmax(f))
            if f[i] > best['achieved']:
                best = dict(res[i], xfree=list(map(float, X[i])), gen=gen)
                (out / 'best.json').write_text(json.dumps(best, indent=1))
            log.write(json.dumps(dict(gen=gen, gen_best=f[i], best=best['achieved'],
                                      nfail=sum(v < 0 for v in f), sigma=float(es.sigma),
                                      t=time.time())) + '\n')
            log.flush()
            gen += 1
            pickle.dump((es, gen), open(out / 'es.pkl', 'wb'))


if __name__ == '__main__':
    main()
