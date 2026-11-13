#!/usr/bin/env python3
"""Global minimum of F - c for a q = 12 model (m12w validation).

    python fmin12.py table SPEC.json OUT.json [--starts 800] [--far 1048576] [--workers 8]
    python fmin12.py true  SPEC.json WINDOW.json MINIMA.json OUT.json [--top 40] [--dps 34]

table: the model's F with its quantised weights (BS, AW, cN over SA from spec.json), the window of
spec.json (numerators over 1e9, omegas (sqrt 2, 2 pi j)), and the checker's far rule: a pair whose
distance E (units of 1/32768) is >= FAR counts 0.  L-BFGS-B (g >= 0) from near-lattice starts (every gap pattern in
{1.04, 1.975}^12, and patterns with one to three gaps at 2.92) and random starts; distinct local minima are written.

true: every pair counts (no far rule).  Each of the best `top` table minima is refined in float without
the far rule, then by Newton steps in mpmath at `dps` digits, for two weight sets: the refit's float
weights x with its eps (WINDOW.json), and the model's quantised weights with c = cN / SA.
"""
import argparse
import json
import math
import os
import sys
from multiprocessing import Pool

import numpy as np
from scipy.optimize import minimize

Q = 12
SA = 2 ** 23 * 10 ** 24
SC = 32768
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
U = np.zeros((len(PAIRS), Q))
for _p, (_i, _j) in enumerate(PAIRS):
    U[_p, _i:_j] = 1.0


def window(spec):
    c = np.array(spec['window'], float) / 1e9
    om = np.array([math.sqrt(2.0)] + [2 * j * math.pi for j in range(1, len(c))])
    return c, om


def sinc3(z):
    small = np.abs(z) < 1e-3
    zs = np.where(small, 1.0, z)
    s, co = np.sin(zs), np.cos(zs)
    v = s / zs
    d1 = (zs * co - s) / zs ** 2
    d2 = ((2.0 - zs ** 2) * s - 2.0 * zs * co) / zs ** 3
    t = np.where(small, z, 0.0)
    t2 = t * t
    v = np.where(small, 1 - t2 / 6 + t2 * t2 / 120, v)
    d1 = np.where(small, -t / 3 + t * t2 / 30, d1)
    d2 = np.where(small, -1 / 3 + t2 / 10, d2)
    return v, d1, d2


class Fn:
    def __init__(self, c, om, b, a, cc, far=None):
        self.c, self.h, self.b, self.a, self.cc, self.far = c, om / 2, np.asarray(b), np.asarray(a), cc, far
        self.k0 = self.k(np.zeros(1))[0][0]

    def k(self, x):
        px = np.pi * x[:, None]
        lv, ld, ldd = sinc3(self.h - px)
        rv, rd, rdd = sinc3(self.h + px)
        k = (self.c * (lv + rv) / 2).sum(-1)
        kp = (self.c * np.pi * (rd - ld) / 2).sum(-1)
        kpp = (self.c * np.pi ** 2 * (ldd + rdd) / 2).sum(-1)
        return k, kp, kpp

    def __call__(self, g):
        d = U @ g
        k, kp, _ = self.k(d)
        w = (k / self.k0) ** 2
        wp = 2 * k * kp / self.k0 ** 2
        a = self.a
        if self.far is not None:
            a = np.where(d * SC >= self.far, 0.0, a)
        f = self.b @ g + a @ w - self.cc
        gr = self.b + U.T @ (a * wp)
        return f, gr


def lattice_starts(rng, n):
    """every pattern in {1.04, 1.975}^12, then n patterns with one to three gaps at 2.92 (jitter 0.005)."""
    out = []
    for m in range(1 << Q):
        out.append(np.array([1.975 if m >> r & 1 else 1.04 for r in range(Q)]) + rng.normal(0, 0.005, Q))
    for _ in range(n):
        g = np.where(rng.random(Q) < 0.5, 1.975, 1.04)
        g[rng.choice(Q, rng.integers(1, 4), replace=False)] = 2.92
        out.append(g + rng.normal(0, 0.005, Q))
    return out


def random_starts(rng, n):
    return [rng.uniform(0.6, 3.4, Q) for _ in range(n)]


_F = None


def _init(args):
    global _F
    _F = Fn(*args)


def _run(g0):
    r = minimize(_F, g0, jac=True, method='L-BFGS-B', bounds=[(0, None)] * Q,
                 options=dict(maxiter=3000, ftol=1e-16, gtol=1e-11))
    return float(r.fun), r.x.tolist()


def distinct(res, tol=2e-4):
    res = sorted(res)
    out = []
    for f, g in res:
        if not any(np.max(np.abs(np.array(g) - np.array(h))) < tol for _, h in out):
            out.append((f, g))
    return out


def model_weights(spec):
    BS = [b / SA for b in spec['BS']]
    AW = {tuple(map(int, k.split(','))): v / SA for k, v in spec['AW'].items()}
    return np.array(BS), np.array([AW[p] for p in PAIRS]), spec['cN'] / SA


def table(a):
    spec = json.load(open(a.spec))
    c, om = window(spec)
    b, aw, cc = model_weights(spec)
    rng = np.random.default_rng(a.seed)
    starts = lattice_starts(rng, a.starts) + random_starts(rng, a.starts // 4)
    with Pool(a.workers, _init, ((c, om, b, aw, cc, a.far),)) as pool:
        res = pool.map(_run, starts, chunksize=4)
    out = distinct(res)
    print('starts', len(starts), 'distinct minima', len(out))
    for f, g in out[:15]:
        print('%.4e' % f, ' '.join('%.4f' % v for v in g), 'span %.3f' % sum(g))
    json.dump(dict(starts=len(starts), far=a.far, minima=out), open(a.out, 'w'))


def mp_newton(c, om, b, aw, cc, g, dps, iters=8):
    import mpmath as mp
    mp.mp.dps = dps
    cm = [mp.mpf(int(round(v * 1e9))) / 10 ** 9 for v in c]
    hm = [mp.sqrt(2) / 2] + [j * mp.pi for j in range(1, len(c))]
    bm = [mp.mpf(v) for v in b]
    am = [mp.mpf(v) for v in aw]
    ccm = mp.mpf(cc)

    def sinc_d(z):
        if abs(z) < mp.mpf('1e-8'):
            return 1 - z ** 2 / 6, -z / 3, mp.mpf(-1) / 3 + z ** 2 / 10
        s, co = mp.sin(z), mp.cos(z)
        return s / z, (z * co - s) / z ** 2, ((2 - z ** 2) * s - 2 * z * co) / z ** 3

    def ktrip(x):
        k = kp = kpp = mp.mpf(0)
        for cj, hj in zip(cm, hm):
            lv, ld, ldd = sinc_d(hj - mp.pi * x)
            rv, rd, rdd = sinc_d(hj + mp.pi * x)
            k += cj * (lv + rv) / 2
            kp += cj * mp.pi * (rd - ld) / 2
            kpp += cj * mp.pi ** 2 * (ldd + rdd) / 2
        return k, kp, kpp

    k0 = ktrip(mp.mpf(0))[0]
    gm = [mp.mpf(v) for v in g]

    def evalF(gm, need=True):
        f = -ccm + sum(bm[r] * gm[r] for r in range(Q))
        gr = list(bm)
        H = [[mp.mpf(0)] * Q for _ in range(Q)]
        for p, (i, j) in enumerate(PAIRS):
            if am[p] == 0:
                continue
            d = sum(gm[i:j])
            k, kp, kpp = ktrip(d)
            f += am[p] * (k / k0) ** 2
            if need:
                w1 = am[p] * 2 * k * kp / k0 ** 2
                w2 = am[p] * 2 * (kp ** 2 + k * kpp) / k0 ** 2
                for r in range(i, j):
                    gr[r] += w1
                    for s in range(i, j):
                        H[r][s] += w2
        return f, gr, H

    for _ in range(iters):
        f, gr, H = evalF(gm)
        step = mp.lu_solve(mp.matrix(H), mp.matrix(gr))
        gm = [gm[r] - step[r] for r in range(Q)]
        if max(abs(s) for s in step) < mp.mpf(10) ** (-dps + 6):
            break
    f, gr, H = evalF(gm)
    ev = min(mp.eig(mp.matrix(H))[0], key=lambda z: mp.re(z))
    return f, [float(v) for v in gm], float(max(abs(v) for v in gr)), float(mp.re(ev))


def true(a):
    spec = json.load(open(a.spec))
    W = json.load(open(a.window))
    c, om = window(spec)
    mins = json.load(open(a.minima))['minima'][:a.top]
    x = W['x']
    bf, af, ef = np.array(x[:Q]), np.array(x[Q:]), W['eps']
    bq, aq, cq = model_weights(spec)
    rows = []
    for tag, b, aw, cc in (('refit', bf, af, ef), ('model', bq, aq, cq)):
        F = Fn(c, om, b, aw, cc)
        best = None
        for ftab, g in mins:
            r = minimize(F, np.array(g), jac=True, method='L-BFGS-B', bounds=[(0, None)] * Q,
                         options=dict(maxiter=3000, ftol=1e-16, gtol=1e-12))
            f, gm, gn, ev = mp_newton(c, om, b, aw, cc, r.x, a.dps)
            rows.append(dict(w=tag, ftab=ftab, ffloat=float(r.fun), fmp=str(f), g=gm, gradmax=gn, hmin=ev))
            if best is None or f < best[0]:
                best = (f, gm, gn, ev)
        print(tag, 'min F - %s = %s (grad %.1e, min Hessian eig %.3e)' % (
            'eps' if tag == 'refit' else 'c', __import__('mpmath').nstr(best[0], 20), best[2], best[3]))
        print('   g', ' '.join('%.6f' % v for v in best[1]))
        if tag == 'refit':
            print('   F - c (c = eps - 6e-7):', float(best[0]) + 6e-7)
    json.dump(rows, open(a.out, 'w'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['table', 'true'])
    ap.add_argument('spec')
    ap.add_argument('rest', nargs='+')
    ap.add_argument('--starts', type=int, default=800)
    ap.add_argument('--far', type=int, default=1 << 20)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--top', type=int, default=40)
    ap.add_argument('--dps', type=int, default=34)
    a = ap.parse_args()
    if a.mode == 'table':
        a.out, = a.rest
        if a.far <= 0:
            a.far = None
        table(a)
    else:
        a.window, a.minima, a.out = a.rest
        true(a)


if __name__ == '__main__':
    main()
