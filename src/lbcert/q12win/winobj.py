#!/usr/bin/env python3
"""Window objective for the q = 12 re-optimization: f(xfree) = float kappa after a full refit.

    python winobj.py eval --q 10 [--window W.json] [--rounds 64] [--threads 6] [--out R.json]

The window is v(s) = cos(sqrt 2 s) + sum_{j=1}^{J} c_j cos(2 pi j s) with xfree = (c_1 .. c_J),
quantized to numerators over 10^9 as the Lean base reads them.  f runs, in order:

  1. side conditions (cheap; a failure returns achieved = -1 and the failing names):
     vmin > 0; the separated-assembly conditions of src/sep_conditions_cert.py in float on a
     grid (W1 majorant at d = 17/20, gamma = 7/10; W2 close-pair kernel k(t)/k(0) >= 1/8 on
     [0, 17/20]); for J = 16 the exact Lean window conditions of w16/regen_window.compute with
     pvCheck at 256 cells (profile budgets, core, correction, normalized profile margins).
  2. the separated-assembly refit of q12/cert12.sep_score_stream (streaming C++ template search)
     with the checker's end-gap floor for KB = 2^22, optionally warm-started at weights x0.

Returned fields: achieved (float kappa, the CMA objective), ceiling, H, B, eps, x, margins, and
kappa_lb = (H_W floor - B) / (1 - (eps - 6e-7)), the leaderboard-form value that the converted
certificate would give (c = eps_float - 6e-7).
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse                                        # noqa: E402
import contextlib
import io
import json
import math
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(HERE.parent / 'q12'))
sys.path.insert(0, str(HERE.parent / 'w16'))
import sep_window_search as S                          # noqa: E402
import cert12                                          # noqa: E402
from pipeline.score import omegas                      # noqa: E402

KB = 4194304
W0 = math.sqrt(2.0)
E9 = 10 ** 9
D, GAMMA = 0.85, 0.7
OFFSET = 6e-7                       # c = eps_float - 6e-7 (leaderboard form)


def numerators(xfree):
    return [E9] + [int(round(x * E9)) for x in xfree]


def sep_margins(c, om, n=20001):
    """Float W1 / W2 margins of sep_conditions_cert.py on uniform grids (min over the grid)."""
    c = np.asarray(c, float)
    k0 = float(np.sum(c * np.sinc(om / 2 / np.pi)))           # int v = sum c sin(w/2)/(w/2)
    s = np.linspace(0.0, 0.5, n)
    v = np.cos(np.outer(s, om)) @ c
    maj = (np.sinc(D * (s - 0.5)) + np.sinc(D * (s + 0.5))) ** 2
    w1 = float(np.min(GAMMA * maj - v / k0))
    t = np.linspace(0.0, D, n)
    # k(t) = sum c (sinc(w/2 - pi t) + sinc(w/2 + pi t)) / 2, sinc unnormalized
    a = (om[None, :] / 2 - np.pi * t[:, None]) / np.pi
    b = (om[None, :] / 2 + np.pi * t[:, None]) / np.pi
    k = (np.sinc(a) + np.sinc(b)) @ c / 2
    w2 = float(np.min(k / k0) - 0.125)
    return w1, w2


def lean_conditions(cnum):
    """Exact Lean window conditions (regen_window.compute, pvCheck at 256 cells); J = 16 only."""
    import regen_window as R
    K, checks = R.compute(cnum, [256])
    marg = dict(pv_value=float(K['pv_value']), rho=str(K['rho']), r0=str(K['r0']),
                budget_sq=float(1 - K['r0'] ** 2 - 4 * K['rho']), S=K['S'] / E9, v0=K['v0'] / E9,
                core=float(K['core']), corr=float(K['corr']), margin_core=float(K['margin_core']),
                margin_edge=float(K['margin_edge']), d2lit=K['d2lit'], hw=K['hw'])
    return [k for k, v in checks.items() if not v], marg


def conditions(xfree):
    J = len(xfree)
    cnum = numerators(xfree)
    c = np.array(cnum, float) / E9
    om = omegas(J, W0)
    m = dict(vmin=float(S.vmin_ratio(c, om)))
    m['w1'], m['w2'] = sep_margins(c, om)
    fail = [k for k in ('vmin', 'w1', 'w2') if m[k] <= 0]
    if J == 16:
        lf, lm = lean_conditions(cnum)
        fail += lf
        m.update(lm)
    return c, om, fail, m


def evaluate(xfree, q, rounds=64, threads=6, seed=0, x0=None, full_every=8, kb=KB):
    t0 = time.time()
    c, om, fail, m = conditions(xfree)
    if fail:
        return dict(achieved=-1.0, fail=fail, margins=m, secs=round(time.time() - t0, 1))
    S.HS_RATIO = 32768 / (kb - 1) if kb else None
    with contextlib.redirect_stdout(io.StringIO()):
        r = cert12.sep_score_stream(c, om, q, rounds=rounds, threads=threads, seed=seed,
                                    x0=x0, full_every=full_every)
    hw = m.get('hw')
    if hw is not None:
        r['kappa_lb'] = float((Fr(hw, 10 ** 40) - Fr(r['B'])) / (1 - Fr(r['eps']) + Fr(OFFSET)))
    r.update(margins=m, fail=[], secs=round(time.time() - t0, 1))
    return r


def load_xfree(path):
    d = json.load(open(path))
    if 'xfree' in d:
        return list(d['xfree'])
    w = d['window']
    return [n / w['denominator'] for n in w['numerators'][1:]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['eval', 'cond'])
    ap.add_argument('--window', default=str(ROOT / 'src/lbcert/q12win/work/final2_q12.json'))
    ap.add_argument('--q', type=int, default=12)
    ap.add_argument('--J', type=int, default=None, help='pad the window with zero harmonics to J')
    ap.add_argument('--rounds', type=int, default=64)
    ap.add_argument('--threads', type=int, default=6)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    xf = load_xfree(a.window)
    if a.J:
        xf = (xf + [0.0] * a.J)[:a.J]
    if a.mode == 'cond':
        _, _, fail, m = conditions(xf)
        print(json.dumps(dict(fail=fail, margins=m), indent=1))
        return
    r = evaluate(xf, a.q, rounds=a.rounds, threads=a.threads)
    r['xfree'] = xf
    r['q'] = a.q
    if a.out:
        Path(a.out).write_text(json.dumps(r, indent=1))
    print(json.dumps({k: v for k, v in r.items() if k not in ('x', 'xfree')}))


if __name__ == '__main__':
    main()
