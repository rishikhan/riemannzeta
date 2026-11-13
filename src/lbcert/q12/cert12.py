#!/usr/bin/env python3
"""q = 12 certificate in leaderboard form at the record window.

    python cert12.py convert OUT.json [--threads 8]
    python cert12.py refit OUT.json [--threads 8] [--rounds 24] [--kb 1048576|0] [--q 12]

convert: the certificate of record's window and weights (pipeline.certref.cert_of_record), float
min F at those weights (CppGmin, full template search), H = hwin.  refit: the same window, weights
re-solved for the separated assembly (sep_window_search.sep_score, warm rounds), optionally with the
checker's end-gap floor b_0 = b_{Q-1} >= eps * 32768 / (KB - 1).  The template search and the
prescreen run streaming in C++ (gmin12/), so memory stays at the table plus O(threads x keep).  Both write a window JSON in the
best_q9_j16 format (xfree, x, eps, H, B, achieved) that q9win/build9.py reads.

gmin12_cpp copy: q12/cert12.py with the cut-model LP (sep_window_search.model_ratio) run inside the
streaming core (gmin12_cpp/lp.inc, HiGHS C++ API) instead of scipy.  Q12_LP selects it:
cold (default; scipy's model and options, a fresh solve per LP), warm (one HiGHS model kept across
rounds, cuts appended), scipy (the original Python path).
"""
import argparse
import json
import os
import sys
import time
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
ROOT = next(p for p in _HERE.parents if (p / 'pipeline').is_dir())
_LPDIR = _HERE if _HERE.name == 'gmin12_cpp' else _HERE / 'gmin12_cpp'
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'src'))
from pipeline.certref import cert_of_record          # noqa: E402
from pipeline.cppgmin import CppGmin, cpp_table      # noqa: E402
from pipeline.geometry import geom                   # noqa: E402
from pipeline.kernel import hwin                     # noqa: E402
import sep_window_search as S                        # noqa: E402
sys.path.insert(0, str(_LPDIR))
from stream import StreamGmin                        # noqa: E402
from pipeline.lp import cut_row                      # noqa: E402


def cert_x(cert, q):
    G = geom(q)
    pw = cert['pair_weights']
    A = {(i, j): v / pw['denominator'] for i, j, v in pw['entries']}
    pp = cert['position_pressure']
    b = [v / pp['denominator'] for v in pp['numerators']]
    return np.array(b + [A[p] for p in G.PAIRS])


def sep_score_stream(c, om, q, rounds=24, threads=1, seed=0, x0=None, n_rand=1200,
                     full_every=8, prescreen=5000):
    """sep_window_search.sep_score(warm=True) with the template search and the prescreen in the
    streaming C++ core (gmin12/gmin_stream.cpp): no template array is ever built in Python."""
    c = np.asarray(c, float)
    vmin = S.vmin_ratio(c, om)
    H = hwin(c, om)
    tab = cpp_table(c, om, threads=threads)
    G = geom(q)
    Aeq, beq, bnds = S.sep_polytope(G)
    if x0 is None:
        a0 = np.zeros(G.NP)
        for p, (i, j) in enumerate(G.PAIRS):
            a0[p] = 2.0 / (q + 1 - (j - i))
        x = np.concatenate([np.full(q, 0.0045 / q), a0])
    else:
        x = np.asarray(x0, float)
    lp_mode = os.environ.get('Q12_LP', 'cold')
    assert lp_mode in ('cold', 'warm', 'scipy'), lp_mode
    rows, best, upper, kappa, pool = [], None, np.inf, 0.6735, []
    rng = np.random.default_rng(seed + 7919)
    light = CppGmin(tab, q, threads=threads, iters2=70, templates=np.full((1, q), 2.0))
    with StreamGmin(tab, q, threads=threads, iters2=70) as core:
        if lp_mode != 'scipy':
            core.lp_init(Aeq, beq, bnds, S.HS_RATIO, S.HS_GAPS, mode=1 if lp_mode == 'warm' else 0)
        for it in range(rounds):
            full = it % full_every == 0 or it == rounds - 1
            if full:
                f, _, cuts = core.gmin(x[q:], x[:q], seed=seed + it, n_rand=n_rand, nkeep=24)
            else:
                st = S.warm_starts(pool, rng, q, x[:q])
                if prescreen:
                    st = np.vstack([st, core.prescreen(x[q:], x[:q], prescreen)[1]])
                Fw, gw = light.newton(x[q:], x[:q], st)
                f, cuts = S._distinct(Fw, gw)
            pool = (pool + list(cuts))[-200:]
            new_rows = [cut_row(g, tab, G) for g in cuts]
            ach = (H - x[:q].sum()) / (1 - f)
            if full and (best is None or ach > best['achieved']):
                best = dict(achieved=float(ach), H=float(H), B=float(x[:q].sum()), eps=float(f), x=x.tolist())
            if lp_mode == 'scipy':
                rows += new_rows
                kappa, xlp = S.model_ratio(np.array(rows), H, Aeq, beq, bnds, G.NV, q, max(kappa, best['achieved']))
            else:
                kappa, xlp = core.lp_ratio(new_rows, H, max(kappa, best['achieved']))
            if xlp is None:
                break
            upper = min(upper, kappa)
            x = xlp
            print('round', it, 'full' if full else 'warm', 'achieved', ach, 'ceiling', upper, flush=True)
        if lp_mode != 'scipy':
            print('lp', core.lp_stats(), flush=True)
    light.close()
    best.update(ceiling=float(upper), vmin=float(vmin))
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['convert', 'refit'])
    ap.add_argument('out')
    ap.add_argument('--threads', type=int, default=8)
    ap.add_argument('--rounds', type=int, default=24)
    ap.add_argument('--full-every', type=int, default=8)
    ap.add_argument('--kb', type=int, default=0, help='end-gap floor for this KB (0: none)')
    ap.add_argument('--q', type=int, default=12)
    a = ap.parse_args()
    path = cert_of_record(str(ROOT))
    cert = json.load(open(ROOT / path))
    c, om = S.window_of(cert)
    q = a.q
    H = float(hwin(c, om))
    t0 = time.time()
    if a.mode == 'convert':
        assert q == int(cert['q'])
        x = cert_x(cert, q)
        tab = cpp_table(c, om, threads=a.threads)
        with StreamGmin(tab, q, threads=a.threads, iters2=70) as core:
            f, g, _ = core.gmin(x[q:], x[:q], seed=0, n_rand=6000, nkeep=24)
        B = float(x[:q].sum())
        r = dict(achieved=(H - B) / (1 - f), H=H, B=B, eps=float(f), x=x.tolist(), argmin=list(map(float, g)))
    else:
        if a.kb:
            S.HS_RATIO = 32768 / (a.kb - 1)
        x0 = cert_x(cert, q) if q == int(cert['q']) else None
        r = sep_score_stream(c, om, q, rounds=a.rounds, threads=a.threads, x0=x0,
                             full_every=a.full_every)
    r.update(xfree=list(map(float, c[1:])), cert=path, q=q, kb_floor=a.kb, secs=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(r, indent=1))
    print(json.dumps({k: v for k, v in r.items() if k not in ('x', 'xfree')}))


if __name__ == '__main__':
    main()
