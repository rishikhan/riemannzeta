#!/usr/bin/env python3
"""Window and weight search for the separated assembly (H - B) / (1 - eps).

    .venv/bin/python src/sep_window_search.py score --cert results/X.json
    .venv/bin/python src/sep_window_search.py cma --cert results/X.json --out DIR

The envelope pipeline fixes the pressure budget B = sum b_r at B0 and maximizes
eps.  Under the separated assembly B is free, so the weight problem is

    max (H - sum b) / (1 - eps)  s.t.  eps <= F(g; a, b) at every cut g,
                                       sum_{j-i=s} a_ij = 2, a, b palindromic,

solved by Dinkelbach steps on the Kelley cut model: at ratio kappa, maximize the
linear objective kappa eps - sum b, then reset kappa to the new ratio.

Float throughout: `achieved` uses the float gmin, an optimistic upper bound on
min F, and is not a certificate.  `ceiling` is the cut-model maximum of the
ratio, a valid upper bound over the weight polytope, good for rejection only.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np                                             # noqa: E402
from scipy.optimize import linprog                             # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from pipeline.cppgmin import CppGmin, cpp_table                # noqa: E402
from pipeline.geometry import geom                             # noqa: E402
from pipeline.kernel import hwin                               # noqa: E402
from pipeline.lp import cut_row, sym_rows                      # noqa: E402
from pipeline.objective import fbatch, template_starts         # noqa: E402
from pipeline.score import vmin_ratio, omegas                  # noqa: E402

W0 = math.sqrt(2.0)
BMIN = 2e-5          # per-gap pressure floor; the verifier needs b_r > 0
BMAX = 0.02
# Pairs pinned to zero weight.  The leaderboard's nine-point checker has no term
# slot for (0, 2) or (6, 8), so a certificate for it must leave them at zero.
ZERO_PAIRS = set()
# The checker's far-region cover needs eps * SC <= b_r * SMAX_r with SMAX_r <= 2^20 - 1
# and SC = 32768, binding at the end gaps.  None disables the row.
HS_RATIO = None
HS_GAPS = (0,)


def sep_polytope(G):
    q, NV = G.q, G.NV
    Aeq = np.zeros((q, NV))
    Aeq[:, q:] = G.CAP
    beq = np.full(q, 2.0)
    R = sym_rows(G)
    if len(R):
        Aeq = np.vstack([Aeq, R])
        beq = np.concatenate([beq, np.zeros(len(R))])
    bnds = [(BMIN, BMAX)] * G.q + [(0.0, 2.0)] * G.NP
    for p, pair in enumerate(G.PAIRS):
        if pair in ZERO_PAIRS:
            bnds[G.q + p] = (0.0, 0.0)
    return Aeq, beq, bnds


def lp_kappa(rows, kappa, Aeq, beq, bnds, NV, q):
    """max kappa*eps - sum b over the cut model -> (eps, x) or (None, None)."""
    n = len(rows)
    c = np.zeros(NV + 1)
    c[:q] = 1.0
    c[-1] = -kappa
    Aub = np.zeros((n, NV + 1))
    Aub[:, :NV] = -rows
    Aub[:, -1] = 1.0
    if HS_RATIO is not None:
        extra = np.zeros((2 * len(HS_GAPS), NV + 1))
        for k, r_ in enumerate(HS_GAPS):
            for m, gap in enumerate((r_, q - 1 - r_)):
                extra[2 * k + m, gap] = -1.0
                extra[2 * k + m, -1] = HS_RATIO
        Aub = np.vstack([Aub, extra])
    A2 = np.zeros((Aeq.shape[0], NV + 1))
    A2[:, :NV] = Aeq
    r = linprog(c, A_ub=Aub, b_ub=np.zeros(len(Aub)), A_eq=A2, b_eq=beq,
                bounds=list(bnds) + [(None, 1.0 / 64)], method="highs",
                options={"primal_feasibility_tolerance": 1e-10,
                         "dual_feasibility_tolerance": 1e-10})
    if not r.success:
        return None, None
    return r.x[-1], r.x[:NV]


def model_ratio(rows, H, Aeq, beq, bnds, NV, q, kappa0, steps=8):
    """Dinkelbach on the cut model -> (ratio, x)."""
    kappa, x = kappa0, None
    for _ in range(steps):
        e, xx = lp_kappa(rows, kappa, Aeq, beq, bnds, NV, q)
        if e is None:
            break
        x = xx
        new = (H - xx[:q].sum()) / (1 - e)
        if abs(new - kappa) < 1e-13:
            kappa = new
            break
        kappa = new
    return kappa, x


def _distinct(F, g, nkeep=24):
    """The nkeep lowest distinct minimizers, as CppGmin.gmin selects them."""
    ok = np.isfinite(F)
    F, g = F[ok], g[ok]
    keep, kf = [], []
    for idx in np.argsort(F):
        gi = g[idx]
        if any(np.max(np.abs(gi - k)) < 2e-3 for k in keep):
            continue
        keep.append(gi)
        kf.append(F[idx])
        if len(keep) >= nkeep:
            break
    return float(kf[0]), np.array(keep)


_HALF = {}


def half_templates(q):
    """The template starts with g <= rev(g) lexicographically.

    The LP keeps a and b palindromic, so F(rev g) = F(g) and Newton from rev(g)
    retraces the mirror image of the path from g.  Dropping one of each mirror
    pair halves stage 1 and leaves min F and the minimizer set (up to reversal)
    unchanged.
    """
    if q not in _HALF:
        T = template_starts(q)
        keep = np.array([tuple(r) <= tuple(r[::-1]) for r in T])
        _HALF[q] = np.ascontiguousarray(T[keep])
    return _HALF[q]


def warm_starts(pool, rng, q, b, n_jit=8, sd=0.03, n_rand=300):
    """Starts for a warm round: earlier minimizers, jittered copies, a few randoms."""
    P = np.asarray(pool, float)
    J = np.repeat(P[-24:], n_jit, axis=0)
    J = np.maximum(J + rng.normal(0.0, sd, J.shape) * np.maximum(J, 0.5), 0.0)
    hi = min(1.5 * (0.02 / max(float(np.min(b)), 1e-12)), 8.0)
    R = rng.uniform(0.05, hi, (n_rand, q))
    return np.vstack([P, J, R])


def sep_score(c, om, q, rounds=40, threads=1, seed=0, x0=None, n_rand=1200,
              warm=False, full_every=8, prescreen=5000):
    """-> dict(achieved, ceiling, H, B, eps, x, vmin) for one window.

    With warm=True only rounds 0, full_every, 2*full_every, ... and the last run
    the full template search; the rounds between start Newton from earlier
    minimizers, jittered copies and a few random points, about 50 times cheaper.
    Warm rounds still add cuts, so the ceiling stays a valid upper bound, but
    `achieved` is taken from full rounds only, so it is as honest as without warm.
    Warm rounds also restart from the `prescreen` half-templates with the lowest F
    at the current weights.  Full rounds use the mirror-reduced template set
    (half_templates), which is exact for palindromic weights.
    """
    c = np.asarray(c, float)
    vmin = vmin_ratio(c, om)
    if vmin <= 0.0:
        return dict(achieved=-1.0, ceiling=-1.0, H=0.0, vmin=vmin)
    H = hwin(c, om)
    tab = cpp_table(c, om, threads=threads)
    G = geom(q)
    Aeq, beq, bnds = sep_polytope(G)
    if x0 is None:
        a0 = np.zeros(G.NP)
        for p, (i, j) in enumerate(G.PAIRS):
            a0[p] = 2.0 / (q + 1 - (j - i))
        x = np.concatenate([np.full(q, 0.0045 / q), a0])
    else:
        x = np.asarray(x0, float)
    rows, best, upper, kappa = [], None, np.inf, 0.6735
    pool = []
    rng = np.random.default_rng(seed + 7919)
    light = (CppGmin(tab, q, threads=threads, iters2=70, templates=np.full((1, q), 2.0))
             if warm else None)
    HT = half_templates(q)
    with CppGmin(tab, q, threads=threads, iters2=70, templates=HT) as core:
        for it in range(rounds):
            full = (not warm) or it % full_every == 0 or it == rounds - 1
            if full:
                f, _, cuts = core.gmin(x[q:], x[:q], seed=seed + it, n_rand=n_rand, nkeep=24)
            else:
                st = warm_starts(pool, rng, q, x[:q])
                if prescreen:
                    F0 = fbatch(HT, x[q:], x[:q], tab, G)
                    st = np.vstack([st, HT[np.argpartition(F0, prescreen)[:prescreen]]])
                Fw, gw = light.newton(x[q:], x[:q], st)
                f, cuts = _distinct(Fw, gw)
            pool = (pool + list(cuts))[-200:]
            for g in cuts:
                rows.append(cut_row(g, tab, G))
            ach = (H - x[:q].sum()) / (1 - f)
            if full and (best is None or ach > best["achieved"]):
                best = dict(achieved=float(ach), H=float(H), B=float(x[:q].sum()),
                            eps=float(f), x=x.tolist())
            kappa, xlp = model_ratio(np.array(rows), H, Aeq, beq, bnds, G.NV, q,
                                     max(kappa, best["achieved"]))
            if xlp is None:
                break
            upper = min(upper, kappa)
            x = xlp
    if light is not None:
        light.close()
    best.update(ceiling=float(upper), vmin=float(vmin))
    return best


def window_of(cert):
    w = cert["window"]
    c = np.array(w["numerators"], float) / w["denominator"]
    return c, omegas(len(c) - 1, W0)


def _cma_eval(args):
    xfree, J, q, rounds, seed, zp, hs, warm, fe = args
    global HS_RATIO
    ZERO_PAIRS.clear()
    ZERO_PAIRS.update(zp)
    HS_RATIO = hs
    c = np.r_[1.0, xfree]
    r = sep_score(c, omegas(J, W0), q, rounds=rounds, seed=seed, warm=warm, full_every=fe)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["score", "cma"])
    ap.add_argument("--cert", required=True)
    ap.add_argument("--q", type=int, default=None)
    ap.add_argument("--J", type=int, default=16, help="harmonics in the searched window")
    ap.add_argument("--rounds", type=int, default=40)
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--sigma", type=float, default=5e-4)
    ap.add_argument("--popsize", type=int, default=16)
    ap.add_argument("--gens", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1701)
    ap.add_argument("--out", default=None)
    ap.add_argument("--zero-pairs", default="",
                    help="pairs pinned to zero weight, e.g. 0-2,6-8")
    ap.add_argument("--warm", action="store_true",
                    help="warm-started rounds between full template rounds (see sep_score)")
    ap.add_argument("--full-every", type=int, default=8,
                    help="with --warm, run the exact template search every this many rounds")
    ap.add_argument("--start", default=None,
                    help="best.json of an earlier search; its xfree is the CMA mean")
    ap.add_argument("--hs", action="store_true",
                    help="add the checker's end-gap pressure floor b_0 = b_7 >= eps/32")
    a = ap.parse_args()
    zp = {tuple(int(t) for t in s.split("-")) for s in a.zero_pairs.split(",") if s}
    ZERO_PAIRS.update(zp)
    global HS_RATIO
    hs = 32768 / 1048575 if a.hs else None
    HS_RATIO = hs
    cert = json.load(open(a.cert))
    q = a.q or int(cert["q"])
    c, om = window_of(cert)

    if a.mode == "score":
        t0 = time.time()
        r = sep_score(c, om, q, rounds=a.rounds, threads=a.threads, warm=a.warm,
                      full_every=a.full_every)
        r.pop("x")
        r["secs"] = round(time.time() - t0, 1)
        print(json.dumps(r))
        return

    import cma
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    x0 = np.zeros(a.J)
    k = min(a.J, len(c) - 1)
    x0[:k] = c[1:k + 1]
    if a.start:
        xs = json.load(open(a.start))["xfree"]
        x0 = np.zeros(a.J)
        x0[:min(a.J, len(xs))] = xs[:a.J]
    base = _cma_eval((x0, a.J, q, a.rounds, 0, zp, hs, a.warm, a.full_every))
    best = dict(base, xfree=x0.tolist())
    log = open(out / "log.jsonl", "a")
    log.write(json.dumps({"gen": -1, "achieved": base["achieved"], "H": base["H"],
                          "B": base.get("B"), "eps": base.get("eps")}) + "\n")
    log.flush()
    es = cma.CMAEvolutionStrategy(x0, a.sigma, {"popsize": a.popsize, "seed": a.seed,
                                                 "verbose": -9})
    with Pool(a.workers) as pool:
        for gen in range(a.gens):
            X = es.ask()
            res = pool.map(_cma_eval, [(np.asarray(x), a.J, q, a.rounds, gen, zp, hs, a.warm, a.full_every) for x in X])
            es.tell(X, [-r["achieved"] for r in res])
            i = int(np.argmax([r["achieved"] for r in res]))
            if res[i]["achieved"] > best["achieved"]:
                best = dict(res[i], xfree=list(map(float, X[i])))
                (out / "best.json").write_text(json.dumps(best, indent=1))
            log.write(json.dumps({"gen": gen, "gen_best": res[i]["achieved"],
                                  "best": best["achieved"], "H": best["H"],
                                  "B": best.get("B"), "eps": best.get("eps")}) + "\n")
            log.flush()
    (out / "best.json").write_text(json.dumps(best, indent=1))


if __name__ == "__main__":
    main()
