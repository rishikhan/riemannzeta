"""Score one candidate window: solve its weights cold, assemble its bound.

This is the CMA objective.  Each candidate gets a fresh table, a fresh core and
a COLD Kelley bundle, so no information passes between candidates.

Direction of error.  `achieved` comes from the float gmin, an UPPER bound on
the true local minimum, so it is optimistic and is not a certificate.
`ceiling` comes from the Kelley LP model max, a genuine upper bound on eps over
the polytope at any round count, so it is good for REJECTION only.  Rank
windows by `achieved`: at few rounds the ceiling is loose in a way that favors
windows whose bundle has not converged, and ranking on it inverts the order.
"""
from __future__ import annotations

import numpy as np
from scipy import optimize

from pipeline.assembly import final_bound
from pipeline.cppgmin import CppGmin, cpp_table
from pipeline.geometry import geom
from pipeline.kernel import hwin
from pipeline.lp import cut_row, model_max, polytope

# The inner multistart, in one place: the paper reports these three and
# reads them from here, so they cannot drift from what the search ran.
GMIN = dict(n_rand=1200, iters=70, nkeep=24)


def omegas(J, w0):
    """The carrier plus J harmonics, as a float frequency vector."""
    return np.array([w0] + [2 * j * np.pi for j in range(1, J + 1)])


def vmin_ratio(c, omega, ngrid=200001):
    """min_{|s|<=1/2} v(s) / v(0).  Positive means the window is admissible.

    v is even, so scan [0, 1/2] and polish the lowest grid cell.

    v(0) = sum(c) must itself be positive.  Dividing by a negative v(0) would
    turn a window that goes negative into a positive ratio, so such a window is
    rejected outright rather than scaled.
    """
    c = np.asarray(c, float)
    omega = np.asarray(omega, float)
    v0 = float(c.sum())
    if v0 <= 0.0:
        return -1.0
    s = np.linspace(0.0, 0.5, ngrid)
    v = np.cos(np.outer(s, omega)) @ c
    i = int(np.argmin(v))
    lo, hi = s[max(i - 1, 0)], s[min(i + 1, ngrid - 1)]
    r = optimize.minimize_scalar(lambda t: float(np.cos(t * omega) @ c),
                                 bounds=(lo, hi), method="bounded",
                                 options={"xatol": 1e-14})
    return min(float(r.fun), float(v[i])) / v0


def score_bundle(tab, core, B0, rounds, q, seed=0, blo_frac=0.30):
    """The plain Kelley loop: cut, take the model max, move to its argmax.

    -> (best achieved eps, the model max, the cut rows).
    """
    G = geom(q)
    Aeq, beq, bnds, _ = polytope(B0, blo_frac, G, symmetric=True)
    a0 = np.zeros(G.NP)
    for p, (i, j) in enumerate(G.PAIRS):
        a0[p] = 2.0 / (q + 1 - (j - i))
    x = np.concatenate([np.full(q, B0 / q), a0])
    rows, best, upper = [], -np.inf, np.inf
    for it in range(rounds):
        f, _, cuts = core.gmin(x[q:], x[:q], seed=seed + it,
                               n_rand=GMIN["n_rand"], nkeep=GMIN["nkeep"])
        for g in cuts:
            rows.append(cut_row(g, tab, G))
        best = max(best, f)
        U_, xlp = model_max(np.array(rows), Aeq, beq, bnds, G.NV)
        if U_ is None:
            break
        upper = min(upper, U_)
        x = xlp
    return best, upper, np.array(rows)


def score(x, J, w0, rounds, q, B0, blo_frac=0.30, threads=1):
    """-> (ceiling, achieved, H, vmin) for one window.

    `x` holds the free coefficients; the pinned carrier coefficient 1.0 is
    prepended here.  A window with vmin <= 0 is inadmissible and is rejected
    without a bundle.
    """
    c = np.r_[1.0, np.asarray(x, float)]
    om = omegas(J, w0)
    vmin = vmin_ratio(c, om)
    if vmin <= 0.0:                      # v must be non-negative on [-1/2, 1/2]
        return (-1.0, -1.0, 0.0, vmin)
    H = hwin(c, om)
    tab = cpp_table(c, om, threads=threads)
    with CppGmin(tab, q, threads=threads, iters2=GMIN["iters"]) as core:
        e, u, _ = score_bundle(tab, core, B0, rounds, q, blo_frac=blo_frac)
    achieved = final_bound(H, e, B0, q=q)[0]
    ceiling = final_bound(H, u, B0, q=q)[0] if np.isfinite(u) else -1.0
    return (ceiling, achieved, H, vmin)


def score_args(args):
    """(x, J, w0, rounds, q, B0, threads) -> score(...).  A pool entry point."""
    x, J, w0, rounds, q, B0, threads = args
    return score(x, J, w0, rounds, q, B0, threads=threads)
