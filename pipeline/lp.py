"""The Kelley cutting-plane model of eps, and the level step that moves on it.

The weight problem is

    max eps  s.t.  eps <= F(g; a, b) for every g >= 0,
                   sum_r b_r = B0,  blo <= b_r <= B0,
                   sum_{j-i=s} a_ij = 2,  0 <= a_ij <= 2,
                   a and b palindromic.

Each local minimizer g found by the inner search contributes one cut row
[g, W(pair distances)], so the model max is an upper bound on eps over the
polytope at any round count, valid for every (a, b).
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import linprog


def sym_rows(G):
    """Equality rows pinning x to the reversal-invariant subspace."""
    q, NV = G.q, G.NV
    rows = []
    for k in range(G.NP):
        if G.SIG[k] > k:
            r = np.zeros(NV)
            r[q + k] = 1.0
            r[q + G.SIG[k]] = -1.0
            rows.append(r)
    for r_ in range(q // 2):
        r = np.zeros(NV)
        r[r_] = 1.0
        r[q - 1 - r_] = -1.0
        rows.append(r)
    return np.array(rows) if rows else np.zeros((0, NV))


def cut_row(g, tab, G):
    """The cut a local minimizer contributes: F(g) = row @ [b, a]."""
    g = np.asarray(g, float)
    return np.concatenate([g, tab.W(g @ G.U.T)])


def polytope(B0, blo_frac, G, symmetric=True):
    """-> (Aeq, beq, bounds, blo) for the weight polytope at this B0."""
    q, NV = G.q, G.NV
    blo = blo_frac * B0 / q
    Aeq = np.zeros((1 + q, NV))
    Aeq[0, :q] = 1.0
    Aeq[1:, q:] = G.CAP
    beq = np.concatenate([[B0], np.full(q, 2.0)])
    if symmetric:
        R = sym_rows(G)
        if len(R):
            Aeq = np.vstack([Aeq, R])
            beq = np.concatenate([beq, np.zeros(len(R))])
    bnds = [(blo, B0)] * q + [(0.0, 2.0)] * G.NP
    return Aeq, beq, bnds, blo


def model_max(rows, Aeq, beq, bnds, NV):
    """-> (model max, its argmax), or (None, None) when the LP fails.

    HiGHS runs at 1e-10 feasibility: its default 1e-7 leaves the ceiling about
    2e-8 loose in bound units, the scale at which it is compared to the
    achieved value.
    """
    n = len(rows)
    c = np.zeros(NV + 1)
    c[-1] = -1.0
    Aub = np.zeros((n, NV + 1))
    Aub[:, :NV] = -rows
    Aub[:, -1] = 1.0
    A2 = np.zeros((Aeq.shape[0], NV + 1))
    A2[:, :NV] = Aeq
    r = linprog(c, A_ub=Aub, b_ub=np.zeros(n), A_eq=A2, b_eq=beq,
                bounds=list(bnds) + [(None, None)], method="highs",
                options={"primal_feasibility_tolerance": 1e-10,
                         "dual_feasibility_tolerance": 1e-10})
    if not r.success:
        return None, None
    return r.x[-1], r.x[:NV]


def level_step(rows, lev, xc, Aeq, beq, bnds, NV):
    """The nearest point in L1 to xc whose model value reaches `lev`."""
    n = len(rows)
    c = np.concatenate([np.zeros(NV), np.ones(NV)])
    Aub = np.zeros((n + 2 * NV, 2 * NV))
    bub = np.zeros(n + 2 * NV)
    Aub[:n, :NV] = -rows
    bub[:n] = -lev
    I = np.eye(NV)
    Aub[n:n + NV, :NV] = I
    Aub[n:n + NV, NV:] = -I
    bub[n:n + NV] = xc
    Aub[n + NV:, :NV] = -I
    Aub[n + NV:, NV:] = -I
    bub[n + NV:] = -xc
    A2 = np.zeros((Aeq.shape[0], 2 * NV))
    A2[:, :NV] = Aeq
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=A2, b_eq=beq,
                bounds=list(bnds) + [(0, None)] * NV, method="highs")
    if not r.success:
        return None
    return r.x[:NV]
