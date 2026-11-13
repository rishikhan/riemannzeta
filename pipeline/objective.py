"""The local objective and the projected Newton that minimizes it.

    F(g) = sum_r b_r g_r + sum_{i<j} a_ij W(y_j - y_i),   g >= 0

Everything here is FLOAT.  A minimum found by descent is an UPPER bound on the
true infimum of F over the orthant, so it is an optimistic search value and
never a certificate.
"""
from __future__ import annotations

import numpy as np


def fbatch(g, a, b, tab, G):
    """F at a stack of gap vectors, through the spline table."""
    d = g @ G.U.T
    return g @ b + tab.W(d) @ a


def fexact(g, a, b, tab, G):
    """F at one gap vector, through the exact kernel."""
    g = np.asarray(g, float)
    d = g @ G.U.T
    return float(g @ b + tab.Wexact(d)[0] @ a)


def _fgh(g, a, b, tab, G):
    d = g @ G.U.T
    w, wp, wpp = tab.all3(d)
    F = g @ b + w @ a
    grad = (wp * a) @ G.U + b
    H = ((wpp * a) @ G.UU).reshape(-1, G.q, G.q)
    return F, grad, H


def newton_batch(g0, a, b, tab, G, iters=90, chunk=40000):
    """Projected damped Newton on F over g >= 0, run on a whole batch at once.

    Every row evolves independently, with its own damping and its own accept
    test, so splitting the block changes nothing but the memory held.
    """
    g0 = np.maximum(np.asarray(g0, float).copy(), 0.0)
    if len(g0) > chunk:
        Fs, gs = [], []
        for s in range(0, len(g0), chunk):
            f, gg = newton_batch(g0[s:s + chunk], a, b, tab, G, iters, chunk)
            Fs.append(f)
            gs.append(gg)
        return np.concatenate(Fs), np.concatenate(gs)
    g = g0
    n = len(g)
    mu = np.full(n, 1e-2)
    F = fbatch(g, a, b, tab, G)
    eye = np.eye(G.q)
    for _ in range(iters):
        Fc, grad, H = _fgh(g, a, b, tab, G)
        A = H + mu[:, None, None] * eye
        try:
            dx = np.linalg.solve(A, grad[..., None])[..., 0]
        except np.linalg.LinAlgError:
            A = H + (mu[:, None, None] + 1.0) * eye
            dx = np.linalg.solve(A, grad[..., None])[..., 0]
        gt = np.maximum(g - dx, 0.0)
        Ft = fbatch(gt, a, b, tab, G)
        acc = Ft < Fc - 1e-18
        g = np.where(acc[:, None], gt, g)
        F = np.where(acc, Ft, Fc)
        mu = np.where(acc, np.maximum(mu * 0.4, 1e-12), np.minimum(mu * 6.0, 1e8))
    return F, g


_TEMPLATES = {}


def template_starts(q, vals=((1., 2., 3., 4.), (1., 2., 3., 5.))):
    """The full {1,2,3,4}^q union {1,2,3,5}^q start family, 2*4^q - 3^q rows.

    Never subsampled.  An undersampled descent returns a HIGHER minimum, so it
    overstates eps and flatters the bound.
    """
    if q in _TEMPLATES:
        return _TEMPLATES[q]
    out = []
    for v in vals:
        grids = np.meshgrid(*([np.array(v)] * q), indexing="ij")
        out.append(np.stack([x.ravel() for x in grids], 1))
    T = np.unique(np.concatenate(out, 0), axis=0)
    _TEMPLATES[q] = T
    return T
