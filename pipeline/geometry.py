"""Index bookkeeping for the (q+1)-point, q-gap local geometry.

The local object is

    F(g) = sum_{r=1..q} b_r g_r + sum_{0<=i<j<=q} a_ij W(y_j - y_i),   g >= 0
    y_0 = 0,  y_j = g_1 + ... + g_j

with a >= 0, b >= 0 and the span capacities sum_{j-i=s} a_ij = 2 for s = 1..q.
Everything here is the index algebra that turns a gap vector into pair
distances and back.
"""
from __future__ import annotations

import numpy as np


class Geom:
    """Pair indexing, gap-coverage and reversal maps at geometry length q."""

    def __init__(self, q):
        self.q = int(q)
        q = self.q
        self.PAIRS = [(i, j) for i in range(q + 1) for j in range(i + 1, q + 1)]
        self.NP = len(self.PAIRS)
        self.SPAN = np.array([j - i for i, j in self.PAIRS])
        # U[p, r] = 1 iff gap r+1 lies inside (y_i, y_j], so d = g @ U.T are the
        # pair distances.
        U = np.zeros((self.NP, q))
        for p, (i, j) in enumerate(self.PAIRS):
            U[p, i:j] = 1.0
        self.U = U
        # CAP @ a = 2 pins the span capacities, one row per span class.
        CAP = np.zeros((q, self.NP))
        for s in range(1, q + 1):
            CAP[s - 1, self.SPAN == s] = 1.0
        self.CAP = CAP
        # flattened rank-one outers, so a Hessian is one matmul
        self.UU = np.einsum("pr,ps->prs", U, U).reshape(self.NP, q * q)
        # SIG[k] indexes the reversal partner of PAIRS[k]
        idx = {p: k for k, p in enumerate(self.PAIRS)}
        self.SIG = [idx[(q - j, q - i)] for (i, j) in self.PAIRS]
        self.NV = q + self.NP


_GEOM = {}


def geom(q):
    """The Geom at length q, built once."""
    if q not in _GEOM:
        _GEOM[q] = Geom(q)
    return _GEOM[q]
