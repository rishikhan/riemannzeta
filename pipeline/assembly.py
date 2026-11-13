"""Assemble the final bound from the window form factor H and the local eps.

    s1/N >= max_m  (m H - eta B (m - q)) / (m - R),
    A = eps (m - q),   R = g_q(A),   eta = R / A,   g_q(E) = E below T_q = (q+1)/q
                                                    2 sqrt(T_q E) - T_q above it.

`final_bound` runs in round-to-nearest binary64, so its last significant digit
can sit above the exact assembly.  A quoted bound comes from
`final_bound_floor`, which computes the assembly in exact rationals, encloses
the one irrational step sqrt(T_q A) two-sided and takes the min over that
enclosure, so the returned Fraction is at or below the exact bound at every m.
"""
from __future__ import annotations

from decimal import Decimal, ROUND_FLOOR, getcontext
from fractions import Fraction
from math import isqrt

import numpy as np


def g_q(E, q):
    """The banded spectral envelope: the identity below the knee T_q."""
    T = (q + 1) / q
    return E if E <= T else 2 * np.sqrt(T * E) - T


def final_bound(H, eps, B, q, mhi=3000):
    """-> (bound, m*) maximized over the block length m."""
    best = (-1.0, 0)
    for m in range(q + 2, mhi):
        A = eps * (m - q)
        if A < 0:
            continue
        if A == 0.0:                      # eta -> 1 as A -> 0, since g_q(E) = E
            R, eta = 0.0, 1.0
        else:
            R = g_q(A, q)
            eta = R / A
        v = (m * H - eta * B * (m - q)) / (m - R)
        if v > best[0]:
            best = (v, m)
    return best


def _sqrt_bracket(fr, extra_bits=256):
    """[lo, hi] rational enclosure of sqrt(fr), fr >= 0, with lo^2 <= fr <= hi^2."""
    if fr < 0:
        raise ValueError("sqrt of a negative rational")
    if fr == 0:
        return Fraction(0), Fraction(0)
    n, d = fr.numerator, fr.denominator
    r = isqrt(n * d << (2 * extra_bits))          # r^2 <= n*d*scale < (r+1)^2
    lo = Fraction(r, d << extra_bits)
    hi = Fraction(r + 1, d << extra_bits)
    assert lo * lo <= fr <= hi * hi
    return lo, hi


def final_bound_floor(H, eps, B, q, mhi=3000):
    """Rigorous rational lower bound on `final_bound`, and its argmax m.

    H, eps and B are exact: anything Fraction() accepts.
    """
    H, eps, B = Fraction(H), Fraction(eps), Fraction(B)
    T = Fraction(q + 1, q)
    best, bestm = None, 0
    for m in range(q + 2, mhi):
        A = eps * (m - q)
        if A < 0:
            continue
        if A <= T:                        # g_q(A) = A on this branch, exact
            Rlo = Rhi = A
        else:
            slo, shi = _sqrt_bracket(T * A)
            Rlo, Rhi = 2 * slo - T, 2 * shi - T

        def bnd(R):
            eta = Fraction(1) if A == 0 else R / A
            return (m * H - eta * B * (m - q)) / (m - R)

        v = min(bnd(Rlo), bnd(Rhi))       # conservative over the sqrt enclosure
        if best is None or v > best:
            best, bestm = v, m
    return best, bestm


def frac_floor_decimal(fr, places=16):
    """fr rounded DOWN to `places` decimal places, so it stays a lower bound."""
    getcontext().prec = places + 40
    d = Decimal(fr.numerator) / Decimal(fr.denominator)
    return str(d.quantize(Decimal(1).scaleb(-places), rounding=ROUND_FLOOR))
