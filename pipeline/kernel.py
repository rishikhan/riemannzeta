"""The window kernel, in float64.

A window is a finite cosine sum on [-1/2, 1/2],

    v(s) = sum_j c_j cos(w_j s),

whose Fourier transform gives the kernel and the pair weight

    k(x) = sum_j c_j [sinc(w_j/2 - pi x) + sinc(w_j/2 + pi x)] / 2
    W(x) = (k(x) / k(0))^2.

`hwin` is the form factor H = 2 - W(v) by Gauss-Legendre quadrature, which is
what the search ranks on.  A certified floor for H comes from `hfloor`, which
evaluates the same functional in outward-rounded interval arithmetic.
"""
from __future__ import annotations

import numpy as np


def sinc3(z):
    """sinc(z), sinc'(z) and sinc''(z) for a real array z, stable near 0."""
    z = np.asarray(z, float)
    small = np.abs(z) < 1e-3
    zs = np.where(small, 1.0, z)
    s, c = np.sin(zs), np.cos(zs)
    v = s / zs
    d1 = (zs * c - s) / zs ** 2
    d2 = ((2.0 - zs ** 2) * s - 2.0 * zs * c) / zs ** 3
    if small.any():
        t = np.where(small, z, 0.0)
        t2 = t * t
        v = np.where(small, 1 - t2 / 6 + t2 * t2 / 120 - t2 ** 3 / 5040, v)
        d1 = np.where(small, -t / 3 + t * t2 / 30 - t * t2 * t2 / 840, d1)
        d2 = np.where(small, -1 / 3 + t2 / 10 - t2 * t2 / 168, d2)
    return v, d1, d2


def kernel_exact(coeff, omega):
    """-> (W, Wall, k0), callables on real x plus the normalizing k(0).

    `W(x)` is (k(|x|)/k0)^2.  `Wall(x)` adds the first two derivatives, with
    W' carrying the sign of x.
    """
    coeff = np.asarray(coeff, float)
    omega = np.asarray(omega, float)
    h = omega / 2.0

    def ktrip(x):
        x = np.atleast_1d(np.asarray(x, float))[..., None]
        px = np.pi * x
        lv, ld, ldd = sinc3(h - px)
        rv, rd, rdd = sinc3(h + px)
        k = (coeff * (lv + rv) / 2).sum(-1)
        kp = (coeff * np.pi * (rd - ld) / 2).sum(-1)
        kpp = (coeff * np.pi ** 2 * (ldd + rdd) / 2).sum(-1)
        return k, kp, kpp

    k0 = ktrip(0.0)[0][0]

    def W(x):
        k, _, _ = ktrip(np.abs(x))
        return (k / k0) ** 2

    def Wall(x):
        ax = np.abs(x)
        sg = np.sign(x)
        k, kp, kpp = ktrip(ax)
        w = (k / k0) ** 2
        wp = 2 * k * kp / k0 ** 2
        wpp = 2 * (kp ** 2 + k * kpp) / k0 ** 2
        return w, wp * sg, wpp

    return W, Wall, k0


def hwin(coeff, omega, n1=400, n2=1400):
    """H = 2 - W, with W = [A(0) + 2 int_0^1 alpha A(alpha) d alpha] / I1^2.

    A(alpha) is the overlap correlation int v(t) v(t - alpha) dt and I1 is
    int v over the half period.
    """
    coeff = np.asarray(coeff, float)
    omega = np.asarray(omega, float)
    xs, ws = np.polynomial.legendre.leggauss(n1)

    def v(s):
        return sum(c * np.cos(o * s) for c, o in zip(coeff, omega))

    I1 = float(0.5 * np.sum(ws * v(0.5 * xs)))

    def A(al):
        s = (1.0 - al) / 2
        m = al / 2
        t = s * xs + m
        return float(s * np.sum(ws * v(t) * v(t - al)))

    aa, wa = np.polynomial.legendre.leggauss(n2)
    al = 0.5 * (aa + 1)
    return 2.0 - (A(0.0)
                  + 2 * 0.5 * np.sum(wa * np.array([A(x) for x in al]) * al)) / I1 ** 2
