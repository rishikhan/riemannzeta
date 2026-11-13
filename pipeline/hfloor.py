"""A certified rational floor for the window form factor H = 2 - W.

`pipeline.kernel.hwin` evaluates H by Gauss-Legendre quadrature, which ranks
windows but certifies nothing.  For a window that is a finite cosine sum every
integral in W is elementary, so W has a closed form and evaluates in
outward-rounded interval arithmetic.

DERIVATION.  With I1 = int_{-1/2}^{1/2} v and A(alpha) = int v(t) v(t-alpha) dt
over the overlap,

    W = [ A(0) + 2 int_0^1 alpha A(alpha) d alpha ] / I1^2 ,

and {(t,u) in [-1/2,1/2]^2 : t - u = alpha} is A's domain, so

    W = [ int v^2 + int int |t-u| v(t) v(u) ] / (int v)^2 .

Write S(p) = int_{-1/2}^{1/2} cos(p u) du = 2 sin(p/2)/p, with S(0) = 1.  Then

    int v   = sum_j c_j S(w_j)
    int v^2 = sum_{j,k} c_j c_k [S(w_j - w_k) + S(w_j + w_k)] / 2

and, integrating t out of the |t-u| kernel, for a != 0

    g_a(u) = int |t-u| cos(a t) dt = sin(a/2)/a + 2 cos(a/2)/a^2 - 2 cos(a u)/a^2

so that

    I(a,b) = [S(a)/2 + 2 cos(a/2)/a^2] S(b) - [S(a-b) + S(a+b)] / a^2 .

For a = 0, g_0(u) = u^2 + 1/4 and I(0,b) = int (u^2 + 1/4) cos(b u) du, giving

    I(0,b) = 2[ sin(b/2)/(4b) + cos(b/2)/b^2 - 2 sin(b/2)/b^3 ] + S(b)/4
    I(0,0) = 1/3 .

The factor 2 on the sin(b/2)/b^3 term is load-bearing.  Dropping it OVERSTATES
H, the unsafe direction, and the a = 0 branch fires only when a constant
term meets a non-harmonic frequency.  On the harmonic grid b = 2 j pi the term
vanishes, so a harmonic-only check cannot see it.

Zero-ness is decided on the SPEC STRINGS, never numerically: w_j - w_k is
exactly zero when the two spec strings are equal, and w_j + w_k is exactly zero
only when both denote zero.

I(a,b) is symmetric in (a,b) although the formula is not manifestly so.

ARITHMETIC.  Arb balls, the same library the kernel tables use, so one interval
implementation carries the whole certified numerical path.  Arb tracks the
error of every operation, including the trigonometry, and `arb.lower()` and
`arb.upper()` return the ball's endpoints exactly, which `exact_endpoints`
converts to `Fraction` without a float round trip.  The floor is then compared
against the certificate as exact rationals.
"""
from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx

from pipeline.freqspec import arb_freq, canon


def _prec(dps):
    """Working precision in bits for a request of `dps` decimal digits."""
    return int(dps * 3.3219280948873626) + 32


class Iv:
    """An enclosure, carried as its two exact rational endpoints."""

    __slots__ = ("a", "b")

    def __init__(self, a, b):
        self.a, self.b = a, b

    def __repr__(self):
        return f"[{float(self.a):.17g}, {float(self.b):.17g}]"


def _exact(x):
    """The exact rational an Arb endpoint denotes."""
    man, exp = x.man_exp()
    return Fraction(int(man)) * Fraction(2) ** int(exp)


def _iv(ball):
    lo, hi = ball.lower(), ball.upper()
    assert lo.rad() == 0 and hi.rad() == 0
    return Iv(_exact(lo), _exact(hi))


def S(p, zero):
    """int_{-1/2}^{1/2} cos(p u) du = 2 sin(p/2)/p, exactly 1 at p = 0.

    `zero` states on exact index grounds that p is identically zero.
    """
    if zero:
        return arb(1)
    return 2 * (p / 2).sin() / p


def I(a, b, a_zero, b_zero, diff_zero, sum_zero):
    """int int_{[-1/2,1/2]^2} |t-u| cos(a t) cos(b u) dt du."""
    if a_zero and b_zero:
        return arb(1) / 3
    if a_zero:
        return (2 * ((b / 2).sin() / (4 * b) + (b / 2).cos() / b ** 2
                     - 2 * (b / 2).sin() / b ** 3) + S(b, False) / 4)
    return ((S(a, False) / 2 + 2 * (a / 2).cos() / a ** 2) * S(b, b_zero)
            - (S(a - b, diff_zero) + S(a + b, sum_zero)) / a ** 2)


def _W_ball(numerators, denominator, freqs, prec):
    freqs = [canon(t) for t in freqs]
    c = [arb(int(n)) / int(denominator) for n in numerators]
    w = [arb_freq(t, prec) for t in freqs]
    n = len(c)
    zero = [t == "0" for t in freqs]

    I1 = arb(0)
    for j in range(n):
        I1 = I1 + c[j] * S(w[j], zero[j])

    num = arb(0)
    for j in range(n):
        for k in range(n):
            if int(numerators[j]) == 0 or int(numerators[k]) == 0:
                continue
            cc = c[j] * c[k]
            dz = freqs[j] == freqs[k]
            sz = zero[j] and zero[k]
            quad = (S(w[j] - w[k], dz) + S(w[j] + w[k], sz)) / 2
            dist = I(w[j], w[k], zero[j], zero[k], dz, sz)
            num = num + cc * (quad + dist)
    return num / (I1 * I1), I1


def W_interval(numerators, denominator, freqs, dps=60):
    """-> (W, I1), rigorous enclosures."""
    prec = _prec(dps)
    old = ctx.prec
    try:
        ctx.prec = prec
        W, I1 = _W_ball(numerators, denominator, freqs, prec)
        return _iv(W), _iv(I1)
    finally:
        ctx.prec = old


def H_interval(numerators, denominator, freqs, dps=60):
    """-> (H, W, I1), rigorous enclosures, with H = 2 - W."""
    prec = _prec(dps)
    old = ctx.prec
    try:
        ctx.prec = prec
        W, I1 = _W_ball(numerators, denominator, freqs, prec)
        return _iv(2 - W), _iv(W), _iv(I1)
    finally:
        ctx.prec = old


def floor_rational(H, den):
    """The largest k/den at or below the enclosure's lower endpoint.

    The endpoints are exact rationals, so the floor is exact: no candidate is
    guessed in floating point and then checked.
    """
    k = (H.a * den).numerator // (H.a * den).denominator
    return Fraction(k, den)


def exact_endpoints(val):
    """The enclosure's endpoints as exact rationals."""
    return val.a, val.b


def tail_sum(numerators, denominator):
    """sum_{n>=1} |c_n|, the window tail Lemma 4.1 needs below 0.0796."""
    return sum(abs(int(n)) for n in numerators[1:]) / int(denominator)
