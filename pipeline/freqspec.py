"""Frequency SPEC STRINGS, and rigorous values for them.

The H floor and the kernel tables are certified in interval arithmetic from
spec strings, never from floats.  An arbitrary float carrier has no rigorous
representation: the float 1.4142135623730951 is not sqrt(2), and a certificate
that treats it as such proves nothing.

The carrier is therefore restricted to w0 = sqrt(P/Q) with P and Q positive
integers.  `iv.mpf(P)/Q` is an outward-rounded enclosure of the exact rational,
and `iv.sqrt` of an enclosure is an enclosure of the exact square root, so
every downstream stage consumes a rigorous enclosure of an exact algebraic
number.  That family contains sqrt(2), is dense in the positive reals, and at
Q = 1e8 its spacing near sqrt(2) is about 3.5e-9, four orders finer than any
effect the search resolves.

Also accepted: "<p>/<q>*pi" and "<int>*pi" (iv.pi is an enclosure), bare
rationals, and "0".

The float stages use `float_freq`.  The gap between that float and the exact
algebraic number never enters a certificate, because the certified stages
re-derive the frequency from the spec string.
"""
from __future__ import annotations

import math
import re
from fractions import Fraction

from mpmath import iv

_INT = re.compile(r"^-?\d+$")
_RAT = re.compile(r"^(-?\d+)/(\d+)$")


def parse_rational(s):
    """Fraction from '<int>' or '<p>/<q>', None if it is neither."""
    s = s.strip()
    if _INT.match(s):
        return Fraction(int(s), 1)
    m = _RAT.match(s)
    if not m or int(m.group(2)) == 0:
        return None
    return Fraction(int(m.group(1)), int(m.group(2)))


def _body(t):
    return t[:-3] if t.endswith("*pi") else t


def is_zero_spec(t):
    """True when the spec string denotes exactly 0, however it is spelled."""
    t = t.strip()
    if t == "0":
        return True
    if t.startswith("sqrt("):
        return False
    f = parse_rational(_body(t))
    return f is not None and f == 0


def canon(t):
    """Canonical spelling, mapping every spelling of exact 0 to the literal "0".

    The zero flag is what makes S(0) = 1 exact.  A spec denoting 0 by any other
    spelling would reach S(p) = 2 sin(p/2)/p at p = 0 and the enclosure would
    come back nan.  The rewrite is exact and is the identity on every spec list
    that contains no such spelling.
    """
    return "0" if is_zero_spec(t) else t.strip()


def float_freq(t):
    """The float value of a spec string.  FLOAT stages only."""
    t = t.strip()
    if t == "sqrt(2)":
        return math.sqrt(2.0)
    if t == "0":
        return 0.0
    if t.startswith("sqrt(") and t.endswith(")"):
        f = parse_rational(t[5:-1])
        return math.sqrt(f.numerator / f.denominator)
    if t.endswith("*pi"):
        f = parse_rational(t[:-3])
        return (f.numerator / f.denominator) * math.pi
    f = parse_rational(t)
    return f.numerator / f.denominator


def arb_freq(t, prec):
    """Rigorous Arb enclosure of the frequency the spec string names.

    Arb carries its own working precision on `flint.ctx.prec`; `prec` is set by
    the caller around the whole evaluation, and is passed here only so a caller
    cannot forget to set it.
    """
    from flint import arb, ctx
    assert ctx.prec >= prec
    t = t.strip()
    if t == "0":
        return arb(0)
    if t.startswith("sqrt(") and t.endswith(")"):
        f = parse_rational(t[5:-1])
        assert f is not None and f > 0, t
        return (arb(f.numerator) / f.denominator).sqrt()
    if t.endswith("*pi"):
        f = parse_rational(t[:-3])
        assert f is not None, t
        return (arb(f.numerator) / f.denominator) * arb.pi()
    f = parse_rational(t)
    assert f is not None, t
    return arb(f.numerator) / f.denominator


def iv_freq(t):
    """Rigorous mpmath.iv enclosure of the frequency the spec string names.

    Retained for `pipeline.intervals`; the certified H floor uses `arb_freq`.
    """
    t = t.strip()
    if t == "0":
        return iv.mpf(0)
    if t.startswith("sqrt(") and t.endswith(")"):
        f = parse_rational(t[5:-1])
        assert f is not None and f > 0, t
        return iv.sqrt(iv.mpf(f.numerator) / f.denominator)
    if t.endswith("*pi"):
        f = parse_rational(t[:-3])
        assert f is not None, t
        return (iv.mpf(f.numerator) / f.denominator) * iv.pi
    f = parse_rational(t)
    assert f is not None, t
    return iv.mpf(f.numerator) / f.denominator


def carrier_spec(num, den=1):
    """Canonical spec string for sqrt(num/den).  P/Q = 2 renders as 'sqrt(2)'."""
    f = Fraction(int(num), int(den))
    assert f > 0
    if f.denominator == 1:
        return "sqrt(2)" if f.numerator == 2 else f"sqrt({f.numerator})"
    return f"sqrt({f.numerator}/{f.denominator})"


def pi_spec(num, den=1):
    f = Fraction(int(num), int(den))
    return (f"{f.numerator}*pi" if f.denominator == 1
            else f"{f.numerator}/{f.denominator}*pi")


def harm_specs(J, carrier="sqrt(2)"):
    """[carrier, 2*pi, 4*pi, ..., 2J*pi] as canonical spec strings."""
    return [carrier] + ["%d*pi" % (2 * j) for j in range(1, J + 1)]
