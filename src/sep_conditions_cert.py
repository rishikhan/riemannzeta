#!/usr/bin/env python3
"""Certify the two window conditions of the separated-block assembly.

    .venv/bin/python src/sep_conditions_cert.py --out results/sep_conditions_final2_q12.json

The separated-block assembly (close-pair matching plus an eigenvalue cap on
17/20-separated blocks) needs two facts about the window v(s) = sum c_j cos(w_j s)
on [-1/2, 1/2], with rho = 1 / int v:

  (M) rho v(s) <= GAMMA (sincN(d(s - 1/2)) + sincN(d(s + 1/2)))^2 on |s| <= 1/2,
      d = 17/20.  The right side is nonnegative with Fourier support in [-d, d],
      so every d-separated principal Gram block has eigenvalues at most
      L = 2 GAMMA / d (1 + sincN(d)), and L < 2 is required.
  (K) k(t) / k(0) >= 1/8 on 0 <= t <= d, so every close pair has w >= 1/64 >= c.

Both are checked by Arb ball evaluation over a uniform subdivision, each
segment enclosed as one ball, so the check covers every point of the interval.
The window comes from --cert, a JSON file with a "window" entry; the default is the window of
the main theorem (src/lbcert/q12win/work/final2_q12_sepinput.json).
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from fractions import Fraction

from flint import arb, ctx

ROOT = pathlib.Path(__file__).resolve().parent.parent

ctx.prec = 128
D = Fraction(17, 20)
GAMMA = Fraction(7, 10)


def a(q):
    return arb(q.numerator) / q.denominator


def sinc_pi(z):
    return (arb.pi() * z).sinc()


def window(cert):
    w = cert["window"]
    coef = [arb(n) / w["denominator"] for n in w["numerators"]]
    freqs = [arb(2).sqrt()] + [2 * arb.pi() * j for j in range(1, len(coef))]
    return coef, freqs


def seg(lo, hi):
    return a(lo).union(a(hi))


def check(f, lo, hi, n):
    """Min over n segments of the lower end of f's ball on each segment."""
    worst = None
    for i in range(n):
        x = seg(lo + (hi - lo) * Fraction(i, n), lo + (hi - lo) * Fraction(i + 1, n))
        low = f(x).lower()
        worst = low if worst is None or low < worst else worst
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert", default="src/lbcert/q12win/work/final2_q12_sepinput.json")
    ap.add_argument("--n", type=int, default=20000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    rel = args.cert
    cert = json.load(open(ROOT / rel))
    coef, freqs = window(cert)

    # int_{-1/2}^{1/2} cos(w s) ds = sinc(w/2); zero for w = 2 pi j, j >= 1.
    k0 = sum(c * (w / 2).sinc() for c, w in zip(coef, freqs))
    rho = 1 / k0
    d, g = a(D), a(GAMMA)

    def v(s):
        return sum(c * (w * s).cos() for c, w in zip(coef, freqs))

    def maj_margin(s):
        m = (sinc_pi(d * (s - arb(1) / 2)) + sinc_pi(d * (s + arb(1) / 2))) ** 2
        return g * m - rho * v(s)

    def k(t):
        return sum(c * ((w / 2 - arb.pi() * t).sinc() + (w / 2 + arb.pi() * t).sinc()) / 2
                   for c, w in zip(coef, freqs))

    def close_margin(t):
        return k(t) / k0 - arb(1) / 8

    L = 2 * g / d * (1 + sinc_pi(d))
    # v and the majorant are even, so [0, 1/2] covers [-1/2, 1/2].
    mmin = check(maj_margin, Fraction(0), Fraction(1, 2), args.n)
    kmin = check(close_margin, Fraction(0), D, args.n)
    c = Fraction(cert["local_certificate"]["target"]["numerator"],
                 cert["local_certificate"]["target"]["denominator"])
    ok = mmin > 0 and kmin > 0 and L.upper() < 2 and c <= Fraction(1, 64)
    res = {
        "cert": rel, "sep": str(D), "gamma": str(GAMMA), "segments": args.n,
        "majorant_margin_lower": str(mmin), "eigencap_L_upper": str(L.upper()),
        "close_pair_margin_lower": str(kmin), "c_le_1_64": c <= Fraction(1, 64),
        "rho_upper": str(rho.upper()), "ok": bool(ok),
    }
    print(json.dumps(res, indent=1))
    if args.out:
        (ROOT / args.out).write_text(json.dumps(res, indent=1) + "\n")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
