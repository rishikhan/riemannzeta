"""Cubic-spline tables of W, W' and W'' on a uniform grid.

Three INDEPENDENT splines, one per derivative order, so the second derivative
keeps O(h^4) accuracy rather than the O(h^2) of differentiating one spline.

The knots are `linspace(0, ymax, n)`, so the interval index is `floor(x/h)` and
no per-point binary search is needed.  Evaluation is that multiply-index
followed by Horner, sharing one index computation across all three splines.

The knot grid is evaluated in slices: `ktrip` is row-independent and its only
reduction runs along the contiguous frequency axis, so a chunked evaluation
gives the same knot values as one call and holds ten times less memory.

The table is an interpolant used by the FLOAT search.  No certificate reads it;
the certificate's tables are the outward-rounded interval ones from
`pipeline.tables`.
"""
from __future__ import annotations

import numpy as np
from scipy import interpolate

from pipeline.kernel import kernel_exact


class WTable:
    """W, W' and W'' on [0, ymax]; W is zero beyond ymax.

    `knot_eval`, when given, replaces the knot evaluator.  The threaded C++
    evaluator goes in there, which changes no value: its knot arrays are
    bit-identical, so the fitted spline coefficients are too.
    """

    def __init__(self, coeff, omega, ymax=34.0, h=2.5e-5, knot_eval=None,
                 knot_chunk=200_000, correct=True):
        self.coeff = np.asarray(coeff, float)
        self.omega = np.asarray(omega, float)
        self.ymax = float(ymax)
        _, Wall, self.k0 = kernel_exact(self.coeff, self.omega)
        self.Wexact = Wall
        evaluate = knot_eval if knot_eval is not None else Wall
        n = int(round(ymax / h)) + 1
        gy = np.linspace(0.0, ymax, n)
        w = np.empty(n)
        wp = np.empty(n)
        wpp = np.empty(n)
        for lo in range(0, n, knot_chunk):
            hi = min(lo + knot_chunk, n)
            w[lo:hi], wp[lo:hi], wpp[lo:hi] = evaluate(gy[lo:hi])
        sW = interpolate.CubicSpline(gy, w)
        sWp = interpolate.CubicSpline(gy, wp)
        sWpp = interpolate.CubicSpline(gy, wpp)

        self.correct = bool(correct)
        self.breaks = np.ascontiguousarray(sW.x)
        self.nint = len(self.breaks) - 1                # number of intervals
        # spacing from the stored breakpoints, not from the requested h
        self.inv_h = self.nint / (self.breaks[-1] - self.breaks[0])
        self.top = self.nint - 1
        self.hmax = float(np.diff(self.breaks).max())
        self.cw = [np.ascontiguousarray(sW.c[k]) for k in range(4)]
        self.cp = [np.ascontiguousarray(sWp.c[k]) for k in range(4)]
        self.cpp = [np.ascontiguousarray(sWpp.c[k]) for k in range(4)]

    # ------------------------------------------------------------- indexing
    def _idx_t(self, x):
        """The interval index and the local coordinate, without a search.

        `x` lies in [0, ymax], so the lower clamp on the index is a no-op and
        only the upper one is applied.  The correction test reuses the
        `breaks[idx]` gather that `t` needs anyway and compares against the
        scalar hmax instead of gathering `breaks[idx+1]`: an index one too LOW
        implies `t >= breaks[idx+1] - breaks[idx]`, so `t >= hmax` is a
        conservative flag.  It can only over-select, and the flagged points are
        re-derived by searchsorted.
        """
        b, top = self.breaks, self.top
        idx = (x * self.inv_h).astype(np.int64)
        np.minimum(idx, top, out=idx)
        t = x - b[idx]
        if self.correct:
            bad = (t < 0.0) | (t >= self.hmax)
            if bad.any():
                # BOOLEAN masking, not flatnonzero: x arrives two-dimensional
                # from the batched objective, where a flat index would address
                # the wrong axis.
                xb = x[bad]
                f = np.clip(np.searchsorted(b, xb, side="right") - 1, 0, top)
                idx[bad] = f
                t[bad] = xb - b[f]
        return idx, t

    @staticmethod
    def _horner(c, idx, t):
        r = c[0][idx]
        r *= t
        r += c[1][idx]
        r *= t
        r += c[2][idx]
        r *= t
        r += c[3][idx]
        return r

    # -------------------------------------------------------------- the API
    def W(self, x):
        """W at |x|, zero beyond ymax."""
        x = np.abs(np.asarray(x, float))
        if x.size and x.max() <= self.ymax:
            idx, t = self._idx_t(x)
            return self._horner(self.cw, idx, t)
        inb = x <= self.ymax
        # Send out-of-range arguments to 0.0, an interior knot, rather than
        # clipping them to ymax, which sits at the top of the last interval and
        # trips the conservative index flag en masse.  Their values are
        # overwritten below.
        idx, t = self._idx_t(np.where(inb, x, 0.0))
        r = self._horner(self.cw, idx, t)
        r[~inb] = 0.0
        return r

    def all3(self, x):
        """W, W' and W'' from ONE index computation."""
        x = np.asarray(x, float)
        if x.size and x.min() >= 0.0 and x.max() <= self.ymax:
            idx, t = self._idx_t(x)
            return (self._horner(self.cw, idx, t),
                    self._horner(self.cp, idx, t),
                    self._horner(self.cpp, idx, t))
        inb = (x <= self.ymax) & (x >= 0.0)
        idx, t = self._idx_t(np.where(inb, x, 0.0))
        out = []
        for cf in (self.cw, self.cp, self.cpp):
            r = self._horner(cf, idx, t)
            r[~inb] = 0.0
            out.append(r)
        return tuple(out)
