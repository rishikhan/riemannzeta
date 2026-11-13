"""Leaf format study: exact checker for candidate formats and a generator for them.

Formats (all verified by fcheck, an exact copy of replay's mcheckGX that also returns the
per-gap Ng arguments):

* The checker reads, per leaf, an evaluation point g* (one value per gap, multiple of G inside
  [L_r, U_r]); per term a kind; the multiplier list.
* Derived anchors: x*_n = sum_{i <= r < j} g*_r, clamped into the term range [eL, eU];
  anchor(n) = the multiple of G nearest x*_n inside [ceil_G eL, floor_G eU] (ties down).
  Adjacent term r (gap r): kind 3 uses p1 = floor_G(g*_r) clamped, p2 = p1 + G.
* Non-adjacent kinds: 0 constant, 1 tangent(anchor).  Adjacent kinds: 0 constant, 1 tangent,
  2 constant + tangent, 3 tangent(p1) + tangent(p2); the weight lambda of kinds 2 and 3 is
  computed by the checker (lam_rule), not stored.
* Explicit anchor escape (kind 1 with offset d): anchor = derived + d*G (d != 0 stored).
"""
import math
import os
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'q9'))
import qgen                                  # noqa: E402
from core import SC, replay                  # noqa: E402

nsub = replay.nsub
E10, E9 = 1e10, 1e9


def lo32(v): return v & 0xFFFFFFFF
def hi32(v): return v >> 32
def trip(v): return v & ((1 << 96) - 1)


def mwc(k, lam): return 1024 if k == 0 else (nsub(1024, lam) if k == 2 else 0)
def mw1(k, lam): return {0: 0, 1: 1024, 2: lam, 3: nsub(1024, lam)}[k]
def mw2(k, lam): return lam if k == 3 else 0


class Fmt:
    def __init__(self, C, G=128):
        self.C = C
        self.M = C.M
        self.G = G
        M = self.M
        self.adj = [j - i == 1 for (i, j, a, k) in M.TS]
        self.adj_of_gap = {M.TS[n][0]: n for n in range(len(M.TS)) if self.adj[n]}

    # ------------------------------------------------------------ exact parts
    def mult_ps(self, s, mults):
        L, U, A, B = s
        M = self.M
        P = [0] * M.Q; S = [0] * M.Q; Cp = 0; Cm = 0
        for (c, sd, q) in mults:
            Y = M.SIG * q
            if c == M.NP:                    # half-space row g_0 <= g_{Q-1} (hs.ydec_half)
                P[M.Q - 1] += Y; S[0] += Y
                Cp += Y * nsub(L[M.Q - 1], L[0]); Cm += Y * nsub(L[0], L[M.Q - 1])
                continue
            Ylo = 0 if sd == 1 else Y
            Yhi = Y if sd == 1 else 0
            i, j = M.PR[c]
            sL = sum(L[i:j])
            for r in range(i, j):
                P[r] += Ylo; S[r] += Yhi
            Cp += Ylo * nsub(sL, A[c]) + Yhi * nsub(B[c], sL)
            Cm += Ylo * nsub(A[c], sL) + Yhi * nsub(sL, B[c])
        return P, S, Cp, Cm

    def fcheck(self, s, rngs, terms, PS):
        """replay.Checker.mcheck (non-variance) -> (ok, lhs, rhs, inner[g], parts)."""
        C, M = self.C, self.M
        L, U, A, B = s
        P, S, Cp, Cm = PS
        PT = C.PT
        sum_mcn = sum_mcp = sum_mv = 0
        okterms = True
        wsl = [0] * M.Q; ssl = [0] * M.Q
        for n, (i, j, tA, kk) in enumerate(M.TS):
            eL, eU, eL0 = rngs[n]
            a, lam, p, r = terms[n]
            l1, l2, lc = mw1(a, lam), mw2(a, lam), mwc(a, lam)
            ok = lam <= 1024
            fp = trip(PT(p)) if l1 else 0
            fr = trip(PT(r)) if l2 else 0
            if ok and l1:
                ok = C.ivIn(PT(p), eL, eU, p)
            if ok and l2:
                ok = C.ivIn(PT(r), eL, eU, r)
            okterms = okterms and ok
            Mp, Mr = hi32(hi32(fp)), hi32(hi32(fr))
            mcn = l1 * nsub(2000000000, Mp) * nsub(p, eL0) + l2 * nsub(2000000000, Mr) * nsub(r, eL0)
            mcp = l1 * nsub(Mp, 2000000000) * nsub(p, eL0) + l2 * nsub(Mr, 2000000000) * nsub(r, eL0)
            mv = (lc * C.lb(eL, max(eU, eL + 1)) if lc else 0) + l1 * lo32(fp) + l2 * lo32(fr)
            msl = l1 * lo32(hi32(fp)) + l2 * lo32(hi32(fr))
            sum_mcn += tA * mcn; sum_mcp += tA * mcp; sum_mv += tA * mv
            for g in range(i, j):
                wsl[g] += tA * (l1 + l2)
                ssl[g] += tA * msl
        inner = [2000000000 * wsl[g] + P[g] - 1024000000000 * M.BS[g] - ssl[g] - S[g] for g in range(M.Q)]
        Ng_sum = sum(nsub(U[g], L[g]) * max(0, inner[g]) for g in range(M.Q))
        lhs = 335544320000000000 * M.cN + 10 * (sum_mcn + Cp + Ng_sum)
        rhs = 10240000000000 * sum(M.BS[g] * L[g] for g in range(M.Q)) + 32768 * sum_mv + 10 * (sum_mcp + Cm)
        boxok = all(L[g] <= U[g] for g in range(M.Q))
        return (lhs <= rhs and okterms and boxok), lhs, rhs, inner, okterms

    def lam_rule(self, s, rngs, terms, PS):
        """Checker-computed lambda for every adjacent term of kind 2 or 3 (others unchanged).
        margin is separable in these lambdas: f_r(lam) = lam*beta - 10 W_r max(0, I0 + lam d)."""
        terms = list(terms)
        idx = [n for n in range(len(terms)) if self.adj[n] and terms[n][0] in (2, 3)]
        if not idx:
            return terms
        t0 = [(a, 0, p, r) if n in idx else (a, lam, p, r) for n, (a, lam, p, r) in enumerate(terms)]
        in0 = self.fcheck(s, rngs, t0, PS)[3]
        L, U = s[0], s[1]
        for n in idx:
            g = self.M.TS[n][0]
            tA = self.M.TS[n][2]
            a, _, p, r = terms[n]
            beta = self.term_val(rngs[n], (a, 1024, p, r), tA) - self.term_val(rngs[n], (a, 0, p, r), tA)
            I0 = in0[g]
            d1024 = self.term_inner(rngs[n], (a, 1024, p, r), tA) - self.term_inner(rngs[n], (a, 0, p, r), tA)
            W = 10 * nsub(U[g], L[g])
            cands = {0, 1024}
            if d1024 != 0:
                # I0 + lam * d1024 / 1024 = 0
                l0f = (-I0 * 1024) // d1024
                for x in (l0f, l0f + 1):
                    if 0 <= x <= 1024:
                        cands.add(x)
            best = None
            for x in sorted(cands):
                f = x * beta - W * max(0, I0 * 1024 + x * d1024)
                if best is None or f > best[0]:
                    best = (f, x)
            terms[n] = (a, best[1], p, r)
        return terms

    def term_val(self, rng, t, tA):
        """RHS - LHS contribution of one term without its Ng part (exact integer)."""
        C = self.C
        eL, eU, eL0 = rng
        a, lam, p, r = t
        l1, l2, lc = mw1(a, lam), mw2(a, lam), mwc(a, lam)
        fp = trip(C.PT(p)) if l1 else 0
        fr = trip(C.PT(r)) if l2 else 0
        Mp, Mr = hi32(hi32(fp)), hi32(hi32(fr))
        mcn = l1 * nsub(2000000000, Mp) * nsub(p, eL0) + l2 * nsub(2000000000, Mr) * nsub(r, eL0)
        mcp = l1 * nsub(Mp, 2000000000) * nsub(p, eL0) + l2 * nsub(Mr, 2000000000) * nsub(r, eL0)
        mv = (lc * C.lb(eL, max(eU, eL + 1)) if lc else 0) + l1 * lo32(fp) + l2 * lo32(fr)
        return tA * (32768 * mv + 10 * mcp - 10 * mcn)

    def term_inner(self, rng, t, tA):
        C = self.C
        a, lam, p, r = t
        l1, l2 = mw1(a, lam), mw2(a, lam)
        fp = trip(C.PT(p)) if l1 else 0
        fr = trip(C.PT(r)) if l2 else 0
        msl = l1 * lo32(hi32(fp)) + l2 * lo32(hi32(fr))
        return tA * (2000000000 * (l1 + l2) - msl)

    # ------------------------------------------------------------ anchors
    def snap(self, x, eL, eU):
        G = self.G
        lo = -(-eL // G) * G
        hi = (eU // G) * G
        if hi < lo:
            return None
        x = min(max(x, eL), eU)
        p = ((x + G // 2 - 1) // G) * G     # nearest, ties down
        return min(max(p, lo), hi)

    def anchors(self, s, gs, rngs):
        """Derived anchors per term: (pn, p1, p2) (p1, p2 only for adjacent terms)."""
        M, G = self.M, self.G
        out = []
        for n, (i, j, tA, kk) in enumerate(M.TS):
            eL, eU, _ = rngs[n]
            x = sum(gs[i:j])
            pn = self.snap(x, eL, eU)
            if self.adj[n]:
                lo = -(-eL // G) * G
                p1 = max(lo, (min(max(x, eL), eU) // G) * G)
                p2 = p1 + G
                if p2 > eU:
                    p1, p2 = p1 - G, p1
                out.append((pn, p1, p2))
            else:
                out.append((pn, None, None))
        return out

    def valid(self, p, eL, eU):
        if p is None:
            return False
        w = self.C.PT(p)
        return bool(w) and self.C.ivIn(w, eL, eU, p)

    def decode(self, s, gs, kinds, offs=None):
        """kinds per term -> terms (a, lam=0, p, r) before lam_rule; offs: {n: d} anchor offsets."""
        rngs = self.C.term_ranges(s)
        an = self.anchors(s, gs, rngs)
        terms = []
        for n, k in enumerate(kinds):
            pn, p1, p2 = an[n]
            if offs and n in offs and pn is not None:
                pn = pn + offs[n] * self.G
            if k == 0:
                terms.append((0, 0, 0, 0))
            elif k == 1:
                terms.append((1, 0, pn, 0))
            elif k == 2:
                terms.append((2, 0, pn, 0))
            else:
                terms.append((3, 0, p1, p2))
        return rngs, terms

    def check(self, s, gs, kinds, mults, offs=None):
        rngs, terms = self.decode(s, gs, kinds, offs)
        if any(t[0] and t[2] is None for t in terms):
            return False, None, terms
        PS = self.mult_ps(s, mults)
        terms = self.lam_rule(s, rngs, terms, PS)
        ok, lhs, rhs, inner, okt = self.fcheck(s, rngs, terms, PS)
        return ok, rhs - lhs, terms


# ---------------------------------------------------------------- LP over explicit candidates
class LP:
    half = False                             # True: one more multiplier column, the half-space row (record c = NP)

    def __init__(self, C):
        self.C = C
        self.M = C.M
        M = self.M
        self.a = [t[2] / M.SA for t in M.TS]
        self.b = [x / M.SA for x in M.BS]
        self.yq = M.SIG / (1024e9 * M.SA)

    def cand(self, rng, p):
        """(val at L0, slope) of candidate p (None = constant)."""
        C = self.C
        eL, eU, L0 = rng
        if p is None:
            return C.lb(eL, max(eU, eL + 1)) / E10, 0.0
        w = C.PT(p)
        V, P, Mv = w & 0xFFFFFFFF, (w >> 32) & 0xFFFFFFFF, (w >> 64) & 0xFFFFFFFF
        return V / E10 - (2e9 - Mv) / E9 * nsub(p, L0) / SC, (P - 2e9) / E9

    def solve(self, s, cands, fixed=None, fixy=None, ypen=0.0):
        """cands[n]: list of p (None = constant).  fixed[n]: {k: weight} or None.
        fixy: {(c, sd): q}.  -> dict(margin, mu, ylo, yhi, gstar) or None."""
        M, C = self.M, self.C
        L, U, A, B = s
        rngs = C.term_ranges(s)
        nT = len(M.TS)
        idx = []
        nvar = 0
        for cl in cands:
            idx.append(list(range(nvar, nvar + len(cl)))); nvar += len(cl)
        NP = M.NP
        ylo0 = nvar; nvar += NP
        yhi0 = nvar; nvar += NP
        yh = nvar if self.half else None
        nvar += 1 if self.half else 0
        z0 = nvar; nvar += M.Q
        obj = np.zeros(nvar)
        const = sum(self.b[r] * L[r] for r in range(M.Q)) / SC - M.cN / M.SA
        rows, cols, vals = [], [], []
        for n, (i, j, tA, kk) in enumerate(M.TS):
            for k, p in enumerate(cands[n]):
                v, sl = self.cand(rngs[n], p)
                obj[idx[n][k]] = self.a[n] * v
                if sl != 0.0:
                    for r in range(i, j):
                        rows.append(r); cols.append(idx[n][k]); vals.append(-self.a[n] * sl)
        sL = [sum(L[i:j]) for (i, j) in M.PR]
        for c, (i, j) in enumerate(M.PR):
            obj[ylo0 + c] = (A[c] - sL[c]) / SC - ypen
            obj[yhi0 + c] = (sL[c] - B[c]) / SC - ypen
            for r in range(i, j):
                rows.append(r); cols.append(ylo0 + c); vals.append(1.0)
                rows.append(r); cols.append(yhi0 + c); vals.append(-1.0)
        if self.half:
            obj[yh] = (L[0] - L[M.Q - 1]) / SC - ypen
            rows.append(M.Q - 1); cols.append(yh); vals.append(1.0)
            rows.append(0); cols.append(yh); vals.append(-1.0)
        for r in range(M.Q):
            obj[z0 + r] = -(U[r] - L[r]) / SC
            rows.append(r); cols.append(z0 + r); vals.append(-1.0)
        Aub = coo_matrix((vals, (rows, cols)), shape=(M.Q, nvar)).tocsr()
        er, ec = [], []
        for n in range(nT):
            for v in idx[n]:
                er.append(n); ec.append(v)
        Aeq = coo_matrix((np.ones(len(er)), (er, ec)), shape=(nT, nvar)).tocsr()
        bounds = [(0, None)] * nvar
        ymax = self.yq * 16383
        for v in range(ylo0, z0):
            bounds[v] = (0, ymax)
        if fixy:
            for (c, sd), q in fixy.items():
                v = yh if c == NP else (ylo0 if sd == 0 else yhi0) + c
                bounds[v] = (q * self.yq, q * self.yq)
        if fixed:
            for n, fx in enumerate(fixed):
                if fx is None:
                    continue
                for k, v in enumerate(idx[n]):
                    w = fx.get(k, 0.0)
                    bounds[v] = (w, w)
        r = linprog(-obj, A_ub=Aub, b_ub=np.array(self.b), A_eq=Aeq, b_eq=np.ones(nT), bounds=bounds, method='highs')
        if r.status != 0:
            return None
        x = r.x
        pi = -np.array(r.ineqlin.marginals)
        gstar = [L[g] + SC * pi[g] for g in range(M.Q)]
        return dict(margin=const + float(obj @ x), mu=[x[ix] for ix in idx], ylo=x[ylo0:yhi0], yhi=x[yhi0:yhi0 + NP],
                    yh=x[yh] if self.half else 0.0, gstar=gstar, rngs=rngs)

    def mults(self, sol, mode='round'):
        q = []
        ys = [(c, sd, y) for c in range(self.M.NP) for sd, y in ((0, sol['ylo'][c]), (1, sol['yhi'][c]))]
        if self.half:
            ys.append((self.M.NP, 0, sol['yh']))
        for c, sd, y in ys:
            v = y / self.yq
            qi = int(math.floor(v)) if mode == 'floor' else (int(math.ceil(v - 1e-12)) if mode == 'ceil' else int(round(v)))
            qi = max(0, min(16383, qi))
            if qi:
                q.append((c, sd, qi))
        return q
