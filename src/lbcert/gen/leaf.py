"""Leaf certificates: a float LP picks term minorants and multipliers, then the choice is
quantised to the leaf word format and verified with replay's exact mcheck.

Margin model (F units, see FORMAT.md section 8).  Per term n with range [eL, eU] and
range start L0, a component k is the constant lb(eL, max(eU, eL+1))/1e10 (slope 0) or a
tangent at anchor p with word (V, P, M): value V/1e10 - (2e9 - M)/1e9 (p - L0)/SC at L0
and slope (P - 2e9)/1e9.  Weights mu_{n,k} >= 0 sum to 1.  Multipliers ylo_c, yhi_c >= 0
(real y = Y / (1024e9 SA)).  The gap coefficient is
  kap_r = b_r + sum_{n ∋ r} a_n sum_k mu slope - sum_{c ∋ r} ylo_c + sum_{c ∋ r} yhi_c
and the margin is
  sum_r b_r L_r/SC + sum_n a_n sum_k mu val - c + sum_c (ylo_c (A_c - sL_c) + yhi_c (sL_c - B_c))/SC
  - sum_r (U_r - L_r)/SC max(0, -kap_r).
"""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from core import SC, replay

nsub = replay.nsub
E10 = 1e10
E9 = 1e9


class LeafSolver:
    def __init__(self, C, pt, cN=None, fine=True, maxcand=1000):
        """C: replay Checker (its PT is replaced by pt); pt(x) -> expanded point word or 0."""
        self.C = C
        self.M = C.M
        self.pt = pt
        C.PT = pt
        self.cN = C.M.cN if cN is None else cN
        self.fine = fine
        self.maxcand = maxcand
        self._tc = {}
        self.base_fixed = None
        self.base_fixy = None
        self.allowed = None
        self.tau_q = 0.0
        self.tau_w = 64
        M = self.M
        self.a = [t[2] / M.SA for t in M.TS]
        self.b = [x / M.SA for x in M.BS]
        self.SIG = M.SIG
        self.yunit = 1024e9 * M.SA          # real y = Y / yunit
        self.yq = M.SIG / self.yunit        # multiplier quantum in y

    # ---------------------------------------------------------------- candidates
    def codes(self, L, U):
        """Distinct anchor positions reachable by the decoder on [L, U]: {p: code}."""
        C = self.C
        out = {}
        for jj in [33, 34] + list(range(0, 33)) + ([64 + j for j in range(33)] if self.fine else []):
            p = C.gptQG(self.M.FS, L, U, jj)
            if L <= p <= U and p not in out:
                out[p] = jj
        return out

    def term_cands(self, eL, eU, L0):
        """[(kind, p, code, val, slope, word)] for one term: the constant first."""
        key = (eL, eU, L0)
        r = self._tc.get(key)
        if r is None:
            if len(self._tc) > 500000:
                self._tc.clear()
            r = self._tc[key] = self._term_cands(eL, eU, L0)
        return r

    def _term_cands(self, eL, eU, L0):
        C = self.C
        lbv = C.lb(eL, max(eU, eL + 1))
        cands = [(0, None, None, lbv / E10, 0.0, None)]
        for p, jj in self.codes(eL, eU).items():
            w = self.pt(p)
            if not w or not C.ivIn(w, eL, eU, p):
                continue
            if self.allowed is not None and p not in self.allowed:
                continue
            V = w & 0xFFFFFFFF
            P = (w >> 32) & 0xFFFFFFFF
            Mv = (w >> 64) & 0xFFFFFFFF
            val = V / E10 - (2e9 - Mv) / E9 * nsub(p, L0) / SC
            cands.append((1, p, jj, val, (P - 2e9) / E9, w))
        if len(cands) > self.maxcand:
            # keep the constant and the best-valued tangents at a spread of slopes
            t = sorted(cands[1:], key=lambda c: c[4])
            idx = np.linspace(0, len(t) - 1, self.maxcand - 1).round().astype(int)
            cands = [cands[0]] + [t[i] for i in sorted(set(idx))]
        return cands

    # ---------------------------------------------------------------- LP
    def solve_lp(self, s, c=None, fixed=None, fixy=None):
        """Float LP. fixed: optional per-term list of (k-index -> weight) to freeze terms.
        Returns dict(margin, terms=[(cands, mu)], ylo, yhi, z) or None."""
        M = self.M
        C = self.C
        if len(C.lb_cache) > 100000:
            C.lb_cache.clear()
        if len(C.lbd_cache) > 100000:
            C.lbd_cache.clear()
        if len(C.CE.cache) > 20000:
            C.CE.cache.clear()
        if len(self._tc) > 30000:
            self._tc.clear()
        c = (self.cN / M.SA) if c is None else c
        L, U, A, B = s
        rngs = self.C.term_ranges(s)
        nT = len(M.TS)
        terms = [self.term_cands(*r) for r in rngs]
        nvar = 0
        mu_idx = []
        for tc in terms:
            mu_idx.append(list(range(nvar, nvar + len(tc))))
            nvar += len(tc)
        NP = M.NP
        ylo0 = nvar; nvar += NP
        yhi0 = nvar; nvar += NP
        z0 = nvar; nvar += M.Q
        obj = np.zeros(nvar)
        const = sum(self.b[r] * L[r] for r in range(M.Q)) / SC - c
        # kap_r rows: -kap_r - z_r <= 0  ->  -sum(a mu slope) + ylo - yhi - z <= b_r
        rows, cols, vals = [], [], []
        for n, (i, j, tA, kk) in enumerate(M.TS):
            an = self.a[n]
            for k, cd in enumerate(terms[n]):
                obj[mu_idx[n][k]] = an * cd[3]
                if cd[4] != 0.0:
                    for r in range(i, j):
                        rows.append(r); cols.append(mu_idx[n][k]); vals.append(-an * cd[4])
        sL = [sum(L[i:j]) for (i, j) in M.PR]
        for cidx, (i, j) in enumerate(M.PR):
            obj[ylo0 + cidx] = (A[cidx] - sL[cidx]) / SC
            obj[yhi0 + cidx] = (sL[cidx] - B[cidx]) / SC
            for r in range(i, j):
                rows.append(r); cols.append(ylo0 + cidx); vals.append(1.0)
                rows.append(r); cols.append(yhi0 + cidx); vals.append(-1.0)
        for r in range(M.Q):
            obj[z0 + r] = -(U[r] - L[r]) / SC
            rows.append(r); cols.append(z0 + r); vals.append(-1.0)
        Aub = coo_matrix((vals, (rows, cols)), shape=(M.Q, nvar)).tocsr()
        tau = [self.tau_q * self.yq if (U[r] - L[r]) > self.tau_w else 0.0 for r in range(M.Q)]
        bub = np.array(self.b) - np.array(tau)
        er, ec, ev = [], [], []
        for n in range(nT):
            for v in mu_idx[n]:
                er.append(n); ec.append(v); ev.append(1.0)
        Aeq = coo_matrix((ev, (er, ec)), shape=(nT, nvar)).tocsr()
        beq = np.ones(nT)
        ymax = self.yq * 16383
        bounds = [(0, None)] * nvar
        for v in range(ylo0, z0):
            bounds[v] = (0, ymax)
        if self.base_fixy is not None:
            merged = dict(self.base_fixy)
            merged.update(fixy or {})
            fixy = merged
        if self.base_fixed is not None:
            fixed = [f if f is not None else b for f, b in zip(fixed or [None] * len(M.TS), self.base_fixed)]
        if fixy is not None:
            for (cidx, sd), qi in fixy.items():
                v = (ylo0 if sd == 0 else yhi0) + cidx
                bounds[v] = (qi * self.yq, qi * self.yq)
        if fixed is not None:
            for n, fx in enumerate(fixed):
                if fx is None:
                    continue
                for k, v in enumerate(mu_idx[n]):
                    w = fx.get(k, 0.0)
                    bounds[v] = (w, w)
        r = linprog(-obj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
        if r.status != 0:
            return None
        x = r.x
        return dict(margin=const + float(obj @ x), terms=terms,
                    mu=[x[ix] for ix in mu_idx], ylo=x[ylo0:yhi0], yhi=x[yhi0:z0], z=x[z0:], rngs=rngs)

    # ---------------------------------------------------------------- quantise and encode
    @staticmethod
    def _pick(cands, mu, tol=1e-9):
        """Reduce a term's weights to a decoder kind: list of (k, weight) with <= 2 entries,
        at most one constant (kinds: const, tan, const+tan, tan+tan)."""
        nz = [(k, w) for k, w in enumerate(mu) if w > tol]
        if not nz:
            nz = [(int(np.argmax(mu)), 1.0)]
        nz.sort(key=lambda t: -t[1])
        nz = nz[:2]
        tot = sum(w for _, w in nz)
        return [(k, w / tot) for k, w in nz]

    def encode_terms(self, sol):
        """-> (bits int, nbits, per-term spec) for the 34 term records."""
        bits = 0
        o = 0
        specs = []
        for n, cands in enumerate(sol['terms']):
            pk = self._pick(cands, sol['mu'][n])
            if len(pk) == 1:
                k = pk[0][0]
                if k == 0:
                    rec, ln = 0, 2
                    spec = (0, 0, None, None)
                else:
                    rec, ln = 1 | (cands[k][2] << 2), 9
                    spec = (1, 0, cands[k][1], None)
            else:
                (k1, w1), (k2, w2) = pk
                if k2 == 0:
                    k1, w1, k2, w2 = k2, w2, k1, w1
                if k1 == 0:          # const + tangent k2: mwc = 1024 - lam, mw1 = lam
                    lam = min(1023, max(0, int(round(1024 * w2))))
                    rec, ln = 2 | (cands[k2][2] << 2) | (lam << 9), 19
                    spec = (2, lam, cands[k2][1], None)
                else:                # two tangents: mw1 = 1024 - lam (anchor k1), mw2 = lam (anchor k2)
                    lam = min(1023, max(0, int(round(1024 * w2))))
                    rec, ln = 3 | (cands[k1][2] << 2) | (cands[k2][2] << 9) | (lam << 16), 26
                    spec = (3, lam, cands[k1][1], cands[k2][1])
            bits |= rec << o
            o += ln
            specs.append(spec)
        return bits, o, specs

    def encode_mult(self, q):
        """q: list of (c, sd, qint) -> (bits, nbits) with terminator."""
        bits = 0
        o = 0
        for (cidx, sd, qi) in q[:41]:
            rec = 1 | (cidx << 1) | (sd << 6) | (qi << 7)
            bits |= rec << o
            o += 21
        o += 1                     # terminating 0 bit
        return bits, o

    def mult_from(self, ylo, yhi, mode='round'):
        q = []
        for cidx in range(self.M.NP):
            for sd, y in ((0, ylo[cidx]), (1, yhi[cidx])):
                v = y / self.yq
                qi = int(np.floor(v)) if mode == 'floor' else (int(np.ceil(v)) if mode == 'ceil' else int(round(v)))
                qi = max(0, min(16383, qi))
                if qi:
                    q.append((cidx, sd, qi))
        return q

    def check(self, s, payload):
        """Exact replay check of a payload (without the 2 leading leaf bits).
        -> (end offset or 0, rhs - lhs)."""
        n, det = self.C.mleaf(payload, s, False, want_detail=True)
        return n, det['rhs'] - det['lhs']

    MAXBITS = 598          # leaf word read through WMASK (600 bits) minus the 2 leaf bits

    def certify(self, s, c=None):
        r = self._certify(s, c)
        if r[0] is not None and r[1] > self.MAXBITS:
            return None, 0, r[2], r[3]
        return r

    def _certify(self, s, c=None):
        r = self.certify1(s, c)
        if r[0] is None and r[3] is not None and r[3] > 0:
            t0 = self.tau_q
            self.tau_q = 4.0
            try:
                r2 = self.certify1(s, c)
            finally:
                self.tau_q = t0
            if r2[0] is not None:
                return r2
        return r

    def certify1(self, s, c=None):
        """Full leaf attempt -> (payload, nbits, exact margin in F units, lp margin) or (None, ...)."""
        sol = self.solve_lp(s, c)
        if sol is None:
            return None, 0, None, None
        tb, to, specs = self.encode_terms(sol)
        scale = 335544320000000000 * self.M.SA
        best = None
        tries = [('lp', sol)]
        for tag, sl in tries:
            for mode in ('round', 'floor', 'ceil'):
                q = self.mult_from(sl['ylo'], sl['yhi'], mode)
                mb, mo = self.encode_mult(q)
                payload = tb | (mb << to)
                n, mg = self.check(s, payload)
                if n and n == to + mo:
                    return payload, to + mo, mg / scale, sol['margin']
                if best is None or mg > best[2]:
                    best = (payload, to + mo, mg)
        # second chance: freeze the quantised terms, re-solve the multipliers only
        fixed = self.fixed_from(sol, specs)
        sol2 = self.solve_lp(s, c, fixed=fixed)
        if sol2 is not None:
            for mode in ('round', 'floor', 'ceil'):
                q = self.mult_from(sol2['ylo'], sol2['yhi'], mode)
                mb, mo = self.encode_mult(q)
                payload = tb | (mb << to)
                n, mg = self.check(s, payload)
                if n and n == to + mo:
                    return payload, to + mo, mg / scale, sol['margin']
                if mg > best[2]:
                    best = (payload, to + mo, mg)
        r = self.certify_iter(s, c, sol)
        if r is not None:
            return r[0], r[1], r[2], sol['margin']
        return None, 0, best[2] / scale, sol['margin']

    def _lam_fix(self, cands, pk, lam):
        (k1, w1), (k2, w2) = pk
        if k2 == 0:
            k1, k2 = k2, k1
        return {k1: (1024 - lam) / 1024, k2: lam / 1024} if k1 != k2 else {k1: 1.0}

    def certify_iter(self, s, c, sol):
        """Iterative rounding: freeze one mixed term at a time at the better of its two
        neighbouring 1/1024 weights, re-solving the LP after each."""
        nT = len(self.M.TS)
        fixed = [None] * nT
        scale = 335544320000000000 * self.M.SA
        cur = sol
        for _ in range(nT):
            mixed = []
            for n in range(nT):
                if fixed[n] is not None:
                    continue
                nz = [w for w in cur['mu'][n] if w > 1e-9]
                if len(nz) > 1:
                    mixed.append((-(len(nz)), n))
            if not mixed:
                break
            mixed.sort()
            n = mixed[0][1]
            pk = self._pick(cur['terms'][n], cur['mu'][n])
            (k1, w1), (k2, w2) = pk
            wt = w2 if k1 != 0 and k2 != 0 else (w1 if k1 != 0 else w2)
            if k2 == 0 or (k1 != 0 and k2 != 0):
                wt = w2 if k2 != 0 else w1
            # weight on the second-listed tangent (or the tangent of a const+tan pair)
            if k1 == 0 or k2 == 0:
                kt = k2 if k1 == 0 else k1
                wt = dict(pk)[kt]
            else:
                wt = w2
            bestn = None
            for lam in sorted({int(np.floor(1024 * wt)), int(np.ceil(1024 * wt))}):
                lam = min(1023, max(0, lam))
                fx = list(fixed)
                fx[n] = self._lam_fix(cur['terms'][n], pk, lam)
                sl = self.solve_lp(s, c, fixed=fx)
                if sl is not None and (bestn is None or sl['margin'] > bestn[0]['margin']):
                    bestn = (sl, fx)
            if bestn is None:
                return None
            cur, fixed = bestn
        fixy = {}
        for _ in range(2 * self.M.NP):
            frac = []
            for cidx in range(self.M.NP):
                for sd, arr in ((0, cur['ylo']), (1, cur['yhi'])):
                    if (cidx, sd) in fixy:
                        continue
                    v = arr[cidx] / self.yq
                    if v > 1e-6:
                        frac.append((-v, cidx, sd, v))
            if not frac:
                break
            frac.sort()
            _, cidx, sd, v = frac[0]
            bestn = None
            for qi in sorted({int(np.floor(v)), int(np.ceil(v))}):
                qi = max(0, min(16383, qi))
                fy = dict(fixy); fy[(cidx, sd)] = qi
                sl = self.solve_lp(s, c, fixed=fixed, fixy=fy)
                if sl is not None and (bestn is None or sl['margin'] > bestn[0]['margin']):
                    bestn = (sl, fy)
            if bestn is None:
                return None
            cur, fixy = bestn
        # unfixed multipliers are now zero; freeze them at zero
        for cidx in range(self.M.NP):
            for sd in (0, 1):
                fixy.setdefault((cidx, sd), 0)
        tb, to, specs = self.encode_terms(cur)
        for mode in ('round', 'floor', 'ceil'):
            q = self.mult_from(cur['ylo'], cur['yhi'], mode)
            mb, mo = self.encode_mult(q)
            payload = tb | (mb << to)
            n, mg = self.check(s, payload)
            if n and n == to + mo:
                return payload, to + mo, mg / scale
        return None

    def fixed_from(self, sol, specs):
        fixed = []
        for n, cands in enumerate(sol['terms']):
            kind, lam, p, r = specs[n]
            idx = {cd[1]: k for k, cd in enumerate(cands) if cd[0] == 1}
            if kind == 0:
                fx = {0: 1.0}
            elif kind == 1:
                fx = {idx[p]: 1.0}
            elif kind == 2:
                fx = {0: (1024 - lam) / 1024, idx[p]: lam / 1024}
            else:
                fx = {idx[p]: (1024 - lam) / 1024}
                fx[idx[r]] = fx.get(idx[r], 0) + lam / 1024
            fixed.append(fx)
        return fixed
