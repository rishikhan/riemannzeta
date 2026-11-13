"""Leaf certificates with the half-space row and the variance bonus (options of LeafSolverHS).

Derived from gen/leaf.py (LeafSolver) and q9/qgen.py (LeafSolverQ); the margin model is the
same (FORMAT.md section 8) with two additions:

* half: one more multiplier yh >= 0 on the reflection half-space g_0 <= g_{Q-1}
  (attempt-032's PCellHalf row).  LP column: kappa row Q-1 +1, row 0 -1, objective
  (L_0 - L_{Q-1})/SC, bound [0, ymax].  Encoded as a multiplier record with pair index NP
  (hs.ydec_half); the exact check is hs.HSChecker.
* var: two-tangent candidates (kind 3) with the anchor-variance bonus vbW of attempt-031's
  mleafV, for terms whose range spans at most five 256-cells with a positive curvature field.
  (p, r) neighbours or second neighbours among the term's tangent candidates sorted by position,
  lambda in {256, 512, 768}/1024,
  value (1 - lam) T_p + lam T_r + vbon/(1024 e10) (the exact bonus of the record), slope the
  mix of the two slopes.  A leaf is checked first without the variance bit and, if that fails,
  with it (replay mcheck with variance=True reads M.TBL).

Every emitted leaf is verified with the exact checker (HSChecker.mleaf); the LP only proposes.
"""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import qgen
from core import SC

nsub = qgen.nsub
E10 = 1e10
E9 = 1e9
VAR_LAMS = (256, 512, 768)


class LeafSolverHS(qgen.LeafSolverQ):
    def __init__(self, C, pt, half=False, var=False, **kw):
        super().__init__(C, pt, **kw)
        self.half = half
        self.var = var          # variance bit allowed in the exact check
        self.varc = var         # variance candidates in the LP
        self.last_var = False

    # ---------------------------------------------------------------- candidates
    def _term_cands(self, eL, eU, L0):
        cands = super()._term_cands(eL, eU, L0)
        if not self.varc or eU // 256 - eL // 256 > 4:
            return cands
        C = self.C
        if C.cmin(eL // 256, nsub(eU // 256, eL // 256)) == 0:
            return cands
        tan = {cd[1]: (cd[2], cd[3], cd[4]) for cd in cands if cd[0] == 1}
        ps = sorted(tan)
        for u in range(len(ps)):
            for v in range(u + 1, min(len(ps), u + 3)):
                for lam in VAR_LAMS:
                    cands.append(self._varcand(eL, eU, tan, ps[u], ps[v], lam))
        return cands

    def _varcand(self, eL, eU, tan, p, r, lam):
        (jp, vp, sp), (jr, vr, sr) = tan[p], tan[r]
        bon = self.C.vbW(eL, eU, 3, lam, p, r)
        val = ((1024 - lam) * vp + lam * vr + bon / E10) / 1024
        slope = ((1024 - lam) * sp + lam * sr) / 1024
        return (3, (p, r), (jp, jr), val, slope, lam)

    def var_options(self, cands, mu, rng, top=2, tol=1e-9):
        """Fix options for a term whose LP weights use variance candidates: for the top pairs by
        weight (pair columns plus the two tangents), one column (p, r, lam*) with lam* the weighted
        mean mixing weight on the 1/1024 grid (appended to the cached candidate list if new)."""
        eL, eU, L0 = rng
        tan = {cd[1]: (cd[2], cd[3], cd[4]) for cd in cands if cd[0] == 1}
        tw = {cd[1]: w for cd, w in zip(cands, mu) if cd[0] == 1 and w > tol}
        grp = {}
        for cd, w in zip(cands, mu):
            if cd[0] == 3 and w > tol:
                g = grp.setdefault(cd[1], [0.0, 0.0])
                g[0] += w; g[1] += w * cd[5]
        opts = []
        for (p, r), (w, wl) in sorted(grp.items(), key=lambda kv: -kv[1][0])[:top]:
            wp, wr = tw.get(p, 0.0), tw.get(r, 0.0)
            lam = int(round((wl + 1024 * wr) / (w + wp + wr)))
            lam = min(1023, max(1, lam))
            idx = None
            for k, cd in enumerate(cands):
                if cd[0] == 3 and cd[1] == (p, r) and cd[5] == lam:
                    idx = k
                    break
            if idx is None:
                cands.append(self._varcand(eL, eU, tan, p, r, lam))
                idx = len(cands) - 1
            opts.append({idx: 1.0})
        return opts

    # ---------------------------------------------------------------- LP
    def solve_lp(self, s, c=None, fixed=None, fixy=None):
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
        Q = M.Q
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
        yh = None
        if self.half:
            yh = nvar; nvar += 1
        z0 = nvar; nvar += Q
        obj = np.zeros(nvar)
        const = sum(self.b[r] * L[r] for r in range(Q)) / SC - c
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
        if yh is not None:
            obj[yh] = (L[0] - L[Q - 1]) / SC
            rows.append(Q - 1); cols.append(yh); vals.append(1.0)
            rows.append(0); cols.append(yh); vals.append(-1.0)
        for r in range(Q):
            obj[z0 + r] = -(U[r] - L[r]) / SC
            rows.append(r); cols.append(z0 + r); vals.append(-1.0)
        Aub = coo_matrix((vals, (rows, cols)), shape=(Q, nvar)).tocsr()
        tau = [self.tau_q * self.yq if (U[r] - L[r]) > self.tau_w else 0.0 for r in range(Q)]
        bub = np.array(self.b) - np.array(tau)
        er, ec, ev = [], [], []
        for n in range(nT):
            for v in mu_idx[n]:
                er.append(n); ec.append(v); ev.append(1.0)
        Aeq = coo_matrix((ev, (er, ec)), shape=(nT, nvar)).tocsr()
        beq = np.ones(nT)
        ymax = self.yq * ((1 << M.QB) - 1)
        bounds = [(0, None)] * nvar
        for v in range(ylo0, z0):
            bounds[v] = (0, ymax)
        if fixy is not None:
            for (cidx, sd), qi in fixy.items():
                v = yh if cidx == NP else (ylo0 if sd == 0 else yhi0) + cidx
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
                    mu=[x[ix] for ix in mu_idx], ylo=x[ylo0:yhi0], yhi=x[yhi0:yhi0 + NP],
                    yh=(x[yh] if yh is not None else 0.0), z=x[z0:], rngs=rngs)

    # ---------------------------------------------------------------- quantise and encode
    @staticmethod
    def _pick(cands, mu, tol=1e-9):
        """<= 2 (k, weight) entries forming a decoder kind; a variance candidate stands alone."""
        nz = [(k, w) for k, w in enumerate(mu) if w > tol]
        if not nz:
            nz = [(int(np.argmax(mu)), 1.0)]
        nz.sort(key=lambda t: -t[1])
        if cands[nz[0][0]][0] == 3:
            return [(nz[0][0], 1.0)]
        nz = [t for t in nz if cands[t[0]][0] != 3][:2]
        tot = sum(w for _, w in nz)
        return [(k, w / tot) for k, w in nz]

    def encode_terms(self, sol):
        """-> (bits, nbits, specs); spec = (kind, lam, p, r, fix) with fix the frozen weights."""
        bits = 0
        o = 0
        specs = []
        for n, cands in enumerate(sol['terms']):
            pk = self._pick(cands, sol['mu'][n])
            if len(pk) == 1 and cands[pk[0][0]][0] == 3 and 'rngs' in sol:
                pk = [(list(self.var_options(cands, sol['mu'][n], sol['rngs'][n], top=1)[0])[0], 1.0)]
            if len(pk) == 1:
                k = pk[0][0]
                cd = cands[k]
                if cd[0] == 3:
                    (p, r), (jp, jr), lam = cd[1], cd[2], cd[5]
                    rec, ln = 3 | (jp << 2) | (jr << 9) | (lam << 16), 26
                    spec = (3, lam, p, r, {k: 1.0})
                elif k == 0:
                    rec, ln = 0, 2
                    spec = (0, 0, None, None, {0: 1.0})
                else:
                    rec, ln = 1 | (cd[2] << 2), 9
                    spec = (1, 0, cd[1], None, {k: 1.0})
            else:
                (k1, w1), (k2, w2) = pk
                if k2 == 0:
                    k1, w1, k2, w2 = k2, w2, k1, w1
                lam = min(1023, max(0, int(round(1024 * w2))))
                if k1 == 0:
                    rec, ln = 2 | (cands[k2][2] << 2) | (lam << 9), 19
                    spec = (2, lam, cands[k2][1], None, {0: (1024 - lam) / 1024, k2: lam / 1024})
                else:
                    rec, ln = 3 | (cands[k1][2] << 2) | (cands[k2][2] << 9) | (lam << 16), 26
                    spec = (3, lam, cands[k1][1], cands[k2][1], {k1: (1024 - lam) / 1024, k2: lam / 1024})
            bits |= rec << o
            o += ln
            specs.append(spec)
        return bits, o, specs

    def mult_from(self, sol, mode='round'):
        q = []
        mx = (1 << self.M.QB) - 1
        f = (lambda v: int(np.floor(v))) if mode == 'floor' else \
            ((lambda v: int(np.ceil(v))) if mode == 'ceil' else (lambda v: int(round(v))))
        for cidx in range(self.M.NP):
            for sd, y in ((0, sol['ylo'][cidx]), (1, sol['yhi'][cidx])):
                qi = max(0, min(mx, f(y / self.yq)))
                if qi:
                    q.append((cidx, sd, qi))
        if self.half:
            qi = max(0, min(mx, f(sol['yh'] / self.yq)))
            if qi:
                q.append((self.M.NP, 0, qi))
        return q

    def check(self, s, payload):
        """Exact check; tries the plain leaf, then (var) the variance leaf.
        -> (end offset or 0, rhs - lhs); self.last_var says which one passed."""
        n, det = self.C.mleaf(payload, s, False, want_detail=True)
        self.last_var = False
        if n or not self.var:
            return n, det['rhs'] - det['lhs']
        n2, det2 = self.C.mleaf(payload, s, True, want_detail=True)
        if n2:
            self.last_var = True
            return n2, det2['rhs'] - det2['lhs']
        return 0, max(det['rhs'] - det['lhs'], det2['rhs'] - det2['lhs'])

    def _try(self, s, tb, to, sol):
        best = None
        for mode in ('round', 'floor', 'ceil'):
            q = self.mult_from(sol, mode)
            mb, mo = self.encode_mult(q)
            payload = tb | (mb << to)
            n, mg = self.check(s, payload)
            if n and n == to + mo:
                return (payload, to + mo, mg), True
            if best is None or mg > best[2]:
                best = (payload, to + mo, mg)
        return best, False

    def certify(self, s, c=None):
        r = self._certify(s, c)
        if r[0] is not None and r[1] > self.MAXBITS:
            r = (None, 0, r[2], r[3])
        if r[0] is None and self.varc:
            # variance terms are 26-bit records: retry without the variance candidates
            self.varc = False
            tc = self._tc
            self._tc = {}
            try:
                r2 = self.certify(s, c)
            finally:
                self.varc = True
                self._tc = tc
            if r2[0] is not None:
                return r2
        return r

    def certify1(self, s, c=None):
        sol = self.solve_lp(s, c)
        if sol is None:
            return None, 0, None, None
        scale = 335544320000000000 * self.M.SA
        tb, to, specs = self.encode_terms(sol)
        best, ok = self._try(s, tb, to, sol)
        if ok:
            return best[0], best[1], best[2] / scale, sol['margin']
        fixed = [sp[4] for sp in specs]
        sol2 = self.solve_lp(s, c, fixed=fixed)
        if sol2 is not None:
            b2, ok = self._try(s, tb, to, sol2)
            if ok:
                return b2[0], b2[1], b2[2] / scale, sol['margin']
            if b2[2] > best[2]:
                best = b2
        r = self.certify_iter(s, c, sol)
        if r is not None:
            return r[0], r[1], r[2], sol['margin']
        return None, 0, best[2] / scale, sol['margin']

    def certify_iter(self, s, c, sol):
        """Iterative rounding (gen/leaf.py) with variance candidates and the half multiplier."""
        M = self.M
        nT = len(M.TS)
        fixed = [None] * nT
        scale = 335544320000000000 * M.SA
        cur = sol
        for _ in range(nT):
            mixed = []
            for n in range(nT):
                if fixed[n] is not None:
                    continue
                nz = [k for k, w in enumerate(cur['mu'][n]) if w > 1e-9]
                if len(nz) > 1 or (nz and cur['terms'][n][nz[0]][0] == 3):
                    mixed.append((-(len(nz)), n))
            if not mixed:
                break
            mixed.sort()
            n = mixed[0][1]
            cands = cur['terms'][n]
            pk = self._pick(cands, cur['mu'][n])
            opts = []
            if any(cd[0] == 3 and w > 1e-9 for cd, w in zip(cands, cur['mu'][n])):
                opts += self.var_options(cands, cur['mu'][n], cur['rngs'][n])
                pk = self._pick([cd if cd[0] != 3 else (9,) for cd in cands],
                                [w if cd[0] != 3 else 0.0 for cd, w in zip(cands, cur['mu'][n])])
            if len(pk) == 1:
                opts.append({pk[0][0]: 1.0})
            else:
                (k1, w1), (k2, w2) = pk
                if k2 == 0:
                    k1, w1, k2, w2 = k2, w2, k1, w1
                for lam in sorted({int(np.floor(1024 * w2)), int(np.ceil(1024 * w2))}):
                    lam = min(1023, max(0, lam))
                    opts.append({k1: (1024 - lam) / 1024, k2: lam / 1024})
            bestn = None
            for fx_n in opts:
                fx = list(fixed)
                fx[n] = fx_n
                sl = self.solve_lp(s, c, fixed=fx)
                if sl is not None and (bestn is None or sl['margin'] > bestn[0]['margin']):
                    bestn = (sl, fx)
            if bestn is None:
                return None
            cur, fixed = bestn
        keys = [(cidx, sd) for cidx in range(M.NP) for sd in (0, 1)] + ([(M.NP, 0)] if self.half else [])

        def yval(key):
            cidx, sd = key
            if cidx == M.NP:
                return cur['yh']
            return (cur['ylo'] if sd == 0 else cur['yhi'])[cidx]
        fixy = {}
        mx = (1 << M.QB) - 1
        for _ in range(len(keys)):
            frac = [(-yval(k) / self.yq, k) for k in keys if k not in fixy and yval(k) / self.yq > 1e-6]
            if not frac:
                break
            frac.sort()
            v, key = -frac[0][0], frac[0][1]
            bestn = None
            for qi in sorted({int(np.floor(v)), int(np.ceil(v))}):
                qi = max(0, min(mx, qi))
                fy = dict(fixy); fy[key] = qi
                sl = self.solve_lp(s, c, fixed=fixed, fixy=fy)
                if sl is not None and (bestn is None or sl['margin'] > bestn[0]['margin']):
                    bestn = (sl, fy)
            if bestn is None:
                return None
            cur, fixy = bestn
        tb, to, specs = self.encode_terms(cur)
        b, ok = self._try(s, tb, to, cur)
        if ok:
            return b[0], b[1], b[2] / scale
        return None
