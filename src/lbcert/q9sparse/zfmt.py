"""Sparse leaf format Z (FORMAT.md): exact Python mirror of the Lean check (zlean.py, mleafZ), and the
conversion of K-format leaves into Z leaves.

Leaf payload (after the leaf's leading 0 bit): NT-bit presence mask; per listed term (increasing n) a 3-bit
kind z, the anchor codes (7 bits each: z 1, 2, >= 4 one, z 3 two), a 10-bit lam (z 2, 3, >= 4); then the
multiplier list of the K-format (hs.ydec_half).

ZChecker.leafStep evaluates exactly what mleafZ evaluates (same integer operations, same order of side
conditions); it never uses lb for an unlisted term.  zterms() maps a K-format leaf (terms after the
adjacent-lambda rule or with stored lambdas) to Z terms with the same value; to_zleaf() writes the word.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
for d in ('q9enc', 'q9', 'gen', ''):
    p = os.path.join(LB, d)
    if p not in sys.path:
        sys.path.insert(0, p)
import kformat                               # noqa: E402

LAMB = 10
NSLOT = {0: 0, 1: 1, 2: 1, 3: 2, 4: 1}


def nsub(a, b):
    return a - b if a > b else 0


def lo32(v): return v & 0xFFFFFFFF
def hi32(v): return v >> 32
def trip(v): return v & ((1 << 96) - 1)


class ZChecker(kformat.KChecker):
    """Walks Z-format streams; leafStep = Lean leafStep over mleafZ."""

    def zterm(self, z, w, o, eL, eU, e0, anchors=None):
        """tzv: (mv, cp, cn, sl, mw, ok, o').  anchors: a set that receives the tangent points read."""
        C = self
        if anchors is not None and z != 0:
            anchors.add(C.gptQG(3, eL, eU, (w >> o) & 127))
            if z == 3:
                anchors.add(C.gptQG(3, eL, eU, (w >> (o + 7)) & 127))
        if z == 1:
            p = C.gptQG(3, eL, eU, (w >> o) & 127)
            g = C.PT(p); v = trip(g)
            M = hi32(hi32(v))
            return (1024 * lo32(v), 1024 * nsub(M, 2000000000) * nsub(p, e0), 1024 * nsub(2000000000, M) * nsub(p, e0),
                    1024 * lo32(hi32(v)), 1024, 1 if C.ivIn(g, eL, eU, p) else 0, o + 7)
        if z == 3:
            p = C.gptQG(3, eL, eU, (w >> o) & 127)
            g = C.PT(p); v = trip(g)
            r = C.gptQG(3, eL, eU, (w >> (o + 7)) & 127)
            gr = C.PT(r); vr = trip(gr)
            lam = (w >> (o + 14)) & 1023
            l1 = nsub(1024, lam)
            Mp, Mr = hi32(hi32(v)), hi32(hi32(vr))
            ok = 1 if (lam <= 1024 and C.ivIn(g, eL, eU, p) and C.ivIn(gr, eL, eU, r)) else 0
            return (l1 * lo32(v) + lam * lo32(vr),
                    l1 * nsub(Mp, 2000000000) * nsub(p, e0) + lam * nsub(Mr, 2000000000) * nsub(r, e0),
                    l1 * nsub(2000000000, Mp) * nsub(p, e0) + lam * nsub(2000000000, Mr) * nsub(r, e0),
                    l1 * lo32(hi32(v)) + lam * lo32(hi32(vr)), l1 + lam, ok, o + 24)
        if z == 0:
            return 1024 * C.lb(eL, max(eU, eL + 1)), 0, 0, 0, 0, 1, o
        # z == 2 or z >= 4
        p = C.gptQG(3, eL, eU, (w >> o) & 127)
        g = C.PT(p); v = trip(g)
        lam = (w >> (o + 7)) & 1023
        M = hi32(hi32(v))
        mv = lam * lo32(v)
        if z == 2:
            mv += nsub(1024, lam) * C.lb(eL, max(eU, eL + 1))
        ok = 1 if (lam <= 1024 and C.ivIn(g, eL, eU, p)) else 0
        return (mv, lam * nsub(M, 2000000000) * nsub(p, e0), lam * nsub(2000000000, M) * nsub(p, e0),
                lam * lo32(hi32(v)), lam, ok, o + 17)

    KV = 1 << 160

    def zleaf(self, w, s, anchors=None):
        """mleafZ on payload w -> (result, margin, nterms): result = payload length if the check passes, else 0.
        Merged accumulators as the Lean check: CVP = sum a (32768 mv + 10 cp), CN = sum a cn,
        V_r = KV + sum (a 2e9 mw) - (a sl), truncated at 0 after every term (Nat.sub); a failed side condition
        ends the leaf with 0."""
        M = self.M
        Q = M.Q
        NT = len(M.TS)
        L, U, A, B = s
        rngs = self.term_ranges(s)
        m = w & ((1 << NT) - 1)
        o = NT
        CVP = CN = 0
        V = [self.KV] * Q
        nt = 0
        for n, (i, j, a, kk) in enumerate(M.TS):
            if (m >> n) & 1 != 1:
                continue
            nt += 1
            z = (w >> o) & 7
            eL, eU, e0 = rngs[n]
            mv, cp, cn, sl, mw, okt, o = self.zterm(z, w, o + 3, eL, eU, e0, anchors)
            if okt == 0:
                return 0, None, nt
            CVP += a * (32768 * mv + 10 * cp); CN += a * cn
            for r in range(i, j):
                V[r] = nsub(V[r] + a * (2000000000 * mw), a * sl)
        o, P, S, Cp, Cm, _ = self.ydec(s, M.QB, w, M.YFUEL, o)
        ngs = sum(nsub(U[r], L[r]) * nsub(V[r] + P[r], 1024000000000 * M.BS[r] + S[r] + self.KV) for r in range(Q))
        lhs = 335544320000000000 * M.cN + 10 * (CN + Cp + ngs)
        rhs = 10240000000000 * sum(M.BS[r] * L[r] for r in range(Q)) + CVP + 10 * Cm
        box = all(L[r] <= U[r] for r in range(Q))
        good = lhs <= rhs and box
        return (o if good else 0), rhs - lhs, nt

    def leafStep(self, pos, w, s, rec, depth):
        L, U = s[0], s[1]
        if U[self.M.Q - 1] < L[0]:
            if rec is not None:
                rec['refl'] += 1
            return pos + 1
        n, margin, nt = self.zleaf(w >> 1, s)
        if rec is not None:
            rec['leaves'] += 1
            rec['margins'].append(margin)
            rec.setdefault('nterms', []).append(nt)
        if n == 0:
            if rec is not None:
                rec['fail'].append(pos)
            return 0
        return pos + 1 + n


def zterms(C, s, rngs, terms):
    """K terms (k, lam, p, r) (lambdas final) -> Z terms [(n, z, ps, lam)] with the same value per term.
    Unlisted: constant with lb = 0.  Two-component terms with lam 0 or 1024 become one component."""
    out = []
    for n, (k, lam, p, r) in enumerate(terms):
        eL, eU, _ = rngs[n]
        lbz = C.lb(eL, max(eU, eL + 1)) == 0
        if k == 2 and lam == 0:
            k = 0
        if k == 2 and lam == 1024:
            k = 1
        if k == 3 and lam == 0:
            k = 1
        if k == 3 and lam == 1024:
            k, p = 1, r
        if k == 0:
            if not lbz:
                out.append((n, 0, [], 0))
        elif k == 1:
            out.append((n, 1, [p], 0))
        elif k == 2:
            out.append((n, 4 if lbz else 2, [p], lam))
        else:
            out.append((n, 3, [p, r], lam))
        if out and out[-1][0] == n and out[-1][1] in (2, 3, 4):
            assert 0 < lam < 1024
    return out


def code_of(C, eL, eU, p):
    """the anchor code jj (in kformat.CODES order of preference) with gptQG(3, eL, eU, jj) = p"""
    return next(c for c in kformat.CODES if C.gptQG(3, eL, eU, c) == p)


def zleaf_bits(C, s, zt, mbits, mlen, codes=None):
    """Z leaf word including the leading 0 bit, and its length.  zt: zterms(); mbits/mlen: the multiplier
    list bits (K-format, terminator included).  codes: optional {(n, slot): jj} to reuse given codes."""
    NT = len(C.M.TS)
    rngs = C.term_ranges(s)
    mask = 0
    body = 0; o = 0
    for (n, z, ps, lam) in zt:
        mask |= 1 << n
        body |= z << o; o += 3
        eL, eU, _ = rngs[n]
        for sl, p in enumerate(ps):
            jj = codes[(n, sl)] if codes and (n, sl) in codes else code_of(C, eL, eU, p)
            assert C.gptQG(3, eL, eU, jj) == p
            body |= jj << o; o += 7
        if z in (2, 3, 4):
            body |= lam << o; o += LAMB
    bits = (mask << 1) | (body << (1 + NT)) | (mbits << (1 + NT + o))
    return bits, 1 + NT + o + mlen
