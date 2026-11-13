"""K-format: the leaf word the new 9-gap kernel checker reads (specified below).

Walk word at position pos (bits = (WL >> pos) & WMASK as before):
  bit 0 = 1  split: ax = bits 1..6, md = bits 7..9, children at pos + 10       (unchanged)
  bit 0 = 0  leaf:  reflection if U_{Q-1} < L_0 (next pos + 1)                 (unchanged)
                    else payload from bit 1 (no variance bit):
    per term n in TS order: 2-bit kind k, then
      k = 1: 7-bit anchor code
      k = 2: 7-bit anchor code, then 10-bit lambda only if term n is NOT adjacent
      k = 3: two 7-bit anchor codes, then 10-bit lambda only if NOT adjacent
    multiplier list as qgen (1, 6-bit pair, side, 14-bit q; 0 ends); pair NP = half-space row
    (q9hs/hs.ydec_half, attempt-032's ystepH), pair > NP ends
    next pos = pos + 1 + payload length
  Adjacent kinds 2 and 3 take lambda from the checker rule (f1.Fmt.lam_rule).

KChecker(QChecker) walks K-format streams exactly; kencode builds a root's stream from the dump
events and a leaf table.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import f1                                    # noqa: E402
import qgen                                  # noqa: E402
from core import replay                      # noqa: E402
sys.path.insert(0, os.path.join(HERE, '..', 'q9hs'))
import hs                                    # noqa: E402

CODES = list(range(33)) + list(range(64, 97)) + [33, 34]     # code index ci -> anchor code jj


def ci_of(jj):
    return CODES.index(jj)


class KChecker(qgen.QChecker):
    # multiplier list as the Lean checker's ystepH: c < NP pair, c = NP half-space row, c > NP ends
    ydec = hs.ydec_half
    adjlam = False                           # True: adjacent kinds 2, 3 store their lambda (no rule)

    def __init__(self, M):
        super().__init__(M)
        self.F = f1.Fmt(self)
        self.leaves = 0

    def kdecode(self, w, s):
        """-> (terms before the rule, mults, payload length) from payload word w (bit 0 = first payload bit)."""
        M = self.M
        rngs = self.term_ranges(s)
        o = 0
        terms = []
        for n, (eL, eU, eL0) in enumerate(rngs):
            k = (w >> o) & 3
            o += 2
            p = r = lam = 0
            if k:
                p = self.gptQG(3, eL, eU, (w >> o) & 127); o += 7
            if k == 3:
                r = self.gptQG(3, eL, eU, (w >> o) & 127); o += 7
            if k in (2, 3) and (self.adjlam or not self.F.adj[n]):
                lam = (w >> o) & 1023; o += 10
            terms.append((k, lam, p, r))
        o, P, S, Cp, Cm, nmul = self.ydec(s, M.QB, w, M.YFUEL, o)
        mults = []
        return rngs, terms, (P, S, Cp, Cm), o

    def leafStep(self, pos, w, s, rec, depth):
        L, U = s[0], s[1]
        if U[self.M.Q - 1] < L[0]:
            if rec is not None:
                rec['refl'] += 1
            return pos + 1
        rngs, terms, PS, n = self.kdecode(w >> 1, s)
        if not self.adjlam:
            terms = self.F.lam_rule(s, rngs, terms, PS)
        ok, lhs, rhs, inner, okt = self.F.fcheck(s, rngs, terms, PS)
        if rec is not None:
            rec['leaves'] += 1
            rec['margins'].append(rhs - lhs)
        if not ok:
            if rec is not None:
                rec['fail'].append(pos)
            return 0
        return pos + 1 + n


def leaf_word(C, s, terms, mults, adjlam=False):
    """K-format leaf bits (including the leading 0) and length, for kernel terms (k, lam, p, r)."""
    rngs = C.term_ranges(s)
    adj = [j - i == 1 for (i, j, a, kk) in C.M.TS]
    PB = qgen.pair_bits(C.M.NP)
    bits = 0; o = 1
    for n, (k, lam, p, r) in enumerate(terms):
        eL, eU, _ = rngs[n]
        bits |= k << o; o += 2
        for q in ([p] if k in (1, 2) else ([p, r] if k == 3 else [])):
            jj = next(c for c in CODES if C.gptQG(3, eL, eU, c) == q)
            bits |= jj << o; o += 7
        if k in (2, 3) and (adjlam or not adj[n]):
            bits |= lam << o; o += 10
    for (c, sd, q) in mults:
        bits |= (1 | (c << 1) | (sd << (1 + PB)) | (q << (2 + PB))) << o
        o += 2 + PB + C.M.QB
    o += 1
    return bits, o


def kencode(C, ev, leaves, rk):
    """Root stream from dump events ev (preorder) and leaves {(rk, i): (s, terms, mults)}."""
    bits = 0; pos = 1
    for i, e in enumerate(ev):
        if e[0] == 'S':
            bits |= (1 | (e[1] << 1) | (e[2] << 7)) << pos
            pos += 10
        elif e[0] == 'R':
            pos += 1
        else:
            s, terms, mults = leaves[(rk, i)]
            b, n = leaf_word(C, s, terms, mults)
            bits |= b << pos
            pos += n
    return bits, pos
