"""Half-space row and variance bonus for the Q-gap leaf checker (exact side).

* HSChecker: qgen.QChecker whose multiplier list also accepts the reflection half-space row
  g_0 <= g_{Q-1} (attempt-032, module PCellHalf, ystepH):  pair index c == NP selects it, the
  record is 1 + PB + 1 + QB bits like a pair record (the side bit is read but ignored), and it
  adds Y to P_{Q-1} and S_0, Y (L_{Q-1} - L_0)^+ to Cp and Y (L_0 - L_{Q-1})^+ to Cm.  Index
  c > NP ends the list.  With half=False it is QChecker (c >= NP ends the list).
  The variance bonus needs no checker change: replay.Checker.mcheck already applies vbW when the
  leaf word's bit 1 is set (attempt-031's mleafV), reading the curvature table M.TBL.
* make_tb(C): the curvature table TB for the model's window, every 256-cell up to KB with the
  largest 12-bit field f that passes curvatureOk(256 i, 256 (i + 1), f 2^19, VD).
* tb_used(C, s, terms): curvature cells a variance leaf reads (for sizing a trimmed TB).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'q9'))
import qgen                                   # noqa: E402
from qgen import replay, pair_bits            # noqa: E402

nsub = replay.nsub


def ydec_half(self, s, qb, w, fuel, o):
    """ydecH (attempt-032) generalised to Q gaps / NP pairs."""
    L, U, A, B = s
    Q, NP = self.M.Q, self.M.NP
    PB = pair_bits(NP)
    P = [0] * Q; S = [0] * Q; Cp = 0; Cm = 0
    n = 0
    self.last_half = 0
    for _ in range(fuel):
        if ((w >> o) & 1) != 1:
            o = o + 1
            break
        c = (w >> (o + 1)) & ((1 << PB) - 1)
        o1 = o + 1 + PB
        if c > NP:
            o = o1 + qb + 1
            break
        Y = self.M.SIG * ((w >> (o1 + 1)) & nsub(1 << qb, 1))
        if c == NP:
            P[Q - 1] += Y; S[0] += Y
            Cp += Y * nsub(L[Q - 1], L[0])
            Cm += Y * nsub(L[0], L[Q - 1])
            self.last_half = Y
        else:
            sd = (w >> o1) & 1
            Ylo = 0 if sd == 1 else Y
            Yhi = Y if sd == 1 else 0
            i, j = self.PR_(c)
            sL = sum(L[i:j])
            for r in range(i, j):
                P[r] += Ylo; S[r] += Yhi
            Cp += Ylo * nsub(sL, A[c]) + Yhi * nsub(B[c], sL)
            Cm += Ylo * nsub(A[c], sL) + Yhi * nsub(sL, B[c])
        o = o1 + qb + 1
        n += 1
    return o, P, S, Cp, Cm, n


class HSChecker(qgen.QChecker):
    half = True

    def ydec(self, s, qb, w, fuel, o):
        if self.half:
            return ydec_half(self, s, qb, w, fuel, o)
        return super().ydec(s, qb, w, fuel, o)


def tb_fields(C):
    """{cell index: 12-bit curvature field} for every cell with a nonzero field."""
    M = C.M
    out = {}
    for i in range(M.KB // 256):
        c = C.CE.cell(256 * i, 256 * i + 256)
        if not (c['ok'] and c['E2L'] > 0 and c['E3L'] > 0 and c['W2L'] > 0):
            continue
        f = min(4095, (2 * M.VD * c['W2L']) // (524288 * C.DZ ** 2))
        while f > 0 and not C.curvatureOk(256 * i, 256 * i + 256, f * 524288, M.VD):
            f -= 1
        if f > 0:
            out[i] = f
    return out


def pack_tb(fields, maxrun=64):
    """TB list (B0, N, T), B0 descending (tfld takes the first entry with B0 <= i)."""
    idx = sorted(fields)
    runs = []
    for i in idx:
        if runs and i == runs[-1][0] + len(runs[-1][1]) and len(runs[-1][1]) < maxrun:
            runs[-1][1].append(fields[i])
        else:
            runs.append((i, [fields[i]]))
    out = []
    for b0, fs in runs:
        T = 0
        for j, f in enumerate(fs):
            T |= f << (12 * j)
        out.append((b0, len(fs), T))
    out.sort(key=lambda t: -t[0])
    return out


def make_tb(C):
    tb = pack_tb(tb_fields(C))
    assert C.tbOk(tb)
    return tb


def tb_used(C, s, terms):
    """Curvature cells read by vbW for the kappa = 3 terms of a leaf (rngs from term_ranges)."""
    cells = set()
    for (eL, eU, _), (a, lam, p, r) in zip(C.term_ranges(s), terms):
        if a == 3 and C.vbW(eL, eU, a, lam, p, r):
            cells |= set(range(eL // 256, eU // 256 + 1))
    return cells
