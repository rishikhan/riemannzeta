"""Recompute the window-dependent literals of the 16-harmonic Solution.lean and patch them in.

The window is v(s) = cos(sqrt 2 s) + sum_{j=1}^{16} c_j cos(2 pi j s), given as 17 numerators
over 10^9 (c_0 = 10^9).  Every literal below is a function of those numerators only, except
kappa, which also reads B and c from the final theorems (they are weight data):

  cAMn, CE, CJ, FA                    cell-evaluator tables and the window itself
  sum |c_j|                           sum_abs_cAM_succ, abs_pAM_le
  vAM 0                               vAM_zero
  core = floor_1e-3(3/4 - sum|c_j|)   vAM_ge_core and its consumers, core / MAM in hW_core_ge etc.
  |vAMd| <= ceil_0.1(3/2 + 6.3 sum |c_j| j)        abs_vAMd_le, A_1 = that / MAM
  |vAMdd| <= ceil_1(2 + 39.7 sum |c_j| j^2)        abs_vAMdd_le, vAMd_lipschitz, cellU, A_2
  rho = ceil_1/200(pvCheck value)     pvCheck_AM, profile_AM (exact pvCheck replay)
  r0 = ceil_0.01(sqrt(vAM 0 / MAM))   vAM_zero_div_le (r0^2) and the profile budget
  H_W floor (exact, 10^-40)           floor_numeric, HWexpr_ge, HW_ge, final chain
  1 + sum |c_j|                       profile_upper, normalized_profile_margin
  edge = ceil_1e-9(signed pAM bound)  pAM_le_edge, profile_upper_edge (1 + edge)
  corr = ceil_1e-9(sum |c_j| bTs)     correction_abs_le
  kappa = (H_W - B) / (1 - c)         actual_dyadic, actual_cumulative, candidate theorems

It also evaluates every side condition the fixed proofs need (see `checks`) and reports the
ones that fail.  Literals inside comments (notices) are never touched.

Usage:
  regen_window.py LEAN -o OUT [--window W.json] [--report R.json] [--replay]
W.json: a list of 17 integers, {"cAMn": [...]}, or a window-search record with "xfree"
(16 floats, c_0 = 1; numerators are round(x * 1e9)).  Without --window the file's own cAMn
(zero-padded to 17 terms) is used, which must reproduce the file unchanged.
"""
import argparse
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from fractions import Fraction as Fr
from types import SimpleNamespace

NH = 16
E9 = 10 ** 9
HERE = os.path.dirname(os.path.abspath(__file__))
REPLAY = os.path.join(HERE, '..', 'replay.py')
# enclosures used by floor_numeric (cos theta0 upper, sqrt2/2 lower, sin theta0 lower, pi upper)
COSU = (760244597075630151253547198623274394617584, 42)
R2 = (707106781186547524400844362104849039284835, 42)
SINL = (649636939080062444129478616044121910899027, 42)
PIU = (31415926535897932384626433832795028841972, 40)
MAM = Fr(5, 4)


# ---------------------------------------------------------------- formatting helpers

def fr(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else '%d / %d' % (x.numerator, x.denominator)


def ceil_to(x, q):
    """Smallest multiple of q that is >= x."""
    return math.ceil(Fr(x) / q) * Fr(q)


def floor_to(x, q):
    return math.floor(Fr(x) / q) * Fr(q)


# ---------------------------------------------------------------- window constants

def hw_floor(c):
    cu, r2, sl, piu = (Fr(a, 10 ** e) for a, e in (COSU, R2, SINL, PIU))
    pam = sum(Fr(c[n + 1], E9) ** 2 * (Fr(1, 2) - 1 / (4 * piu ** 2 * (n + 1) ** 2)) for n in range(NH))
    e = Fr(3, 2) - cu / (2 * r2 * sl) - pam / (2 * sl ** 2)
    return math.floor(e * 10 ** 40)


def edge_const(c):
    p = Fr(31416, 10000)
    return sum(Fr((-1) ** j * c[j], E9) + max(Fr(0), Fr(-((-1) ** j) * c[j], E9)) * 2 * p ** 2 * j * j / 400
               for j in range(1, NH + 1))


def bTs(n):
    return Fr(17, 37) if n == 0 else Fr(17, 20) / (Fr(157, 50) * ((n + 1) ** 2 - Fr(289, 400)))


def corr_const(c):
    return sum(Fr(abs(c[n + 1]), E9) * bTs(n) for n in range(NH))


def sqrt_ceil(x, q):
    """Smallest multiple k*q of q with (k*q)^2 >= x."""
    k = math.isqrt(math.floor(Fr(x) / q ** 2))
    while (k * q) ** 2 < x:
        k += 1
    return k * Fr(q)


def _replay():
    sys.path.insert(0, os.path.dirname(REPLAY))
    import replay
    return replay


def sin_table(PQ):
    """sinTabZ for cells of width 1/(2 PQ): entry q encloses sin(pi q / (2 PQ)), q = 0..PQ, as the
    interval that tabOk compares against (sinPiI, already on the 1e-10 grid), times 1e10."""
    M = SimpleNamespace(sinTabZ=[], cAMn={0: E9}, pv_lip=0, pv_rho=Fr(0), pv_terms=1, pv_cells=PQ)
    _replay().pv_check(M)
    tab = []
    for q in range(PQ + 1):
        lo, hi = M.pv_sinPiI(Fr(q, 2 * PQ))
        assert (lo * 10 ** 10).denominator == 1 and (hi * 10 ** 10).denominator == 1
        tab.append((int(lo * 10 ** 10), int(hi * 10 ** 10)))
    return tab


def pv_run(c, sintab, d2lit, PQ, rho):
    """Exact pvCheck replay with PQ cells; returns (passes, info, exact value)."""
    M = SimpleNamespace(sinTabZ=sintab, cAMn={j: v for j, v in enumerate(c)}, pv_lip=d2lit,
                        pv_rho=rho, pv_terms=NH + 1, pv_cells=PQ)
    ok, info = _replay().pv_check(M)
    return ok, info, M.pv_value


def pv_choose(c, d2lit, r0, cells):
    """Smallest cell count (from `cells`) whose pvCheck value, rounded up to 1/200, meets the
    profile budget; returns (PQ, table, rho, passes, value)."""
    for PQ in cells:
        tab = sin_table(PQ)
        _, info, val = pv_run(c, tab, d2lit, PQ, Fr(10 ** 6))
        assert info['tabOk'] and info['termOk'], info
        rho = ceil_to(val, Fr(1, 200))
        ok = pv_run(c, tab, d2lit, PQ, rho)[0]
        if ok and r0 + 2 * rho <= 1 and r0 ** 2 + 4 * rho <= 1:
            break
    return PQ, tab, rho, ok, val


def margin_const(V, X0):
    """normalized_profile_margin: with the hint (X0 - x)(579/400 - 2189/2400 (x + X0)) >= 0 the
    x and x^2 coefficients cancel exactly (multiplier 1), leaving this constant, which must be >= 0."""
    a, b = Fr(579, 400), Fr(2189, 2400)
    return Fr(7, 10) * Fr(29, 20) ** 2 - Fr(109, 100) * V - Fr(1, 1000) - X0 * (a - b * X0)


def compute(c, cells, B=None, cfl=None):
    assert len(c) == NH + 1 and c[0] == E9
    S = sum(abs(x) for x in c[1:])
    Sf = Fr(S, E9)
    v0 = sum(c)
    core = floor_to(Fr(3, 4) - Sf, Fr(1, 1000))
    d1 = Fr(3, 2) + Fr(63, 10) * Fr(sum(abs(c[j]) * j for j in range(1, NH + 1)), E9)
    d2 = 2 + Fr(397, 10) * Fr(sum(abs(c[j]) * j * j for j in range(1, NH + 1)), E9)
    d1lit = ceil_to(d1, Fr(1, 10))
    d2lit = math.ceil(d2)
    r0 = sqrt_ceil(Fr(v0, E9) / MAM, Fr(1, 100))
    PQ, sintab, rho, ok_pv, pv_val = pv_choose(c, d2lit, r0, cells)
    edge = edge_const(c)
    edge_num = math.ceil(edge * E9)
    corr = corr_const(c)
    corr_num = math.ceil(corr * E9)
    hw = hw_floor(c)
    K = dict(cAMn=list(c), S=S, v0=v0, core=core, core_M=core / MAM, d1=d1, d1lit=d1lit, A1=d1lit / MAM,
             d2=d2, d2lit=d2lit, A2=Fr(d2lit) / MAM, pv_cells=PQ, sintab=sintab, pv_value=pv_val, rho=rho, r0=r0,
             edge=edge, edge_num=edge_num, corr=corr, corr_num=corr_num, hw=hw)
    checks = {
        'vAM_le: 1 + sum|c| <= 5/4': 1 + Sf <= Fr(5, 4),
        'vAM_pos_wide: 1 - 9/25 - sum|c| > 0': 1 - Fr(9, 25) - Sf > 0,
        'profile ge_quarter: core / MAM >= 1/4': core / MAM >= Fr(1, 4),
        'aAM_range_of: (core / MAM)(15/16) >= 1/2': core / MAM * Fr(15, 16) >= Fr(1, 2),
        'pvCheck passes with rho (cells: %d)' % PQ: ok_pv,
        'profile budget: r0 + 2 rho <= 1': r0 + 2 * rho <= 1,
        'profile budget_sq: r0^2 + 4 rho <= 1': r0 ** 2 + 4 * rho <= 1,
        'correction_abs_le: (109/100) corr <= 187499999/2500000000':
            Fr(109, 100) * Fr(corr_num, E9) <= Fr(187499999, 2500000000),
        'normalized_profile_margin, |s| <= 9/20': margin_const(1 + Sf, Fr(81, 400)) >= 0,
        'normalized_profile_margin, 9/20 <= |s| <= 1/2': margin_const(1 + Fr(edge_num, E9), Fr(1, 4)) >= 0,
    }
    K['margin_core'] = margin_const(1 + Sf, Fr(81, 400))
    K['margin_edge'] = margin_const(1 + Fr(edge_num, E9), Fr(1, 4))
    if B is not None:
        kappa = (Fr(hw, 10 ** 40) - B) / (1 - cfl)
        K['kappa'] = kappa
    return K, checks


# ---------------------------------------------------------------- Lean text

def cAMn_block(c):
    return 'def cAMn : ℕ → ℤ\n' + ''.join(' | %d => %d\n' % (j, v) for j, v in enumerate(c)) + ' | _ => 0\n'


def ce_flag(c, j):
    return 'true' if -((-1) ** j) * c[j] > 0 else 'false'


def ce_block(c):
    it = ['(%d, %d, %s)' % (j, abs(c[j]), ce_flag(c, j)) for j in range(1, NH + 1)]
    return 'def CE : List (ℕ × ℕ × Bool) :=\n [' + ', '.join(it[:6]) + ',\n  ' + ', '.join(it[6:11]) + ',\n  ' + ', '.join(it[11:]) + ']\n'


def cj_block(c):
    it = ['| %d => (%d, %s)' % (j, abs(c[j]), 'true' if c[j] < 0 else 'false') for j in range(1, NH + 1)]
    return ('def CJ (j : ℕ) : ℕ × Bool :=\n match j with\n ' + ' '.join(it[:5]) + '\n ' + ' '.join(it[5:11])
            + '\n ' + ' '.join(it[11:]) + ' | _ => (0, false)\n')


def far_line(c):
    e = '⟨0, 0, 0, 0⟩'
    for j in range(1, NH + 1):
        e = '(farJ n k XL XU XL2 XU2 %s %d %d %s)' % (e, j, abs(c[j]), ce_flag(c, j))
    return ' let a := %s' % e


def comment_mask(src):
    """Boolean per character: inside a (nested) block comment or a line comment."""
    mask = bytearray(len(src))
    i, depth, n = 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1
            mask[i:i + 2] = b'\1\1'
            i += 2
        elif depth and src.startswith('-/', i):
            depth -= 1
            mask[i:i + 2] = b'\1\1'
            i += 2
        elif not depth and src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            mask[i:j] = b'\1' * (j - i)
            i = j
        else:
            if depth:
                mask[i] = 1
            i += 1
    return mask


class Patcher:
    def __init__(self, src):
        self.src = src
        self.log = []

    def _code_matches(self, pat):
        mask = comment_mask(self.src)
        return [m for m in re.finditer(pat, self.src, re.M) if not mask[m.start()]]

    def get(self, pat, group=1):
        ms = self._code_matches(pat)
        if len(ms) != 1:
            raise ValueError('%d code matches for %r' % (len(ms), pat))
        return ms[0].group(group)

    def sub(self, pat, repl, n, what):
        """Replace the code (non-comment) matches of pat; n = expected count (None: at least 1)."""
        ms = self._code_matches(pat)
        if (n is not None and len(ms) != n) or not ms:
            raise ValueError('%s: %d code matches (want %s) for %r' % (what, len(ms), n, pat))
        out, last, changed = [], 0, 0
        for m in ms:
            new = m.expand(repl) if isinstance(repl, str) else repl(m)
            changed += new != m.group(0)
            out.append(self.src[last:m.start()])
            out.append(new)
            last = m.end()
        out.append(self.src[last:])
        self.src = ''.join(out)
        self.log.append((what, len(ms), changed))


def patch_pv(P, PQ, tab):
    """Regenerate sinTabZ and set the pvCheck cell count to PQ in the block from `def sinTabZ` to
    `theorem pvCheck_AM`: every literal of the block that is a cell-count multiple (PQ, PQ + 1,
    2 PQ, 3 PQ, 4 PQ and 5 PQ / 2 = 2 PQ * MAM) is mapped in one pass."""
    src = P.src
    a = src.index('\ndef sinTabZ : List (ℤ × ℤ) := ') + 1
    b = src.index('\n', src.index('theorem pvCheck_AM : pvCheck (')) + 1
    head, body = src[a:b].split('\n', 1)
    newhead = 'def sinTabZ : List (ℤ × ℤ) := [' + ', '.join('(%d, %d)' % t for t in tab) + ']'
    old = int(re.search(r'^ tabOk && allQ termOk (\d+) && decide', body, re.M).group(1))
    n = 0
    if old != PQ:
        assert old % 2 == 0 and PQ % 2 == 0
        mp = {old: PQ, old + 1: PQ + 1, 2 * old: 2 * PQ, 3 * old: 3 * PQ, 4 * old: 4 * PQ, 5 * old // 2: 5 * PQ // 2}
        pat = r'(?<![0-9A-Za-z_])(%s)(?![0-9])' % '|'.join(map(str, sorted(mp, reverse=True)))
        body, n = re.subn(pat, lambda m: str(mp[int(m.group(1))]), body)
    P.src = src[:a] + newhead + '\n' + body + src[b:]
    P.log.append(('sinTabZ', 1, int(newhead != head)))
    P.log.append(('pvCheck cell count %d -> %d' % (old, PQ), n, n))


def num(x):
    """regex for a literal integer x, not part of a longer number."""
    return r'(?<![0-9])' + re.escape(str(x)) + r'(?![0-9])'


def read_window(src):
    m = re.search(r'^def cAMn : ℕ → ℤ\n((?: \| \d+ => -?\d+\n)+) \| _ => 0\n', src, re.M)
    d = {int(a): int(b) for a, b in re.findall(r'\| (\d+) => (-?\d+)', m.group(1))}
    assert max(d) <= NH
    return [d.get(j, 0) for j in range(NH + 1)]


def read_weights(P):
    m = re.search(r'\(\((\d+) / 10{40} - \((\d+) : ℝ\) / (\d+)\) / \(1 - \((\d+) : ℝ\) / (\d+)\)\)\n\s*= (\d+) / (\d+) := by norm_num', P.src)
    hw, bn, bd, cn, cd, kn, kd = map(int, m.groups())
    return Fr(bn, bd), Fr(cn, cd), (kn, kd)


def patch(src, K, kappa_old=None):
    P = Patcher(src)
    c = K['cAMn']
    P.sub(r'^def cAMn : ℕ → ℤ\n(?: \| \d+ => -?\d+\n)+ \| _ => 0\n', lambda m: cAMn_block(c), 1, 'cAMn')
    P.sub(r'^def CE : List \(ℕ × ℕ × Bool\) :=\n(?:.*\n){3}', lambda m: ce_block(c), 1, 'CE')
    P.sub(r'^def CJ \(j : ℕ\) : ℕ × Bool :=\n match j with\n(?:.*\n){3}', lambda m: cj_block(c), 1, 'CJ')
    P.sub(r'^ let a := \(farJ n k XL XU XL2 XU2 .*$', lambda m: far_line(c), 1, 'FA')
    patch_pv(P, K['pv_cells'], K['sintab'])     # before the Lipschitz literal, which shares the block
    # structural sanity: the file must already be in 16-harmonic form
    for pat in [r'def vAM \(s : ℝ\) : ℝ := ∑ j ∈ Finset\.range %d,' % (NH + 1),
                r'Nat\.ble c\.k %d$' % (2 * NH), r'sumQ \(termU i\) %d \+' % (NH + 1),
                r'theorem CJ_val \{j : ℕ\} \(h1 : 1 ≤ j\) \(h2 : j ≤ %d\)' % NH]:
        P.get('(' + pat + ')')

    # literals keyed by their declarations; old values read from the primary site
    S_old = P.get(r'∑ j ∈ Finset\.range %d, \|\(cAM \(j \+ 1\) : ℝ\)\| ≤ (\d+) / 1000000000' % NH)
    edge_old = P.get(r'AMW\.pAM s ≤ (\d+) / 1000000000')
    core_old = P.get(r'theorem vAM_ge_core \{s : ℝ\} \(hs : \|s\| ≤ 1 / 2\) : (\d+ / \d+) ≤ vAM s')
    coreM_old = P.get(r'theorem hW_core_ge \(hL : 0 < L\) \{u : ℝ\} \(hu : \|u\| ≤ L / 2\) : (\d+ / \d+) ≤ hW L u')
    hw_old = P.get(r'theorem HW_ge : \((\d+) / 10 \^ 40 : ℝ\) ≤ HW')
    on_old, oe_old = E9 + int(S_old), E9 + int(edge_old)
    assert on_old != oe_old
    # two-phase swap of the 1 + S and 1 + edge literals (they share a context)
    P.sub(num(on_old) + r' / 1000000000', '\0ON\0', 3, '_placeholder')
    P.sub(num(oe_old) + r' / 1000000000', '\0OE\0', 3, '_placeholder')
    P.sub('\0ON\0', '%d / 1000000000' % (E9 + K['S']), 3, 'profile_upper 1 + sum|c|')
    P.sub('\0OE\0', '%d / 1000000000' % (E9 + K['edge_num']), 3, 'profile_upper_edge 1 + edge')
    P.log[-2:] = [(w, n, ch if new != old else 0) for (w, n, ch), new, old in
                  zip(P.log[-2:], (E9 + K['S'], E9 + K['edge_num']), (on_old, oe_old))]

    P.sub(r'(∑ j ∈ Finset\.range %d, \|\(cAM \(j \+ 1\) : ℝ\)\| ≤ )\d+( / 1000000000)' % NH, r'\g<1>%d\2' % K['S'], 1, 'sum_abs_cAM_succ')
    P.sub(r'(theorem abs_pAM_le \(s : ℝ\) : \|pAM s\| ≤ )\d+( / 1000000000)', r'\g<1>%d\2' % K['S'], 1, 'abs_pAM_le')
    P.sub(r'(theorem vAM_zero : vAM 0 = )\d+( / 10 \^ 9)', r'\g<1>%d\2' % K['v0'], 1, 'vAM_zero')
    P.sub(re.escape(core_old) + r'(?= ≤ vAM s)', fr(K['core']), 1, 'vAM_ge_core')
    P.sub(r'(\(by norm_num : \(0 : ℝ\) ≤ )' + re.escape(core_old) + r'\)', r'\g<1>%s)' % fr(K['core']), 1, 'vAM_ge_core consumer')
    P.sub(r'(?<![0-9])' + re.escape(coreM_old) + r'(?![0-9])', fr(K['core_M']), 7, 'core / MAM')
    P.sub(r'(theorem abs_vAMd_le \(s : ℝ\) : \|vAMd s\| ≤ ).*?( := by)', r'\g<1>%s\2' % fr(K['d1lit']), 1, 'abs_vAMd_le')
    P.sub(r'(theorem abs_vAMdd_le \(s : ℝ\) : \|vAMdd s\| ≤ )\d+( := by)', r'\g<1>%d\2' % K['d2lit'], 1, 'abs_vAMdd_le')
    P.sub(r'(sumQ \(termU i\) %d \+ )\d+( / \d+)' % (NH + 1), r'\g<1>%d\2' % K['d2lit'], 1, 'cellU')
    P.sub(r'(vAMd y ≤ vAMd x \+ )\d+( \* \|y - x\|)', r'\g<1>%d\2' % K['d2lit'], 1, 'vAMd_lipschitz')
    P.sub(r'(\(f := vAMd\) \(s := Set\.univ\) \(C := )\d+\)', r'\g<1>%d)' % K['d2lit'], 1, 'vAMd_lipschitz C')
    P.sub(r'(theorem pvCheck_AM : pvCheck \().*?(\) = true)', r'\g<1>%s\2' % fr(K['rho']), 1, 'pvCheck_AM')
    P.sub(r'(theorem profile_AM : Profile \(fun s => vAM s / MAM\) \(1 / 10\) )\(.*?\) \(.*?\) \(.*?\)( where)',
          r'\g<1>(%s) (%s) (%s)\2' % (fr(K['A1']), fr(K['A2']), fr(K['rho'])), 1, 'profile_AM')
    P.sub(r'(def cAMW \(ϱ : ℝ → ℝ\) : ℝ := cMod ϱ ).*$',
          r'\g<1>(%s) (%s + 2 * (%s) ^ 2)' % (fr(K['A1']), fr(K['A2']), fr(K['A1'])), 1, 'cAMW')
    r0, r02 = fr(K['r0']), fr(K['r0'] ** 2)
    P.sub(r'(theorem vAM_zero_div_le : vAM 0 / MAM ≤ ).*?( := by)', r'\g<1>%s\2' % r02, 1, 'vAM_zero_div_le')
    P.sub(r'(have h0 : Real\.sqrt \(vAM 0 / MAM\) ≤ ).*?( := by)', r'\g<1>%s\2' % r0, 1, 'budget sqrt bound')
    P.sub(r'(rw \[show \().*?( : ℝ\) = Real\.sqrt \().*?(\) by)', r'\g<1>%s\g<2>%s\3' % (r0, r02), 1, 'budget sqrt rewrite')
    P.sub(r'(rw \[show \().*?( : ℝ\) = \().*?(\) \^ 2 by norm_num, Real\.sqrt_sq)', r'\g<1>%s\g<2>%s\3' % (r02, r0), 1, 'budget square')
    P.sub(r'(AMW\.pAM s ≤ )\d+( / 1000000000)', r'\g<1>%d\2' % K['edge_num'], 1, 'pAM_le_edge')
    P.sub(r'(\|\(AMW\.cAM \(n \+ 1\) : ℝ\)\| \* bTs n ≤ )\d+( / 1000000000)', r'\g<1>%d\2' % K['corr_num'], 1, 'correction_abs_le')
    P.sub(num(hw_old), str(K['hw']), None, 'H_W floor')
    if kappa_old is not None and 'kappa' in K:
        kn, kd = kappa_old
        P.sub(num(kn) + r' / ' + num(kd), '%d / %d' % (K['kappa'].numerator, K['kappa'].denominator), None, 'kappa')
    return P


def changed_ok(P, src):
    return '\0' not in P.src


def window_from_json(path):
    d = json.load(open(path))
    if isinstance(d, list):
        return [int(x) for x in d]
    if 'cAMn' in d:
        return [int(x) for x in d['cAMn']]
    xf = d['xfree']
    assert len(xf) == NH, len(xf)
    return [E9] + [int(round(x * E9)) for x in xf]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('lean')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--window')
    ap.add_argument('--report')
    ap.add_argument('--pv-cells', type=int, help='force the pvCheck cell count (default: smallest of 128, 256, 512 that passes)')
    ap.add_argument('--replay', action='store_true', help='run replay.py --only decide pv win on the output')
    a = ap.parse_args()
    src = open(a.lean, encoding='utf-8').read()
    c = window_from_json(a.window) if a.window else read_window(src)
    cells = [a.pv_cells] if a.pv_cells else [128, 256, 512]
    P0 = Patcher(src)
    B, cfl, kappa_old = read_weights(P0)
    K, checks = compute(c, cells, B, cfl)
    P = patch(src, K, kappa_old)
    open(a.out, 'w', encoding='utf-8').write(P.src)
    print('window numerators:', c)
    for k in ['S', 'v0', 'core', 'core_M', 'd1', 'd1lit', 'A1', 'd2', 'd2lit', 'A2', 'pv_cells', 'pv_value', 'rho', 'r0',
              'edge', 'edge_num', 'corr', 'corr_num', 'hw', 'margin_core', 'margin_edge', 'kappa']:
        v = K[k]
        print('  %-11s %s%s' % (k, fr(v) if isinstance(v, (Fr, int)) else v,
                                '  (%.12g)' % float(v) if isinstance(v, Fr) and v.denominator != 1 else ''))
    print('side conditions:')
    bad = [k for k, v in checks.items() if not v]
    for k, v in checks.items():
        print('  %-62s %s' % (k, 'ok' if v else 'FAILS'))
    if not changed_ok(P, src):
        raise SystemExit('internal: placeholder left in output')
    changed = [(w, n, ch) for w, n, ch in P.log if ch and not w.startswith('_')]
    print('patched sites (what, matches, changed):', changed if changed else 'none changed')
    print('file changed:', P.src != src)
    if a.report:
        rep = dict(window=c, constants={k: (str(v) if isinstance(v, Fr) else v) for k, v in K.items() if k != 'sintab'},
                   checks=checks, failing=bad, changed_sites=changed, file_changed=P.src != src)
        json.dump(rep, open(a.report, 'w'), indent=1)
    if a.replay:
        r = subprocess.run([sys.executable, '-I', REPLAY, a.out, '--only', 'decide', 'pv', 'win', '--workers', '1'],
                           capture_output=True, text=True)
        print(r.stdout[-3000:], r.stderr[-2000:])
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
