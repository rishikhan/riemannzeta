"""Window literals of the Lean source: computed values and the text substitutions.

Each substitution names the declaration it touches; `patch_window` fails loudly when a
pattern does not match exactly once, so a change in the base file cannot pass silently.
"""
import math
import re
from fractions import Fraction as Fr

OLD = [1000000000, 14062605, -16219933, 5836910, 6519832, -927202, 4453864, -6483270, 2875651,
       -5999111, 5547809, -3302075, 3100000]
COSU = Fr(760244597075630151253547198623274394617584, 10 ** 42)
R2 = Fr(707106781186547524400844362104849039284835, 10 ** 42)
SINL = Fr(649636939080062444129478616044121910899027, 10 ** 42)
PIU = Fr(31415926535897932384626433832795028841972, 10 ** 40)


def hw_floor(c):
    """floor(10^40 * floor_numeric's right side) for numerators c (over 1e9)."""
    pam = sum(Fr(c[n + 1], 10 ** 9) ** 2 * (Fr(1, 2) - 1 / (4 * PIU ** 2 * (n + 1) ** 2)) for n in range(12))
    e = Fr(3, 2) - COSU / (2 * R2 * SINL) - pam / (2 * SINL ** 2)
    return math.floor(e * 10 ** 40)


def edge_const(c):
    """pAM_le_edge right side (exact), as computed by its norm_num."""
    return sum(Fr((-1) ** j * c[j], 10 ** 9) + max(Fr(0), Fr(-((-1) ** j) * c[j], 10 ** 9)) * 2 * Fr(31416, 10000) ** 2 * j * j / 400
               for j in range(1, 13))


def bts(n):
    return Fr(17, 37) if n == 0 else Fr(17, 20) / (Fr(157, 50) * ((n + 1) ** 2 - Fr(289, 400)))


def corr_const(c):
    return sum(Fr(abs(c[n + 1]), 10 ** 9) * bts(n) for n in range(12))


def ceil9(x):
    """Smallest k / 1e9 >= x, as the integer k."""
    return math.ceil(x * 10 ** 9)


def values(c):
    S = sum(abs(x) for x in c[1:])
    d1 = Fr(3, 2) + Fr(63, 10) * Fr(sum(abs(c[j]) * j for j in range(1, 13)), 10 ** 9)
    d2 = 2 + Fr(397, 10) * Fr(sum(abs(c[j]) * j * j for j in range(1, 13)), 10 ** 9)
    return dict(S=S, v0=sum(c), d1=d1, d2=d2, edge=edge_const(c), corr=corr_const(c), hw=hw_floor(c),
                core=Fr(3, 4) - Fr(S, 10 ** 9))


def subn(src, old, new, what, n):
    pat = re.compile(r'(?<![0-9])' + re.escape(old))
    k = len(pat.findall(src))
    if k != n:
        raise ValueError('%s: %d matches (want %d) for %r' % (what, k, n, old[:80]))
    return pat.sub(lambda m: new, src)


def sub1(src, old, new, what):
    return subn(src, old, new, what, 1)


def far_line(c):
    e = '⟨0, 0, 0, 0⟩'
    for j in range(1, 13):
        flag = 'true' if (-((-1) ** j) * c[j]) > 0 else 'false'
        e = '(farJ n k XL XU XL2 XU2 %s %d %d %s)' % (e, j, abs(c[j]), flag)
    return ' let a := %s' % e


def ce_block(c):
    items = ['(%d, %d, %s)' % (j, abs(c[j]), 'true' if (-((-1) ** j) * c[j]) > 0 else 'false') for j in range(1, 13)]
    return ' [' + ', '.join(items[:5]) + ',\n  ' + ', '.join(items[5:10]) + ',\n  ' + ', '.join(items[10:]) + ']'


def cj_block(c):
    items = ['| %d => (%d, %s)' % (j, abs(c[j]), 'true' if c[j] < 0 else 'false') for j in range(1, 13)]
    return ' ' + ' '.join(items[:4]) + '\n ' + ' '.join(items[4:8]) + '\n ' + ' '.join(items[8:]) + ' | _ => (0, false)'


def patch_window(src, c, consts):
    """consts: dict with chosen literals: core (Fraction), core625, d1lit, a1, d2lit, a2, rho,
    edge_num, corr_num.  Returns the patched source."""
    old = values(OLD)
    new = values(c)
    # cAMn
    blk_old = 'def cAMn : ℕ → ℤ\n' + ''.join(' | %d => %d\n' % (j, v) for j, v in enumerate(OLD))
    blk_new = 'def cAMn : ℕ → ℤ\n' + ''.join(' | %d => %d\n' % (j, v) for j, v in enumerate(c))
    src = sub1(src, blk_old, blk_new, 'cAMn')
    # CE, CJ, FA
    src = sub1(src, far_line(OLD), far_line(c), 'FA')
    src = sub1(src, 'def CE : List (ℕ × ℕ × Bool) :=\n' + ce_block(OLD), 'def CE : List (ℕ × ℕ × Bool) :=\n' + ce_block(c), 'CE')
    src = sub1(src, 'def CJ (j : ℕ) : ℕ × Bool :=\n match j with\n' + cj_block(OLD), 'def CJ (j : ℕ) : ℕ × Bool :=\n match j with\n' + cj_block(c), 'CJ')
    # sum |c_j| (sum_abs_cAM_succ, abs_pAM_le)
    src = subn(src, '%d / 1000000000' % old['S'], '%d / 1000000000' % new['S'], 'sum|c|', 2)
    src = sub1(src, 'theorem vAM_zero : vAM 0 = %d / 10 ^ 9' % old['v0'], 'theorem vAM_zero : vAM 0 = %d / 10 ^ 9' % new['v0'], 'vAM_zero')
    # core lower bound (vAM_ge_core, hW_core_ge and consumers)
    core, core625 = consts['core'], consts['core625']
    src = sub1(src, 'theorem vAM_ge_core {s : ℝ} (hs : |s| ≤ 1 / 2) : 337 / 500 ≤ vAM s', 'theorem vAM_ge_core {s : ℝ} (hs : |s| ≤ 1 / 2) : %s ≤ vAM s' % core, 'vAM_ge_core')
    src = sub1(src, '(by norm_num : (0 : ℝ) ≤ 337 / 500)', '(by norm_num : (0 : ℝ) ≤ %s)' % core, 'core consumer')
    src = subn(src, '337 / 625', core625, 'hW_core_ge', 7)
    # derivative bounds and profile constants
    src = sub1(src, 'theorem abs_vAMd_le (s : ℝ) : |vAMd s| ≤ 39 / 10', 'theorem abs_vAMd_le (s : ℝ) : |vAMd s| ≤ %s' % consts['d1lit'], 'abs_vAMd_le')
    src = sub1(src, 'theorem abs_vAMdd_le (s : ℝ) : |vAMdd s| ≤ 114', 'theorem abs_vAMdd_le (s : ℝ) : |vAMdd s| ≤ %s' % consts['d2lit'], 'abs_vAMdd_le')
    src = sub1(src, 'def cellU (i : ℕ) : ℚ := sumQ (termU i) 13 + 114 / 512', 'def cellU (i : ℕ) : ℚ := sumQ (termU i) 13 + %s / 512' % consts['d2lit'], 'cellU')
    src = sub1(src, 'theorem vAMd_lipschitz (x y : ℝ) : vAMd y ≤ vAMd x + 114 * |y - x| := by\n have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := vAMd) (s := Set.univ) (C := 114)',
               'theorem vAMd_lipschitz (x y : ℝ) : vAMd y ≤ vAMd x + %s * |y - x| := by\n have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := vAMd) (s := Set.univ) (C := %s)' % (consts['d2lit'], consts['d2lit']), 'lipschitz')
    src = sub1(src, 'theorem pvCheck_AM : pvCheck (9 / 200) = true', 'theorem pvCheck_AM : pvCheck (%s) = true' % consts['rho'], 'pvCheck')
    src = sub1(src, 'theorem profile_AM : Profile (fun s => vAM s / MAM) (1 / 10) (78 / 25) (456 / 5) (9 / 200) where',
               'theorem profile_AM : Profile (fun s => vAM s / MAM) (1 / 10) (%s) (%s) (%s) where' % (consts['a1'], consts['a2'], consts['rho']), 'profile_AM')
    src = sub1(src, 'def cAMW (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (78 / 25) (456 / 5 + 2 * (78 / 25) ^ 2)',
               'def cAMW (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (%s) (%s + 2 * (%s) ^ 2)' % (consts['a1'], consts['a2'], consts['a1']), 'cAMW')
    # matching / pinching constants
    on = 1000000000 + old['S']
    src = subn(src, '%d / 1000000000' % on, '%d / 1000000000' % (1000000000 + new['S']), 'profile_upper', 3)
    src = sub1(src, 'AMW.pAM s ≤ 9577405 / 1000000000', 'AMW.pAM s ≤ %d / 1000000000' % consts['edge_num'], 'pAM_le_edge')
    src = subn(src, '1009577405 / 1000000000', '%d / 1000000000' % (1000000000 + consts['edge_num']), 'profile_upper_edge', 3)
    src = sub1(src, '|(AMW.cAM (n + 1) : ℝ)| * bTs n ≤ 8249086 / 1000000000', '|(AMW.cAM (n + 1) : ℝ)| * bTs n ≤ %d / 1000000000' % consts['corr_num'], 'correction_abs_le')
    return src
