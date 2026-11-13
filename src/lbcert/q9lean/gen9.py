#!/usr/bin/env python3
"""Assemble a Q-gap Solution.lean from v3 (Q = 8), a window-patched base and a Q-gap model.

    python gen9.py BASE.lean MODEL.pkl PTS.pkl OUT.lean --trees T.pkl [T.pkl ...]
                   [--roots 0,7,...] [--test] [--no-half] [--cut-leaves N] [--date D]

BASE is v3 (q9lean/work/w16_v3.lean, a file derived from attempt-031, after a structural edit to 16 window
harmonics) with the window already patched by w16/regen_window.py from the window JSON.  The script replaces:

* the instance module (geninst.py, Q gaps, attempt-032's half-space multiplier row);
* inserts attempt-032's generic half-space module PCellHalf (Samuel Lavery's team, Apache-2.0)
  before the instance module, with its section comment kept verbatim;
* the data module: pyramids, REG, PTT (anchors of the included trees), COV/SMAX, root trees,
  run / cert;
* the reflection step (PC9XA_G_rev, PC9XA_half, PC9XA_cert_full), the RiemannFail weights
  (WCert (Q+1)), Opeth.AMFinal and the candidate kappa literal.

--test: only the trees passed are walked (a root subset).  `cert` and everything after it then
take one hypothesis `hm : AMW.Cert.PC9XAData.MissOK`: every root box is covered.  The included
roots are still proved by `decide +kernel` and used in run's case split; the missing ones come
from hm.  This is a compile test of the code, not a certificate.
"""
import argparse
import hashlib
import itertools
import os
import pickle
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(LB, 'gen'))
sys.path.insert(0, os.path.join(LB, 'q9'))
sys.path.insert(0, os.path.join(LB, 'q9hs'))
import geninst                                  # noqa: E402
import emit                                     # noqa: E402

A032 = os.environ.get('A032', os.path.join(HERE, '..', '..', '..', 'third_party', 'attempt-032', 'Solution.lean'))
A032_SHA = '9f4af56ebc9014fdf938da887cf7d2c51eb08a20203ac7d5524a62740b65bfa2'
SA = 8388608000000000000000000000000
W40 = 1099511627776


def half_module():
    raw = open(A032, 'rb').read()
    assert hashlib.sha256(raw).hexdigest() == A032_SHA, 'attempt-032 source changed'
    src = raw.decode()
    a = src.index('section\n\n/-! ###### the reflection half-space as a multiplier row (am-cert, 2026-10-22)')
    b = src.index('-- SWAP BEGIN certificate', a)
    body = src[a:b]
    note = ('/- The section below (module PCellHalf) is taken from Samuel Lavery\'s riemannzeta.fun attempt-032\n'
            '(Solution.lean sha256 %s), which carries the same\n'
            'Copyright (c) 2026 Samuel Lavery (github: samlavery) Apache-2.0 notice as this file (kept verbatim\n'
            'in the header). Unchanged. -/\n' % A032_SHA)
    return note + body


def gvars(Q, p='x'):
    return ' '.join('%s%d' % (p, r) for r in range(Q))


# ------------------------------------------------------------------ data module
def emit_cover(Q, NP, COV, SMAX):
    L = ['def COV : List (List (ℕ × ℕ × Bool)) := [']
    for r, segs in enumerate(COV):
        txt = '[' + ', '.join('(%d, %d, %s)' % (a, b, 'true' if t else 'false') for a, b, t in segs) + ']'
        L.append('  ' + txt + (',' if r < len(COV) - 1 else ']'))
    L.append('def SMAX (r : ℕ) : ℕ := [%s].getD r 0' % ', '.join(str(x) for x in SMAX))
    iv = gvars(Q, 'i')
    L.append('def RC (%s : ℕ) : Cl := rootCl %d %d %d COV (fun r => [%s].getD r 0)'
             % (iv, Q, NP, W40, ', '.join('i%d' % r for r in range(Q))))
    L.append('theorem rcOf {%s : ℕ} (wb : ℕ → ℕ) (e : ℕ) (h : U (walk TOP BK TOPD BKD PT REG wb 128 1) (ofCl (RC %s) 0) = e)' % (iv, iv))
    L.append('    (he : e ≠ 0) : Covered (RC %s) := by' % iv)
    L.append('  have h\' := covered_of_walk lbS lbD ptS hR wb 128 e _ h he')
    L.append('  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h\'')
    L.append('theorem rcOfC {%s : ℕ} (wb : ℕ → ℕ) (cuts : List (ℕ × St × ℕ)) (hc : CutsOk cuts) (e : ℕ)' % iv)
    L.append('    (h : U (walkCutR TOP BK TOPD BKD PT REG wb cuts 128 1) (ofCl (RC %s) 0) = e) (he : e ≠ 0) : Covered (RC %s) := by' % (iv, iv))
    L.append('  have h\' := covered_of_walkCutR lbS lbD ptS hR wb hc 128 1 e _ h he')
    L.append('  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h\'')
    return L


def emit_root(r, idx, stream, nbits, end, cuts, extra, literals=True):
    """literals=False: the WL<r>_<j> definitions come from the E-format command zfE."""
    L = []
    blocks = emit.wl_blocks(stream, nbits, extra=extra)
    keys = [j for j in range(len(blocks)) if blocks[j]]
    for j in keys:
        if literals:
            L.append('def WL%d_%d : ℕ := %s' % (r, j, emit.zf(blocks[j])))
    L += emit.dispatch('WL%d' % r, keys, lambda j: 'WL%d_%d' % (r, j), 'WL%d' % r)
    L.append('def WD%d : ℕ → ℕ := rdw WL%d' % (r, r))
    ix = ' '.join(str(i) for i in idx)
    if not cuts:
        L.append('theorem rc%d : Covered (RC %s) := rcOf WD%d %d (by decide +kernel) (by decide)' % (r, ix, r, end))
        return L
    entries = []
    for k, (pos, flat, ce) in enumerate(cuts, 1):
        nm = 'CS%d_%d' % (r, k)
        L.append('def %s : St := %s' % (nm, emit.st_text(flat)))
        L.append('theorem wcs%d_%d : U (walkC TOP BK TOPD BKD PT REG WD%d 128 %d) %s = %d := by' % (r, k, r, pos, nm, ce))
        L.append('  decide +kernel')
        L.append('theorem ccs%d_%d : Covered (toCl %s) :=' % (r, k, nm))
        L.append('  covered_of_walkCP lbS lbD ptS hR WD%d 128 %d %d _ wcs%d_%d (by decide)' % (r, pos, ce, r, k))
        entries.append('(%d, %s, %d)' % (pos, nm, ce))
    oks = 'cutsOk_nil'
    for k in range(len(cuts), 0, -1):
        oks = '(cutsOk_cons ccs%d_%d %s)' % (r, k, oks)
    L.append('def CUTS%d : List (ℕ × St × ℕ) := [%s]' % (r, ', '.join(entries)))
    L.append('theorem rc%d : Covered (RC %s) := rcOfC WD%d CUTS%d %s %d (by decide +kernel) (by decide)' % (r, ix, r, r, oks, end))
    return L


def emit_run(Q, NP, lens, have, test):
    """have: set of root numbers with an rc theorem; test: the rest come from hm."""
    L = []
    iv = gvars(Q, 'i')
    if test:
        L.append('def MissOK : Prop := ∀ %s : ℕ, Covered (RC %s)' % (iv, iv))
    hs = ' '.join('(h%d : i%d < %d)' % (r, r, n) for r, n in enumerate(lens))
    hm = '(hm : MissOK) ' if test else ''
    L.append('theorem runQ %s(%s : ℕ) %s :' % (hm, iv, hs))
    L.append('    Covered (rootCl %d %d %d COV (fun r => [%s].getD r 0)) := by' % (Q, NP, W40, ', '.join('i%d' % r for r in range(Q))))
    L.append('  match %s, %s with' % (', '.join('i%d' % r for r in range(Q)), ', '.join('h%d' % r for r in range(Q))))
    for k, idx in enumerate(itertools.product(*[range(n) for n in lens])):
        pat = ', '.join(str(i) for i in idx)
        rhs = ('rc%d' % k) if k in have else ('hm %s' % ' '.join(str(i) for i in idx))
        L.append('  | %s, %s => exact %s' % (pat, ', '.join(['_'] * Q), rhs))
    for r, n in enumerate(lens):
        pat = ['_'] * Q
        pat[r] = 'i + %d' % n
        hp = ['_'] * Q
        hp[r] = 'hi'
        L.append('  | %s, %s => exact absurd hi (by omega)' % (', '.join(pat), ', '.join(hp)))
    L.append('theorem run %s: ∀ idx : ℕ → ℕ, (∀ r < %d, idx r < (badOf (COV.getD r [])).length) → Covered (rootCl %d %d %d COV idx) := by'
             % (hm, Q, Q, NP, W40))
    L.append('  intro idx h')
    L.append('  rw [rootCl_congr (idx\' := fun r => [%s].getD r 0) (fun r hr => by interval_cases r <;> rfl)]'
             % ', '.join('idx %d' % r for r in range(Q)))
    for r, n in enumerate(lens):
        L.append('  have l%d : (badOf (COV.getD %d [])).length = %d := rfl' % (r, r, n))
    L.append('  exact runQ %s%s %s' % ('hm ' if test else '', ' '.join(['_'] * Q),
                                       ' '.join('(l%d ▸ h %d (by norm_num))' % (r, r) for r in range(Q))))
    L.append('theorem cert %s: ∀ g : ℕ → ℝ, (∀ r < %d, 0 ≤ g r) → Pg cN %d BS TS g :=' % (hm, Q, Q))
    L.append('  cert_of COV SMAX (by decide) (by decide +kernel) (by decide) %d (by decide) (run%s)' % (W40, ' hm' if test else ''))
    return L


# ------------------------------------------------------------------ after the data module
def emit_tail(Q, BS, AW, cN, hw, kappa, test):
    """AMW.Cert reflection step, RiemannFail weights, as text replacing v3's."""
    n = Q + 1
    hmb = '(hm : PC9XAData.MissOK) ' if test else ''
    hma = ' hm' if test else ''
    x = gvars(Q, 'x')
    y = gvars(Q, 'y')
    xr = ' '.join('x%d' % r for r in reversed(range(Q)))
    L = []
    L.append('noncomputable section')
    L.append('namespace AMW.Cert')
    L.append('theorem PC9XA_G_rev (%s : ℝ) : PC9XA.G %s = PC9XA.G %s := by' % (x, xr, x))
    L.append('  unfold PC9XA.G; ring_nf')
    L.append('theorem PC9XA_half %s(%s : ℝ) %s :' % (hmb, y, ' '.join('(h%d : 0 ≤ y%d)' % (r, r) for r in range(Q))))
    L.append('    (PC9XA.cN : ℝ) / PC9XA.SA ≤ PC9XA.G %s ∨ y%d < y0 := by' % (y, Q - 1))
    L.append('  have hg : ∀ r < %d, 0 ≤ (fun r => [%s].getD r 0) r := by' % (Q, ', '.join('y%d' % r for r in range(Q))))
    L.append('    intro r hr; interval_cases r <;> simpa')
    L.append('  rcases PC9XAData.cert%s _ hg with h | h' % hma)
    L.append('  · left')
    L.append('    rw [PC9XA.Fg_G] at h')
    L.append('    rw [div_le_iff₀ (by norm_num [PC9XA.SA])]')
    L.append('    linarith')
    L.append('  · right; simpa using h')
    L.append('theorem PC9XA_cert_full %s: ∀ %s : ℝ, %s →' % (hmb, x, ' → '.join('0 ≤ x%d' % r for r in range(Q))))
    L.append('    (PC9XA.cN : ℝ) / PC9XA.SA ≤ PC9XA.G %s := by' % x)
    L.append('  intro %s %s' % (x, ' '.join('h%d' % r for r in range(Q))))
    L.append('  rcases lt_or_ge x%d x0 with hlt | hle' % (Q - 1))
    L.append('  · rcases PC9XA_half%s %s %s with h | h' % (hma, xr, ' '.join('h%d' % r for r in reversed(range(Q)))))
    L.append('    · rw [← PC9XA_G_rev]; exact h')
    L.append('    · exact absurd h (not_lt.mpr hlt.le)')
    L.append('  · rcases PC9XA_half%s %s %s with h | h' % (hma, x, ' '.join('h%d' % r for r in range(Q))))
    L.append('    · exact h')
    L.append('    · exact absurd h (not_lt.mpr hle)')
    L.append('end AMW.Cert')
    L.append('end')
    L.append('noncomputable section')
    L.append('namespace RiemannFail')
    L.append('open Filter')
    L.append('open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW')
    Wn = 'W%d' % n
    aW, bW = 'aW%d' % n, 'bW%d' % n
    L += fin_sum("sum_univ_pts'", 'Fin %d' % n, n)
    L += fin_sum('sumG', 'Fin %d' % Q, Q)
    L += fin_sum('sumQ', 'Fin (%d - 1)' % n, Q)
    AWL = ', '.join(str(AW.get((i, j), 0) if i < j else 0) for i in range(n) for j in range(n))
    L.append('def AWL : List ℕ := [%s]' % AWL)
    L.append('def BWL : List ℕ := [%s]' % ', '.join(str(b) for b in BS))
    L.append('def %s (i j : Fin %d) : ℝ := (AWL.getD (%d * i + j) 0 : ℝ) / %d' % (aW, n, n, SA))
    L.append('def %s (r : Fin %d) : ℝ := (BWL.getD r 0 : ℝ) / %d' % (bW, Q, SA))
    L.append('def %s : WCert %d := ⟨%s, %s⟩' % (Wn, n, aW, bW))
    B = sum(BS)
    L.append('theorem %s_B : %s.B = (%d : ℝ) / %d := by' % (Wn, Wn, B, SA))
    L.append('  show (∑ r : Fin %d, %s r) = _' % (Q, bW))
    L.append('  simp only [sumG, %s, BWL]; norm_num' % bW)
    L.append('theorem %s_capacity : ∀ s : ℕ, %s.spanMass s ≤ 2 := by' % (Wn, Wn))
    L.append('  intro s')
    L.append('  unfold WCert.spanMass %s' % Wn)
    L.append('  rcases lt_or_ge s %d with hs | hs' % n)
    L.append("  · interval_cases s <;> simp (config := { decide := true }) only [sum_univ_pts', %s, AWL, Fin.isValue, if_true, if_false] <;> norm_num" % aW)
    L.append('  · have h0 : ∀ i j : Fin %d, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by' % n)
    L.append('      intro i j ⟨_, h⟩')
    L.append('      have := j.2')
    L.append('      omega')
    L.append('    simp only [h0, if_false, Finset.sum_const_zero]')
    L.append('    norm_num')
    L.append('theorem %s_adm : %s.Adm := ⟨fun _ _ => div_nonneg (Nat.cast_nonneg _) (by norm_num), fun _ => div_nonneg (Nat.cast_nonneg _) (by norm_num), %s_capacity⟩' % (Wn, Wn, Wn))
    L.append('theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl')
    gl = ' '.join('(g %d)' % r for r in range(Q))
    L.append('theorem Fw_%s (g : Fin (%d - 1) → ℝ) :' % (Wn, n))
    L.append('    Fw %s g = AMW.Cert.PC9XA.G %s := by' % (Wn, gl))
    L.append('  show (∑ r : Fin %d, %s r * g r) + (∑ i : Fin %d, ∑ j : Fin %d, if (i : ℕ) < (j : ℕ) then %s i j * wfun (ptsN %d g j - ptsN %d g i) else 0) = _'
             % (Q, bW, n, n, aW, n, n))
    L.append('  unfold AMW.Cert.PC9XA.G ptsN')
    L.append("  simp only [cert_wfun_eq, sumQ, sumG, sum_univ_pts', Fin.isValue, %s, %s, AWL, BWL]" % (aW, bW))
    L.append('  norm_num [AMW.Cert.PC9XA.SA]')
    L.append('  try ring')
    L.append('theorem cert_AM %s: ∀ g : Fin %d → ℝ, (∀ i, 0 ≤ g i) → ((%d : ℝ) / %d) ≤ Fw %s g := by' % (hmb.replace('PC9XAData', 'AMW.Cert.PC9XAData'), Q, cN, SA, Wn))
    L.append('  intro g hg')
    L.append('  rw [Fw_%s]' % Wn)
    L.append('  have h := AMW.Cert.PC9XA_cert_full%s %s %s' % (hma, gl, ' '.join('(hg %d)' % r for r in range(Q))))
    L.append('  simp only [AMW.Cert.PC9XA.cN, AMW.Cert.PC9XA.SA] at h')
    L.append('  push_cast at h')
    L.append('  exact h')
    L.append('end RiemannFail')
    L.append('end')
    return L


def fin_sum(name, typ, k):
    """private lemma: a sum over `typ` (k elements, k >= 8) written out"""
    rhs = ' + '.join('f %d' % i for i in range(k))
    return ['private theorem %s {M : Type*} [AddCommMonoid M] (f : %s → M) :' % (name, typ),
            '    ∑ i, f i = %s := by' % rhs,
            '  rw [%s]; rfl' % ', '.join(['Fin.sum_univ_castSucc'] * (k - 8) + ['Fin.sum_univ_eight'])]


def emit_final(Q, B, cN, hw, kappa, test):
    n = Q + 1
    Wn = 'W%d' % n
    hmb = '(hm : AMW.Cert.PC9XAData.MissOK) ' if test else ''
    hma = ' hm' if test else ''
    kn, kd = kappa.numerator, kappa.denominator
    L = ['namespace Opeth.AMFinal']
    for nm, rng, rng2, fn in [('actual_dyadic', 'T (2 * T)', 'T (2 * T)', 'actual_dyadic'),
                              ('actual_cumulative', '0 T', '0 T', 'actual_cumulative')]:
        L.append('theorem %s %s:' % (nm, hmb))
        L.append('    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,')
        L.append('      ((%d / %d : ℝ) - ε) * (Zeta23.Ncount %s : ℝ) ≤' % (kn, kd, rng))
        L.append('        Zeta23.N0star %s := by' % rng2)
        L.append('  have h := OpethN.ActualDefect.%s (by norm_num : 2 ≤ %d) RiemannFail.%s RiemannFail.%s_adm' % (fn, n, Wn, Wn))
        L.append('    (by norm_num : (0 : ℝ) < %d / %d) (by norm_num) RiemannFail.%s_B (RiemannFail.cert_AM%s)' % (cN, SA, Wn, hma))
        L.append('  have e : ((%d / 10000000000000000000000000000000000000000 - (%d : ℝ) / %d) / (1 - (%d : ℝ) / %d))' % (hw, B, SA, cN, SA))
        L.append('      = %d / %d := by norm_num' % (kn, kd))
        L.append('  simpa only [e] using h')
    L.append('end Opeth.AMFinal')
    return L


def replace_between(src, a, b, new, inclusive_b=False):
    i = src.index(a)
    j = src.index(b, i)
    if inclusive_b:
        j += len(b)
    return src[:i] + new + src[j:]


PTN_TEXT = open(os.path.join(HERE, '..', 'q9ptt', 'lean', 'PTN.lean')).read() if os.path.exists(
    os.path.join(HERE, '..', 'q9ptt', 'lean', 'PTN.lean')) else ''
# the table checker that ptOkTN replaces (removed with --ptn --prune)
PTD_NAMES = {'ptlD', 'ptlOkD', 'ptlD_sound', 'ptGetD', 'ptOkTD', 'ptTD_sound', 'ptOkTD_nd'}


def emit_ptn(words, parts):
    """emit.emit_ptt for entries that carry the piece count n − 1 above bit 140, checked by ptOkTN (q9ptt)."""
    L = emit.emit_ptt(words, parts)
    out = []
    for l in L:
        l = l.replace('ptOkTD REG TOP BK TOPD BKD 32 4 ', 'ptOkTN REG TOP BK TOPD BKD 4 ').replace('ptOkTD_nd', 'ptOkTN_nd')
        l = l.replace('def PT (x : ℕ) : ℕ := ptGetD PTT x', 'def PT (x : ℕ) : ℕ := ptGetN PTT x')
        l = l.replace('ptTD_sound (n := 32) (csh := 4) lbS lbD hR (by decide) PTT PTT_ok', 'ptTN_sound (csh := 4) lbS lbD hR PTT PTT_ok')
        assert 'ptOkTD' not in l and 'ptGetD' not in l and 'ptTD_sound' not in l, l[:100]
        out.append(l)
    return out


PTB_TEXT = open(os.path.join(HERE, '..', 'q9leaf2', 'lean', 'PTB.lean')).read() if os.path.exists(
    os.path.join(HERE, '..', 'q9leaf2', 'lean', 'PTB.lean')) else ''


def emit_ptb(words, parts):
    """emit_ptn's table as a balanced tree over the points (q9leaf2/lean/PTB.lean): the same parts and zfPTTN
    payloads, written as `zfPTB` (inductive PTB); top keys are the first x of each right part (1024 j)."""
    sys.path.insert(0, os.path.join(LB, 'pack'))
    import codec
    out = []
    for l in emit_ptn(words, parts):
        m = re.fullmatch(r'def (PTT_\d+) : PTrD := (.+)', l)
        if m:
            E = []
            for j, lst in re.findall(r'\.lf (\d+) \[([^\]]*)\]', m[2]):
                for o, w in re.findall(r'\((\d+), (0x[0-9a-f]+)\)', lst):
                    E.append((int(j) * 1024 + int(o), int(w, 16)))
            assert codec.ptt_tree_text(E) == m[2], m[1]
            out.append('def %s : PTB := zfPTB "%s"' % (m[1], codec.ptt_encode_n(E)))
            continue
        if l.startswith('def PTT : PTrD := '):
            l = re.sub(r'\.nd (\d+) ', lambda mo: '.nd %d ' % (1024 * int(mo[1])), l.replace(': PTrD :=', ': PTB :='))
        l = l.replace('ptOkTN REG TOP BK TOPD BKD 4 ', 'ptOkB REG TOP BK TOPD BKD 4 ').replace('ptOkTN_nd', 'ptOkB_nd')
        l = l.replace('def PT (x : ℕ) : ℕ := ptGetN PTT x', 'def PT (x : ℕ) : ℕ := ptGetB PTT x')
        l = l.replace('ptTN_sound (csh := 4) lbS lbD hR PTT PTT_ok', 'ptTB_sound (csh := 4) lbS lbD hR PTT PTT_ok')
        assert 'ptOkTN' not in l and 'ptGetN' not in l and 'ptTN_sound' not in l and 'PTrD' not in l, l[:100]
        out.append(l)
    return out


class Walker:
    """Walk one tree (HSChecker rules) collecting leaves, anchors and subtree sizes."""

    def __init__(self, C, bits):
        self.C, self.bits = C, bits
        self.leaves = 0
        self.nodes = []
        self.anchors = set()
        self.slack = None

    def walk(self, pos, s, depth=0):
        from core import children
        C = self.C
        w = self.bits(pos)
        if w & 1:
            q, left, right = children(C, s, (w >> 1) & 63, (w >> 7) & 7)
            n0 = self.leaves
            pp = self.walk(pos + 10, left, depth + 1)
            e = self.walk(pp, right, depth + 1)
            self.nodes.append((pos, s, e, self.leaves - n0, depth))
            return e
        if s[1][C.M.Q - 1] < s[0][0]:
            return pos + 1
        if getattr(C, 'zfmt', False):
            an = set()
            n, sl, nt = C.zleaf(w >> 1, s, anchors=an)
            assert n, ('leaf fails', pos)
            self.leaves += 1
            self.slack = sl if self.slack is None else min(self.slack, sl)
            self.anchors |= an
            return pos + 1 + n
        if getattr(C, 'kfmt', False):
            rngs, terms, PS, n = C.kdecode(w >> 1, s)
            if not C.adjlam:
                terms = C.F.lam_rule(s, rngs, terms, PS)
            ok, lhs, rhs, inner, okt = C.F.fcheck(s, rngs, terms, PS)
            assert ok, ('leaf fails', pos)
            self.leaves += 1
            sl = rhs - lhs
            self.slack = sl if self.slack is None else min(self.slack, sl)
            for (a, lam, p, r) in terms:
                if a in (1, 2, 3):
                    self.anchors.add(p)
                if a == 3:
                    self.anchors.add(r)
            return pos + 1 + n
        n, det = C.mleaf(w >> 2, s, ((w >> 1) & 1) == 1, want_detail=True)
        assert n, ('leaf fails', pos)
        self.leaves += 1
        sl = det['rhs'] - det['lhs']
        self.slack = sl if self.slack is None else min(self.slack, sl)
        for (a, lam, p, r) in det['terms']:
            if a in (1, 2, 3):
                self.anchors.add(p)
            if a == 3:
                self.anchors.add(r)
        return pos + 2 + n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('base')
    ap.add_argument('model')
    ap.add_argument('pts')
    ap.add_argument('out')
    ap.add_argument('--trees', nargs='+', required=True)
    ap.add_argument('--roots', default='')
    ap.add_argument('--test', action='store_true')
    ap.add_argument('--no-half', action='store_true')
    ap.add_argument('--cut-leaves', type=int, default=0)
    ap.add_argument('--date', default='2026-10-23')
    ap.add_argument('--profile', action='store_true', help='set_option profiler true on the root theorems (timing)')
    ap.add_argument('--opt', action='append', default=[], help='instance option key=value (share, novar, yrow, gsplit; '
                    'leaf2=OPTS: q9leaf2 leaf-check levers; ptb: balanced point tree, needs --ptn)')
    ap.add_argument('--eformat', default=None, help='base-93 E-format text (q9enc design A) of all roots: WL literals decoded by zfE')
    ap.add_argument('--kfmt', action='store_true', help='trees are K-format streams (q9enc/kformat.py)')
    ap.add_argument('--prune', default=None, help='remove the declarations named in this file (dead/removed.names)')
    ap.add_argument('--pack', action='store_true', help='pack PTT and pyramid literals (src/lbcert/pack)')
    ap.add_argument('--inst', default=None, help='use this instance module text instead of geninst')
    ap.add_argument('--ptn', default=None, help='point table rows "x word n" (q9ptt): per-point piece count n, '
                    'checked by ptOkTN (q9ptt/lean/PTN.lean) in place of ptOkTD')
    a = ap.parse_args()
    import qgen
    import hs as HS
    M = pickle.load(open(a.model, 'rb'))
    pts = pickle.load(open(a.pts, 'rb'))
    Q, NP = M.Q, M.NP
    half = not a.no_half
    C = HS.HSChecker(M) if half else qgen.QChecker(M)
    if a.kfmt:
        sys.path.insert(0, os.path.join(LB, 'q9enc'))
        import kformat
        C = kformat.KChecker(M)
        C.kfmt = True
        C.adjlam = 'adjlam' in a.opt          # adjacent lambdas stored in the stream (no checker rule)
    if 'sparse' in a.opt:
        # sparse leaf check (src/lbcert/q9sparse): trees are Z-format streams, checked by its exact mirror
        sys.path.insert(0, os.path.join(LB, 'q9sparse'))
        import zfmt
        C = zfmt.ZChecker(M)
        C.zfmt = True
        C.adjlam = True

    ptn = None
    if a.ptn:
        ptn = {}
        for l in open(a.ptn):
            x, w, n = map(int, l.split())
            ptn[x] = (w, n)
        pts = {x: w for x, (w, n) in ptn.items()}

    def ptf(x):
        w = pts.get(x, 0)
        return C.pwD(x, w) if w else 0
    C.PT = ptf
    trees = {}
    for f in a.trees:
        trees.update(pickle.load(open(f, 'rb')))
    lens = [len([s for s in M.COV[r] if not s[2]]) for r in range(Q)]
    roots = list(itertools.product(*[range(n) for n in lens]))
    want = sorted(trees) if not a.roots else [int(x) for x in a.roots.split(',')]
    if not a.test:
        assert sorted(trees) == list(range(len(roots))), 'missing roots (use --test)'
    from core import root_state
    walks = {}
    for k in want:
        T = trees[k]
        assert tuple(T['idx']) == roots[k]
        bv = T['bits']
        W = Walker(C, lambda pos, bv=bv: (bv >> pos) & M.WMASK)
        e = W.walk(1, root_state(C, roots[k]))
        assert e == T['nbits'], (k, e, T['nbits'])
        walks[k] = W
        print('root', k, roots[k], 'leaves', W.leaves, 'bits', T['nbits'])
    cN = M.cN
    words = {}
    for W in walks.values():
        for x in W.anchors:
            words[x] = pts[x]
    print('tangent points', len(words))
    # ---------------- data module
    BK = {j: v for j, v in M.BKv.items() if v}
    BKD = {j: v for j, v in M.BKDv.items() if v}
    pre = emit.emit_pyramids(M.TOP, BK, M.TOPD, BKD) + emit.emit_reg(M.REG)
    if ptn is not None:
        assert set(words) <= set(ptn), 'leaves use points outside the table'
        assert len(words) == len(ptn), ('table points not used by any leaf', len(ptn) - len(words))
        pre += (emit_ptb if 'ptb' in a.opt else emit_ptn)({x: w + ((ptn[x][1] - 1) << 140) for x, w in words.items()},
                                                          parts=min(32, max(1, len({x // 1024 for x in words}))))
    else:
        pre += emit.emit_ptt(words, parts=min(32, max(1, len({x // 1024 for x in words}))))
    pre += emit_cover(Q, NP, M.COV, M.SMAX)
    if a.eformat:
        assert want == list(range(len(roots))), 'zfE decodes every root in order'
        sys.path.insert(0, os.path.join(HERE, 'edec'))
        import gen_edec
        pre.append(gen_edec.zfe_command(len(roots), open(a.eformat).read()))
    post = []
    extra = M.WMASK.bit_length()
    for k in want:
        T, W = trees[k], walks[k]
        cuts = []
        if a.cut_leaves and W.leaves > a.cut_leaves:
            rem = W.leaves
            chosen = []
            for (pos, s, e, cnt, d) in sorted([n for n in W.nodes if n[4] >= 1 and n[3] <= a.cut_leaves], key=lambda n: -n[3]):
                if rem <= a.cut_leaves:
                    break
                if any(not (e <= p0 or e0 <= pos) for (p0, e0) in chosen):
                    continue
                chosen.append((pos, e))
                cuts.append((pos, C.st_flat(s), e))
                rem -= cnt
            cuts.sort()
        rl = emit_root(k, roots[k], T['bits'], T['nbits'], T['nbits'], cuts, extra, literals=not a.eformat)
        if a.profile:
            rl = [('set_option profiler true in\n' + x) if x.startswith(('theorem rc', 'theorem wcs')) else x for x in rl]
        post += rl
    post += emit_run(Q, NP, lens, set(want), a.test)
    data = ['namespace AMW.Cert.PC9XAData',
            'open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC9XA',
            'set_option maxRecDepth 100000'] + pre + post + ['end AMW.Cert.PC9XAData']
    # ---------------- instance
    spec = dict(Q=Q, PR=M.PR, TS=M.TS, BS=M.BS, SL=M.SL, BND=M.BND, ADJ=M.ADJ, cN=cN, SIG=M.SIG, SA=SA,
                wmask_bits=M.WMASK.bit_length(), half=half, pb=NP.bit_length(), yfuel=M.YFUEL, TB=getattr(M, 'TBL', []))
    if a.kfmt:
        spec['kfmt'] = True
        spec['novar'] = True
    for kv in a.opt:
        k, _, v = kv.partition('=')
        spec[k] = int(v) if v.isdigit() else (v or True)
    inst = open(a.inst).read() if a.inst else geninst.Inst(spec).emit()
    src = open(a.base).read()
    i0 = src.index('-- SWAP BEGIN certificate')
    i1 = src.index('end AMW.Cert.PC9XA\nend\n', i0) + len('end AMW.Cert.PC9XA\nend\n')
    src = src[:i0] + (half_module() if half else '') + inst + src[i1:]
    if a.eformat:
        sys.path.insert(0, os.path.join(HERE, 'edec'))
        import gen_edec
        if 'sparse' in a.opt:
            import edec_z
            dtext = edec_z.decoder_text(Q, M.WMASK.bit_length())
        else:
            dtext = gen_edec.decoder_text(Q, M.WMASK.bit_length(), adjlam=C.adjlam)
        tab = (PTB_TEXT if 'ptb' in a.opt else PTN_TEXT) if ptn is not None else ''
        data = ['end', dtext.rstrip('\n')] + ([tab.rstrip('\n')] if tab else []) + ['noncomputable section'] + data
    src = replace_between(src, 'namespace AMW.Cert.PC9XAData\n', 'end AMW.Cert.PC9XAData\n', '\n'.join(data) + '\n',
                          inclusive_b=True)
    # ---------------- tail: reflection step + RiemannFail (between the data module and SWAP END)
    AW = {(t[0], t[1]): t[2] for t in M.TS}
    hw = hw_from(src)
    B = sum(M.BS)
    kappa = (Fraction(hw, 10 ** 40) - Fraction(B, SA)) / (1 - Fraction(cN, SA))
    tail = emit_tail(Q, M.BS, AW, cN, hw, kappa, a.test)
    j0 = src.index('end AMW.Cert.PC9XAData\n') + len('end AMW.Cert.PC9XAData\n')
    j0 = src.index('end\n', j0) + len('end\n')
    j1 = src.index('-- SWAP END certificate')
    src = src[:j0] + '\n'.join(tail) + '\n' + src[j1:]
    fin = emit_final(Q, B, cN, hw, kappa, a.test)
    src = replace_between(src, 'namespace Opeth.AMFinal\n', 'end Opeth.AMFinal\n', '\n'.join(fin) + '\n', inclusive_b=True)
    # candidate kappa (exact literal in am_export_candidate_exact)
    src = re.sub(r'(candidateKappa = \()\d+ / \d+( : ℝ\))', lambda m: '%s%d / %d%s' % (m.group(1), kappa.numerator, kappa.denominator, m.group(2)), src, count=1)
    if a.test:
        # the three candidate theorems take the hypothesis through Opeth.AMFinal
        src = src.replace('  exact Opeth.AMFinal.actual_dyadic\n', '  exact Opeth.AMFinal.actual_dyadic hm\n', 1)
        src = src.replace('  exact Opeth.AMFinal.actual_cumulative\n', '  exact Opeth.AMFinal.actual_cumulative hm\n', 1)
        src = src.replace('theorem candidate_critical_line_bound :\n', 'theorem candidate_critical_line_bound (hm : AMW.Cert.PC9XAData.MissOK) :\n', 1)
        src = src.replace('theorem candidate_critical_line_bound_cumulative :\n',
                          'theorem candidate_critical_line_bound_cumulative (hm : AMW.Cert.PC9XAData.MissOK) :\n', 1)
    extra_changes = []
    if a.prune:
        sys.path.insert(0, os.path.join(HERE, 'dead'))
        import prune_names
        names = set(x for x in open(a.prune).read().split() if x)
        if ptn is not None:
            names |= PTD_NAMES
        if 'leaf2' in ''.join(a.opt) and any(kv.startswith('leaf2=') and 'y' in kv[6:] for kv in a.opt):
            names |= {'ystepH', 'ydecH', 'ystepH_ok', 'ydecH_ok'}
        src, missing = prune_names.prune(src, names)
        assert not missing, missing
        extra_changes.append('* Declarations outside the dependency closure of the three scored theorems removed (%d, among them the'
                             % len(names))
        extra_changes.append('  anchor-variance layer and the multiplier soundness without the half-space row); notices kept.')
    if a.pack:
        sys.path.insert(0, os.path.join(LB, 'pack'))
        import pack as PK
        from expand import expand
        packed = PK.pack(src)
        dec = open(os.path.join(LB, 'pack', 'Decoder.lean')).read()
        anchor = '    Lean.Macro.throwErrorAt payload message\nset_option Elab.async false\n'
        assert packed.count(anchor) == 1
        packed = packed.replace(anchor, anchor.replace('set_option', dec + 'set_option'))
        assert expand(packed) == src.replace(anchor, anchor.replace('set_option', dec + 'set_option')), 'pack: expansion differs'
        src = packed
        extra_changes.append('* The tangent point table and the pyramids are written as zfPTT / zfPyr payloads (namespace ZeroForgePack),')
        extra_changes.append('  decoded at elaboration time into the same declarations.')
    a.extra_changes = extra_changes
    a.wmask = M.WMASK.bit_length()
    src = add_changes(src, a, Q, NP, len(M.TS), half, cN, B, hw, kappa, len(words), sum(W.leaves for W in walks.values()), want)
    open(a.out, 'w').write(src)
    print('kappa', kappa.numerator, kappa.denominator, float(kappa), 'c', cN / SA, 'B', B / SA)
    print('bytes', len(src.encode()))


def hw_from(src):
    m = re.search(r'\((\d{38,}) / 10000000000000000000000000000000000000000 - B\)', src)
    return int(m.group(1))


def add_changes(src, a, Q, NP, NT, half, cN, B, hw, kappa, npts, nleaves, roots):
    """Replace our earlier Changes blocks (v3's and the 16-harmonic one) by one block."""
    for head in ('/-\nChanges (Apache-2.0 §4(b)), 2026-10-23, by Rishi Khan.',
                 '/-\nChanges (Apache-2.0 §4(b)), by Rishi Khan, 2026-10-23.'):
        while head in src:
            i = src.index(head)
            j = src.index('-/\n', i) + 3
            src = src[:i] + src[j:]
    lines = [
        '/-',
        'Changes (Apache-2.0 §4(b)), %s, by Rishi Khan. This file is derived from Samuel Lavery\'s riemannzeta.fun' % a.date,
        'attempt-031 (Solution.lean sha256 0adbf8e04b4bc3db5dae886dfe003dc4fb9b9acd6d998a43f2a5603cba515f32, Apache-2.0); every',
        'copyright, license and attribution notice above and below is retained verbatim. Changes:',
        '* The window family has 17 terms, v(s) = cos(√2 s) + ∑_{j=1}^{16} c_j cos(2πj s): the window-dependent declarations',
        '  are written for 16 harmonics (sums over Finset.range 17 / 16, the cell evaluator\'s CE, CJ, FA with 16 entries and',
        '  near-term range k ≤ 32, the positive-variation sum over 17 terms at 256 cells), with every window literal and the',
        '  H_W floor (HW_ge %d/10⁴⁰) recomputed for the window.' % hw,
        '* Ten-point certificate (Q = %d gaps): the instance module PC9XA is regenerated for %d gaps, %d pairs and %d' % (Q, Q, NP, NT),
        '  weighted terms (a state of %d naturals, closure splits, multiplier records with a %d-bit pair index, the' % (2 * Q + 2 * NP + 1, NP.bit_length()),
        '  leaf check, the reflection test U_%d < L_0, a %d-bit walk-word mask); the root cover, the reflection step' % (Q - 1, a.wmask),
        '  and the weights (WCert %d) follow Q.' % (Q + 1),
    ]
    if half:
        lines.append('* The reflection half-space g_0 ≤ g_%d as one more multiplier row (c = %d): module PCellHalf and its' % (Q - 1, NP))
        lines.append('  instance part (MulOKH, yhalf, ystepH, ydecH) from Samuel Lavery\'s attempt-032 (am-cert, 2026-10-22,')
        lines.append('  Apache-2.0); the instance part regenerated for %d gaps.' % Q)
    lines.append('* Weights b_r, a_ij (integers over 2²³·10²⁴, palindromic), floor c = %d/%d,' % (cN, SA))
    lines.append('  B = %d/%d, tables and trees from a new generator;' % (B, SA))
    lines.append('  κ = (H_W⁻ − B)/(1 − c) = %d/%d.' % (kappa.numerator, kappa.denominator))
    lines += getattr(a, 'extra_changes', [])
    if a.test:
        lines.append('* COMPILE TEST ONLY, not a certificate: roots %s are walked (%d leaves, %d tangent points);' % (','.join(map(str, roots)), nleaves, npts))
        lines.append('  every other root box is a hypothesis (AMW.Cert.PC9XAData.MissOK) of cert and of the theorems after it.')
    lines.append('-/')
    txt = '\n'.join(lines) + '\n'
    i = src.index('import ChallengeDeps\n')
    return src[:i] + txt + src[i:]

if __name__ == '__main__':
    main()
