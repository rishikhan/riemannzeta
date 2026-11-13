"""Lean text of the sparse leaf check Z with the q9leaf2 levers, with soundness proofs (no sorry).

Same top-level names and statements as q9sparse/zlean.text_m (TZ, tzG, zchk, zfin, mleafZ, mleafZ_ok, ...), so
leafStep, walk and the root theorems are unchanged. Levers (opts, a string of letters):

  y  multiplier step: Cp / Cm read A_c, B_c and x_c from the state through a 36-way dispatch (ycs) instead of
     sumR / List.getD on toCl s (yupdS2, ystepH2, ydecH2; equal to yupdS for c < 36 by rfl)
  p  packed gap sums: the record is (CVP, CN, VP, VN); a listed term adds a·2e9·mw and a·sl to the 256-bit lanes
     i .. j-1 of VP / VN by one multiplication with lmask i j = sum_{i <= r < j} 2^(256 r); a term with
     mw >= 2049 or sl > 2^43 fails the leaf, which keeps every lane below 2^256; zchk reads
     V_r = KVz + lane_r VP - lane_r VN
  b  small bodies: tzv dispatches to one definition per kind (tzk0 .. tzk4) and tzG's listed path is its own
     definition (tzL), so a step instantiates only the code it runs

    text(Q, TS, BS, pt='f', opts='yp', dev=False) -> str
dev=True: the names are suffixed with 2 and the unchanged term lemmas (tzv, tzv_cov, ...) are not emitted, for
a development file that imports the current Solution's Pre.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'q9sparse'))
import zlean                                  # noqa: E402

B = 'Bool.rec (motive := fun _ => ℕ)'
LANE = 256
PAIRS9 = [(i, j) for i in range(9) for j in range(i + 2, 10)]


def nest_add0(xs):
    e = '0'
    for x in xs:
        e = '(Nat.add %s %s)' % (e, x)
    return e


# ------------------------------------------------------------------ y: multiplier step
def ycs_text(pairs):
    def tree(lo, hi):
        if hi - lo == 1:
            i, j = pairs[lo]
            return '(k s.A%d%d s.B%d%d (x%d%d s))' % (i, j, i, j, i, j)
        mid = (lo + hi) // 2
        return '(Bool.rec (motive := fun _ => YA) %s %s (Nat.blt c %d))' % (tree(mid, hi), tree(lo, mid), mid)
    return ('/-- the multiplier pair `c`\'s state bounds `A_c`, `B_c` and the sum `x_c` of its gaps\' lower ends -/\n'
            'def ycs (c : ℕ) (s : St) (k : ℕ → ℕ → ℕ → YA) : YA :=\n  %s\n' % tree(0, len(pairs)))


def y_text(Q):
    pairs = [(i, j) for i in range(Q) for j in range(i + 2, Q + 1)]
    P = ', '.join('(Nat.add y.P%d (Nat.mul Ylo (ind (inr %d (pI PR c) (pJ PR c)))))' % (r, r) for r in range(Q))
    S = ', '.join('(Nat.add y.S%d (Nat.mul Yhi (ind (inr %d (pI PR c) (pJ PR c)))))' % (r, r) for r in range(Q))
    t = ycs_text(pairs)
    t += ('/-- `yupdS` with `Cp`, `Cm` from `ycs` (no `sumR` / `List.getD` on `toCl s`) -/\n'
          'def yupdS2 (c : ℕ) (s : St) (Ylo Yhi : ℕ) (y : YA) (o\' : ℕ) : YA :=\n'
          '  ycs c s fun a b x => ⟨o\', %s, %s,\n'
          '    (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub x a))) (Nat.mul Yhi (Nat.sub b x))),\n'
          '    (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub a x))) (Nat.mul Yhi (Nat.sub x b)))⟩\n' % (P, S))
    t += ('theorem yupdS2_eq (s : St) (Ylo Yhi : ℕ) (y : YA) (o\' : ℕ) : ∀ c < %d, yupdS2 c s Ylo Yhi y o\' = yupdS c s Ylo Yhi y o\' := by\n'
          '  intro c hc\n  interval_cases c <;> rfl\n'
          'theorem yupdSH2_ok (s : St) (y : YA) (h : MulOKH s y) (c : ℕ) (hc : c < %d) (Ylo Yhi o\' : ℕ) :\n'
          '    MulOKH s (yupdS2 c s Ylo Yhi y o\') := by\n'
          '  rw [yupdS2_eq s Ylo Yhi y o\' c hc]; exact yupdSH_ok s y h c hc Ylo Yhi o\'\n' % (len(pairs), len(pairs)))
    return t


def y_step_text(src_ystep, src_ydec):
    """ystepH2 / ydecH2 (copies of the instance module's ystepH / ydecH on yupdS2) and their proofs"""
    st = src_ystep.replace('def ystepH ', 'def ystepH2 ').replace('(yupdS c s', '(yupdS2 c s')
    assert 'yupdS2' in st
    dc = src_ydec.replace('def ydecH ', 'def ydecH2 ').replace('ystepH s qb w ih', 'ystepH2 s qb w ih')
    assert 'ystepH2' in dc
    pf = ('theorem ystepH2_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOKH s y → MulOKH s (ih y)) (y : YA) (h : MulOKH s y) :\n'
          '    MulOKH s (ystepH2 s qb w ih y) := by\n'
          '  unfold ystepH2\n  simp only [forceT_eq]\n'
          '  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => brec_dep (fun _ => h) fun _ => hih _ (yhalf_ok s y h _ _))\n'
          '    fun hc => hih _ (yupdSH2_ok s y h _ (Nat.blt_eq.mp hc) _ _ _)\n'
          'theorem ydecH2_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOKH s y → MulOKH s (ydecH2 s qb w fuel y)\n'
          '  | 0, _, h => h\n'
          '  | n + 1, y, h => ystepH2_ok s qb w (ydecH2_ok s qb w n) y h\n')
    return st + dc + pf


# ------------------------------------------------------------------ p: packed gap sums
LANES = r'''/-- 2^256 − 1: the lane mask of the packed gap sums -/
def LMSK : ℕ := @LMSK@
/-- `Σ_{i ≤ r < j} 2^(256 r)`: one in each lane `i .. j − 1` -/
def lmask (i j : ℕ) : ℕ := Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 256 (Nat.sub j i))) 1) LMSK) (Nat.mul 256 i)
/-- lane `r` (bits 256 r .. 256 r + 255) of `x` -/
def lane (r x : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 256 r)) LMSK
theorem LMSK_eq : LMSK = 2 ^ 256 - 1 := by unfold LMSK; norm_num
theorem lane_eq (r x : ℕ) : lane r x = x / (2 ^ 256) ^ r % 2 ^ 256 := by
  unfold lane
  rw [LMSK_eq]
  show (x >>> (256 * r)) &&& (2 ^ 256 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
theorem lmask_eq {i j : ℕ} : lmask i j = ∑ r ∈ Finset.range (j - i), (2 ^ 256) ^ (i + r) := by
  unfold lmask
  show ((1 <<< (256 * (j - i)) - 1) / LMSK) <<< (256 * i) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, LMSK_eq, pow_mul, pow_mul, ← Nat.geomSum_eq (by norm_num) (j - i),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [← pow_add, add_comm]
/-- the base-2^256 digits of `Σ_{r < n} f r 2^(256 r)` are the `f r` when each is below 2^256 -/
theorem digit_sum : ∀ (n : ℕ) (f : ℕ → ℕ), (∀ r < n, f r < 2 ^ 256) →
    ∀ k < n, (∑ r ∈ Finset.range n, f r * (2 ^ 256) ^ r) / (2 ^ 256) ^ k % 2 ^ 256 = f k
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, hf, k, hk => by
    have hpos : (0 : ℕ) < 2 ^ 256 := by positivity
    have hsum : ∑ r ∈ Finset.range (n + 1), f r * (2 ^ 256) ^ r
        = f 0 + 2 ^ 256 * ∑ r ∈ Finset.range n, f (r + 1) * (2 ^ 256) ^ r := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one, add_comm]
      congr 1
      apply Finset.sum_congr rfl; intro r _; ring
    rw [hsum]
    have h0 := hf 0 (Nat.succ_pos n)
    rcases k with _ | k
    · simp only [pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    · have hd : (f 0 + 2 ^ 256 * ∑ r ∈ Finset.range n, f (r + 1) * (2 ^ 256) ^ r) / 2 ^ 256
          = ∑ r ∈ Finset.range n, f (r + 1) * (2 ^ 256) ^ r := by
        rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt h0, zero_add]
      rw [show ((2 : ℕ) ^ 256) ^ (k + 1) = 2 ^ 256 * (2 ^ 256) ^ k from pow_succ' _ _, ← Nat.div_div_eq_div_mul, hd]
      exact digit_sum n (fun r => f (r + 1)) (fun r hr => hf (r + 1) (by omega)) k (by omega)
/-- `x` holds the lanes `f 0 .. f 8` -/
def LRep (x : ℕ) (f : ℕ → ℕ) : Prop := x = ∑ r ∈ Finset.range @Q@, f r * (2 ^ 256) ^ r
theorem lane_of_rep {x : ℕ} {f : ℕ → ℕ} (h : LRep x f) (hf : ∀ r < @Q@, f r < 2 ^ 256) : ∀ r < @Q@, lane r x = f r := by
  intro r hr
  rw [lane_eq, h]
  exact digit_sum @Q@ f hf r hr
theorem rep_zero : LRep 0 (fun _ => 0) := by simp [LRep]
theorem rep_add {x : ℕ} {f : ℕ → ℕ} (h : LRep x f) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ @Q@) (X : ℕ) :
    LRep (Nat.add x (Nat.mul X (lmask i j))) (fun r => f r + if i ≤ r ∧ r < j then X else 0) := by
  unfold LRep at h ⊢
  have hm : lmask i j = ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then 1 else 0) * (2 ^ 256) ^ r := by
    rw [lmask_eq]
    rw [show ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then 1 else 0) * (2 ^ 256) ^ r
        = ∑ r ∈ Finset.Ico i j, (2 ^ 256) ^ r from ?_]
    · rw [Finset.sum_Ico_eq_sum_range]
    · simp only [ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  show x + X * lmask i j = _
  rw [h, hm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro r _
  by_cases hc : i ≤ r ∧ r < j <;> simp [hc, add_mul]
theorem tA_lt : ∀ n < @NT@, tA TS n < 2 ^ 104 := by decide
'''

INV_P = r'''/-- the gaps' merged slope sums of a packed record (lane `r` of `VP` minus lane `r` of `VN`, offset by `KVz`) -/
def zv (t : TZ) (r : ℕ) : ℕ := Nat.sub (Nat.add KVz (lane r t.VP)) (lane r t.VN)
/-- the fold invariant after the first `N` terms: `VP`, `VN` hold lanes below `N·2^148`, lane `r` of `VN` minus lane `r`
of `VP` is at most `10⁹ D_r`, and the listed terms among the first `N` are bounded by `Σ_{n<N} a_n wfun` -/
def ZInv (s : St) (g : ℕ → ℝ) (N : ℕ) (t : TZ) : Prop :=
  ∃ P M : ℕ → ℕ, LRep t.VP P ∧ LRep t.VN M ∧ (∀ r < @Q@, P r ≤ N * 2 ^ 148 ∧ M r ≤ N * 2 ^ 148) ∧
  ∃ D : ℕ → ℝ, (∀ r < @Q@, ((M r : ℕ) : ℝ) - ((P r : ℕ) : ℝ) ≤ 1000000000 * D r) ∧
    (t.CVP : ℝ) + 327680000000000 * ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) - 10 * (t.CN : ℝ)
      ≤ 327680000000000 * 1024 * ∑ n ∈ Finset.range N, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
theorem ZInv_zero (s : St) (g : ℕ → ℝ) : ZInv s g 0 ⟨0, 0, 0, 0⟩ := by
  refine ⟨fun _ => 0, fun _ => 0, rep_zero, rep_zero, fun r _ => by simp, fun _ => 0, fun r _ => by simp, ?_⟩
  simp
/-- an unlisted term: its `a_n wfun ≥ 0` only loosens the bound -/
theorem ZInv_skip {s : St} {g : ℕ → ℝ} {n : ℕ} {t : TZ} (h : ZInv s g n t) : ZInv s g (n + 1) t := by
  obtain ⟨P, M, hP, hM, hb, D, h1, h2⟩ := h
  refine ⟨P, M, hP, hM, fun r hr => ?_, D, h1, ?_⟩
  · obtain ⟨b1, b2⟩ := hb r hr
    constructor <;> linarith
  rw [Finset.sum_range_succ (fun k => ((tA TS k : ℕ) : ℝ) * wfun (gsum g (tI TS k) (tJ TS k))) n]
  have : (0 : ℝ) ≤ ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)) := mul_nonneg (Nat.cast_nonneg _) (wfun_nonneg _)
  linarith
/-- a listed term: the per-term bound added to the invariant, its slope sums to the lanes of the gaps it spans -/
theorem ZInv_add {s : St} {g : ℕ → ℝ} {n i j a e0 : ℕ} {t : TZ} {mv cp cn sl mw : ℕ} (hn : n < TS.length)
    (hi : tI TS n = i) (hj : tJ TS n = j) (ha : tA TS n = a) (h0 : eL0 TS (toCl s) n = e0)
    (hinv : ZInv s g n t)
    (htb : ∃ D : ℝ, (sl : ℝ) - 2000000000 * (mw : ℝ) ≤ 1000000000 * D ∧
       32768 * (mv : ℝ) + 327680000000000 * (D * (gsum g i j - (e0 : ℝ) / 32768)) + 10 * (cp : ℝ) - 10 * (cn : ℝ)
         ≤ 327680000000000 * 1024 * wfun (gsum g i j))
    (hmw : mw < 2049) (hsl : sl < 8796093022209) :
    ZInv s g (n + 1) ⟨Nat.add t.CVP (Nat.mul a (Nat.add (Nat.mul 32768 mv) (Nat.mul 10 cp))), Nat.add t.CN (Nat.mul a cn),
      Nat.add t.VP (Nat.mul (Nat.mul a (Nat.mul 2000000000 mw)) (lmask i j)), Nat.add t.VN (Nat.mul (Nat.mul a sl) (lmask i j))⟩ := by
  obtain ⟨P, M, hP, hM, hb, D, hD1, hD2⟩ := hinv
  obtain ⟨Dn, hn1, hn2⟩ := htb
  obtain ⟨hij, hjQ, -⟩ := hTS n hn
  have hij' : i ≤ j := by rw [← hi, ← hj]; exact hij.le
  have hjQ' : j ≤ @Q@ := by rw [← hj]; exact hjQ
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hab : a < 2 ^ 104 := by rw [← ha]; exact tA_lt n hn
  have hX : a * (2000000000 * mw) ≤ 2 ^ 148 := by
    have h1 : 2000000000 * mw ≤ 17592186044416 := by omega
    calc a * (2000000000 * mw) ≤ 2 ^ 104 * 17592186044416 := Nat.mul_le_mul hab.le h1
      _ = 2 ^ 148 := by norm_num
  have hY : a * sl ≤ 2 ^ 148 := by
    have h1 : sl ≤ 17592186044416 := by omega
    calc a * sl ≤ 2 ^ 104 * 17592186044416 := Nat.mul_le_mul hab.le h1
      _ = 2 ^ 148 := by norm_num
  refine ⟨_, _, rep_add hP hij' hjQ' _, rep_add hM hij' hjQ' _, fun r hr => ?_,
    fun r => D r + if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0, fun r hr => ?_, ?_⟩
  · obtain ⟨b1, b2⟩ := hb r hr
    simp only [Nat.mul_eq]
    constructor <;> split_ifs <;> linarith
  · have := hD1 r hr
    simp only [Nat.mul_eq]
    split_ifs with hrr
    · push_cast
      nlinarith [mul_le_mul_of_nonneg_left hn1 ha0]
    · simp only [add_zero]; exact this
  · have hsp : ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
        = (a : ℝ) * (Dn * (gsum g i j - (e0 : ℝ) / 32768)) := by
      rw [← h0, ← hi, ← hj, span_eq (Q := @Q@) g hij.le hjQ, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      split_ifs <;> ring
    have e : ∑ r ∈ Finset.range @Q@, (D r + if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
        = ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
          + ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; ring
    dsimp only
    rw [e, hsp, Finset.sum_range_succ (fun k => ((tA TS k : ℕ) : ℝ) * wfun (gsum g (tI TS k) (tJ TS k))) n, ha, hi, hj]
    simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hn2 ha0]
/-- the invariant after all terms, in the form the final aggregation reads: lane sums exact (all lanes below 2^256) -/
def ZFin (s : St) (g : ℕ → ℝ) (t : TZ) : Prop :=
  ∃ D : ℕ → ℝ, (∀ r < @Q@, (KVz : ℝ) - ((zv t r : ℕ) : ℝ) ≤ 1000000000 * D r) ∧
    (t.CVP : ℝ) + 327680000000000 * ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) - 10 * (t.CN : ℝ)
      ≤ 327680000000000 * 1024 * ∑ n ∈ Finset.range @NT@, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
theorem zfin_of {s : St} {g : ℕ → ℝ} {t : TZ} (h : ZInv s g @NT@ t) : ZFin s g t := by
  obtain ⟨P, M, hP, hM, hb, D, hD1, hD2⟩ := h
  have hlt : ∀ r < @Q@, P r < 2 ^ 256 ∧ M r < 2 ^ 256 := by
    intro r hr; obtain ⟨b1, b2⟩ := hb r hr
    exact ⟨lt_of_le_of_lt b1 (by norm_num), lt_of_le_of_lt b2 (by norm_num)⟩
  have lP := lane_of_rep hP (fun r hr => (hlt r hr).1)
  have lM := lane_of_rep hM (fun r hr => (hlt r hr).2)
  refine ⟨D, fun r hr => ?_, hD2⟩
  have hz : (KVz : ℝ) + ((P r : ℕ) : ℝ) - ((M r : ℕ) : ℝ) ≤ ((zv t r : ℕ) : ℝ) := by
    have := natsub_ge (KVz + lane r t.VP) (lane r t.VN)
    have e : zv t r = KVz + lane r t.VP - lane r t.VN := rfl
    rw [e, lP r hr, lM r hr]
    rw [lP r hr, lM r hr] at this
    push_cast at this ⊢; linarith
  linarith [hD1 r hr]
'''

STEP_P = r'''theorem tzG_cov {top : ℕ} {bk : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x))
    {s : St} {g : ℕ → ℝ} (hg : InCell @Q@ PR (toCl s) g) {i j a eLx eUx e0x n m w o : ℕ} {t : TZ} {k : ℕ → TZ → ℕ} {Pr : Prop}
    (h : tzG top bk pb i j a eLx eUx e0x n m w o t k ≠ 0) (hn : n < TS.length)
    (hi : tI TS n = i) (hj : tJ TS n = j) (ha : tA TS n = a)
    (hL : eL TS (toCl s) n = eLx) (hU : eU TS (toCl s) n = eUx) (h0 : eL0 TS (toCl s) n = e0x)
    (hinv : ZInv s g n t) (hk : ∀ o' t', ZInv s g (n + 1) t' → k o' t' ≠ 0 → Pr) : Pr := by
  obtain ⟨hr0, hr1, hr2⟩ := term_range hPR hTS hg hn
  rw [hL, h0] at hr0
  rw [hL, hi, hj] at hr1
  rw [hU, hi, hj] at hr2
  unfold tzG at h
  cases hb : Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1
  · rw [hb] at h
    exact hk _ _ (ZInv_skip hinv) h
  · rw [hb] at h
    simp only [forceR_eq] at h
    refine tzv_cov hlb hpt hr0 (fun mv cp cn sl mw ok o' htb hk' => ?_) h
    cases hs : Nat.blt sl 8796093022209
    · rw [hs] at hk'; exact absurd rfl hk'
    cases hm : Nat.blt mw 2049
    · rw [hs, hm] at hk'; exact absurd rfl hk'
    cases hz : Nat.beq ok 0
    · rw [hs, hm, hz] at hk'
      have hok : ok ≠ 0 := fun e => by rw [e] at hz; exact absurd hz (by decide)
      exact hk _ _ (ZInv_add hn hi hj ha h0 hinv (htb hok _ hr1 hr2) (Nat.blt_eq.mp hm) (Nat.blt_eq.mp hs)) hk'
    · rw [hs, hm, hz] at hk'; exact absurd rfl hk'
'''


def p_kernel(Q, TS, BS, pt, t_tzv):
    """TZ (packed), tzv (as zlean), tzG, zchk, zfin"""
    L = []
    L.append('/-! ###### sparse leaf check Z: the leaf lists only its nonzero terms (presence mask), folded into accumulators ###### -/')
    L.append('structure TZ where\n  (CVP CN VP VN : ℕ)')
    L.append('/-- the offset of the merged per-gap slope sums (it keeps them from truncating; soundness does not need it) -/')
    L.append('def KVz : ℕ := %d' % (1 << 160))
    L.append(t_tzv.rstrip('\n'))
    return '\n'.join(L) + '\n'


def tzg_text(pt):
    return ('/-- term `n` of the chain: listed (mask bit `n`) -> decode, check and accumulate (lanes `i .. j − 1` of the packed\n'
            'slope sums); unlisted -> nothing -/\n'
            'def tzG (top : ℕ) (bk : ℕ → ℕ) (%s : ℕ → ℕ) (i j a eL eU e0 n m w o : ℕ) (t : TZ) (k : ℕ → TZ → ℕ) : ℕ :=\n'
            '  %s (k o t)\n    (forceR eL fun eL => forceR eU fun eU => forceR e0 fun e0 =>\n'
            '     tzv top bk %s (Nat.land (Nat.shiftRight w o) 7) w (Nat.add o 3) eL eU e0 fun mv cp cn sl mw ok o\' =>\n'
            '     %s (k o\' ⟨Nat.add t.CVP (Nat.mul a (Nat.add (Nat.mul 32768 mv) (Nat.mul 10 cp))), Nat.add t.CN (Nat.mul a cn),\n'
            '       Nat.add t.VP (Nat.mul (Nat.mul a (Nat.mul 2000000000 mw)) (lmask i j)), Nat.add t.VN (Nat.mul (Nat.mul a sl) (lmask i j))⟩) 0\n'
            '       (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) true (Nat.beq ok 0) (Nat.blt mw 2049))\n'
            '         (Nat.blt sl 8796093022209)))\n'
            '    (Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1)\n' % (pt, B, pt, B))


def zchk_text(Q, BS):
    BB = 'Bool.rec (motive := fun _ => Bool)'
    ng = nest_add0(['(Nat.mul (Nat.sub s.u%d s.l%d) (Nat.sub (Nat.add (zv t %d) y.P%d) (Nat.add (Nat.add (Nat.mul 1024000000000 %d) y.S%d) KVz)))'
                    % (r, r, r, r, BS[r], r) for r in range(Q)])
    bl = nest_add0(['(Nat.mul %d s.l%d)' % (BS[r], r) for r in range(Q)])
    box = 'true'
    for r in range(Q):
        box = '(%s false (Nat.ble s.l%d s.u%d) %s)' % (BB, r, r, box)
    chk = ('%s false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add t.CN y.Cp) %s)))\n'
           '      (Nat.add (Nat.add (Nat.mul 10240000000000 %s) t.CVP) (Nat.mul 10 y.Cm)))\n    %s' % (BB, ng, bl, box))
    return ('def zchk (s : St) (t : TZ) (y : YA) : Bool :=\n  ' + chk + '\n'
            'def zfin (s : St) (t : TZ) (y : YA) : ℕ := %s 0 y.o (zchk s t y)\n' % B)


def fin_text(Q, NT):
    """zfin_ok: zlean's SOUND_FIN_M with the invariant ZFin (packed lanes) in place of ZInv"""
    t = zlean.SOUND_FIN_M
    t = t.replace('(hinv : ZInv s g @NT@ t)', '(hinv : ZFin s g t)')
    rep = {'@Q@': str(Q), '@NT@': str(NT), '@KV@': 'KVz', '@PS@': ', '.join('y.P%d' % r for r in range(Q)),
           '@SS@': ', '.join('y.S%d' % r for r in range(Q))}
    for a, b in rep.items():
        t = t.replace(a, b)
    return t


def chain_text(Q, TS, pt, ydec):
    NT = len(TS)
    L = ['/-- the sparse leaf check: the mask, the chain over the %d terms, the multipliers, the final inequality -/' % NT]
    hdr = '(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (%s : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ' % pt
    L.append('def mleafZ %s :=' % hdr)
    L.append('  forceR (Nat.land w %d) fun m =>' % ((1 << NT) - 1))
    for n, (i, j, a, k) in enumerate(TS):
        rg = 's.l%d s.u%d s.l%d' % (i, i, i) if j - i == 1 else '(e%d%d s) (f%d%d s) (x%d%d s)' % (i, j, i, j, i, j)
        tin = '⟨0, 0, 0, 0⟩' if n == 0 else 't%d' % n
        oin = str(NT) if n == 0 else 'o%d' % n
        L.append('  tzG top bk %s %d %d a%d%d %s %d m w %s %s fun o%d t%d =>' % (pt, i, j, i, j, rg, n, oin, tin, n + 1, n + 1))
    L.append('  zfin s t%d (%s s 14 w 42 ⟨o%d, %s⟩)' % (NT, ydec, NT, ', '.join(['0'] * (2 * Q + 2))))
    imp = '{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}'
    L.append('theorem mleafZ_ok %s' % imp)
    L.append('    (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x)) (w : ℕ) (s : St)')
    L.append('    (h : mleafZ top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by')
    L.append('  intro g hg')
    L.append('  rcases lt_or_ge (g %d) (g 0) with hlt | hle' % (Q - 1))
    L.append('  · exact Or.inr hlt')
    L.append('  left')
    L.append('  unfold mleafZ at h')
    L.append('  rw [forceR_eq] at h')
    for n in range(NT):
        hin = '(ZInv_zero s g)' if n == 0 else 'hi'
        L.append('  refine tzG_cov hlb hpt hg h (n := %d) (by decide) rfl rfl rfl rfl rfl rfl %s fun _ _ hi h => ?_' % (n, hin))
    L.append('  exact zfin_ok hg hle (zfin_of hi) (%s_ok s 14 w 42 _ (MulOK_zeroH s _)) h' % ydec)
    return '\n'.join(L) + '\n'


DEVNAMES = ['TZ', 'KVz', 'LMSK', 'lmask', 'lane', 'LMSK_eq', 'lane_eq', 'lmask_eq', 'digit_sum', 'LRep', 'lane_of_rep', 'rep_zero',
            'rep_add', 'tA_lt', 'zv', 'ZInv', 'ZInv_zero', 'ZInv_skip', 'ZInv_add', 'ZFin', 'zfin_of', 'tzG', 'tzG_cov',
            'zchk', 'zfin', 'zu', 'zl', 'zp', 'zs', 'zchkG', 'zchk_eq', 'zfin_ok', 'mleafZ', 'mleafZ_ok']


B_UNFOLD = [
    ('        · -- z ≥ 4: lam × tangent, the kind-2 term without its constant part\n          rw [h2] at h\n', '          unfold tzk4 at h\n'),
    ('        · -- z = 2: (1024 − lam) lb + lam tangent\n          rw [h2] at h\n', '          unfold tzk2 at h\n'),
    ('      · -- z = 0: 1024 lb\n        rw [h0] at h\n', '        unfold tzk0 at h\n'),
    ('    · -- z = 3: (1024 − lam) tangent(p) + lam tangent(r)\n      rw [h3] at h\n', '      unfold tzk3 at h\n'),
    ('  · -- z = 1: 1024 tangent\n    rw [h1] at h\n', '    unfold tzk1 at h\n'),
]
TERMNAMES = ['TBnd', 'tbnd_of', 'ivIn_of2', 'brec_ok', 'mokI_0', 'mokI_1', 'mokI_2', 'mokI_3', 'z0_vals', 'z1_vals', 'z2_vals',
             'tzv_cov', 'tzv', 'tzL', 'tzk0', 'tzk1', 'tzk2', 'tzk3', 'tzk4']


def text(Q, TS, BS, pt='f', opts='yp', dev=False, src=None):
    """src: the current Solution text (for ystepH / ydecH when opts has y)"""
    NT = len(TS)
    assert 'p' in opts, 'only the packed variant is written here'
    base = zlean.text(Q, TS, BS, pt)
    i0 = base.index('/-- the values of one listed term')
    i1 = base.index('/-- the per-term bound')
    i2 = base.index('/-- the per-gap sums of a record')
    t_tzv = base[i0:i1]
    term = base[i1:i2].rstrip('\n')
    out = ''
    if 'y' in opts:
        lines = src.split('\n')
        out += y_text(Q) + y_step_text(defn(lines, 'ystepH'), defn(lines, 'ydecH'))
    tg = tzg_text(pt)
    step = STEP_P.replace('@Q@', str(Q))
    if 'b' in opts:
        sys.path.insert(0, HERE)
        import levers
        dv, dg = t_tzv[:t_tzv.index('def tzv ')], tg[:tg.index('def tzG ')]
        sb = levers.split_bodies(t_tzv[len(dv):], tg[len(dg):], '')
        k = sb.index('def tzL ')
        t_tzv, tg = dv + sb[:k], dg + sb[k:]
        for a, b in B_UNFOLD:
            assert term.count(a) == 1, a
            term = term.replace(a, a + b)
        a = '  · rw [hb] at h\n    simp only [forceR_eq] at h\n'
        assert step.count(a) == 1
        step = step.replace(a, '  · rw [hb] at h\n    unfold tzL at h\n    simp only [forceR_eq] at h\n')
    if dev and 'b' not in opts:
        out += 'structure TZ where\n  (CVP CN VP VN : ℕ)\ndef KVz : ℕ := %d\n' % (1 << 160)
    else:
        out += p_kernel(Q, TS, BS, pt, t_tzv) + term + '\n'
    out += LANES.replace('@Q@', str(Q)).replace('@NT@', str(NT)).replace('@LMSK@', str((1 << LANE) - 1))
    out += INV_P.replace('@Q@', str(Q)).replace('@NT@', str(NT))
    out += tg
    out += step
    out += zchk_text(Q, BS)
    out += fin_text(Q, NT) + '\n'
    out += chain_text(Q, TS, pt, 'ydecH2' if 'y' in opts else 'ydecH')
    if dev:
        for nm in sorted(DEVNAMES + (TERMNAMES if 'b' in opts else []), key=len, reverse=True):
            out = re.sub(r'(?<![\w.\'])%s(?![\w\'])' % re.escape(nm), nm + '2', out)
    return out


def defn(lines, name):
    TOP = ('def ', 'theorem ', 'abbrev ', 'structure ', 'set_option ', 'local ', 'lemma ', 'end ', 'namespace ', '@[', '/--')
    for i, l in enumerate(lines):
        if l.startswith('def %s ' % name):
            j = i + 1
            while j < len(lines) and not lines[j].startswith(TOP):
                j += 1
            return '\n'.join(lines[i:j]) + '\n'
    raise KeyError(name)
