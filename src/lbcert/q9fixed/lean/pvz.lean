/- Cheaper evaluation of pvCheck (by Rishi Khan, 2026-10-24). For j ≠ 0 the term termU i j equals termZ i j / 10²⁵
exactly (sinLook, piMul and cAM have the denominators 10¹⁰, 10⁶ and 10⁹), so the j ≠ 0 terms are summed in ℤ;
sinPiI2 drops the interval that sinPiI multiplies by a zero coefficient of csA. pvCheck2_eq shows that pvCheck2
is pvCheck. -/
theorem csA_zero (k : ℕ) : (csA k).1 = 0 ∨ (csA k).2 = 0 := by
 induction k with
 | zero => simp [csA]
 | succ k ih => simp only [csA]; rcases ih with h | h <;> simp [h]
def sinPiI2 (t : ℚ) : ℚ × ℚ :=
 if 0 ≤ rOf t then
   (if (csA (kOf t)).1 = 0 then imulZ (csA (kOf t)).2 (cosI (rOf t)) else imulZ (csA (kOf t)).1 (sinI (rOf t)))
 else
   (if (csA (kOf t)).1 = 0 then imulZ (csA (kOf t)).2 (cosI (-rOf t)) else ineg (imulZ (csA (kOf t)).1 (sinI (-rOf t))))
theorem sinPiI2_eq (t : ℚ) : sinPiI2 t = sinPiI t := by
 unfold sinPiI2 sinPiI
 have hz : ∀ I : ℚ × ℚ, imulZ 0 I = (0, 0) := fun I => by simp [imulZ]
 by_cases h1 : (csA (kOf t)).1 = 0
 · simp only [h1, ↓reduceIte, hz]
   split_ifs <;> simp [iadd, isub]
 · have h2 : (csA (kOf t)).2 = 0 := (csA_zero (kOf t)).resolve_left h1
   simp only [h1, h2, ↓reduceIte, hz]
   split_ifs <;> simp [iadd, isub, ineg]
def tabOk2 : Bool :=
 allQ (fun q => sinPiOk ((q : ℚ) / 512) && decide ((tabI q).1 ≤ (sinPiI2 ((q : ℚ) / 512)).1)
   && decide ((sinPiI2 ((q : ℚ) / 512)).2 ≤ (tabI q).2)) 257
theorem tabOk2_eq : tabOk2 = tabOk := by
 unfold tabOk2 tabOk; simp only [sinPiI2_eq]
def eZ (j : ℕ) : ℤ := -(2 * (j : ℤ) * cAMn j)
def inegZ (I : ℤ × ℤ) : ℤ × ℤ := (-I.2, -I.1)
def sinLookZ (r : ℕ) : ℤ × ℤ :=
 if r % 1024 ≤ 256 then tabZ (r % 1024)
 else if r % 1024 ≤ 512 then tabZ (512 - r % 1024)
 else if r % 1024 ≤ 768 then inegZ (tabZ (r % 1024 - 512))
 else inegZ (tabZ (1024 - r % 1024))
def piMulZ (S : ℤ × ℤ) : ℤ × ℤ := (min (3141592 * S.1) (3141593 * S.1), max (3141592 * S.2) (3141593 * S.2))
def termZ (i j : ℕ) : ℤ :=
 if 0 ≤ eZ j then eZ j * (piMulZ (sinLookZ (j * (2 * i + 1)))).2 else eZ j * (piMulZ (sinLookZ (j * (2 * i + 1)))).1
def sumZ (i : ℕ) : ℕ → ℤ
 | 0 => 0
 | n + 1 => sumZ i n + termZ i (n + 1)
def cellB (i : ℕ) : ℚ := termU i 0 + (sumZ i 16 : ℚ) / 10 ^ 25 + 167 / 1024
def pvCheck2 (ρ : ℚ) : Bool :=
 tabOk2 && allQ termOk 256 && decide (sumQ (fun i => max (cellB i) 0) 256 / 640 ≤ ρ)
theorem sinLook_eqZ (r : ℕ) :
   sinLook r = (((sinLookZ r).1 : ℚ) / 10000000000, ((sinLookZ r).2 : ℚ) / 10000000000) := by
 unfold sinLook sinLookZ
 split_ifs <;> simp only [tabI, ineg, inegZ, Int.cast_neg, neg_div]
theorem piMul_eqZ (S : ℤ × ℤ) :
   piMul (((S.1 : ℚ) / 10000000000, (S.2 : ℚ) / 10000000000))
     = (((piMulZ S).1 : ℚ) / 10 ^ 16, ((piMulZ S).2 : ℚ) / 10 ^ 16) := by
 simp only [piMul, piMulZ, piLoQ, piHiQ, Int.cast_min, Int.cast_max, Int.cast_mul, Prod.mk.injEq]
 have h16 : (0 : ℚ) ≤ 10 ^ 16 := by norm_num
 constructor
 · rw [← min_div_div_right h16]; congr 1 <;> push_cast <;> ring
 · rw [← max_div_div_right h16]; congr 1 <;> push_cast <;> ring
theorem termU_eqZ (i j : ℕ) (hj : j ≠ 0) : termU i j = (termZ i j : ℚ) / 10 ^ 25 := by
 have e : -(2 * (j : ℚ) * cAM j) = (eZ j : ℚ) / 10 ^ 9 := by
   simp only [eZ, cAM]; push_cast; ring
 have hc : (0 ≤ -(2 * (j : ℚ) * cAM j)) ↔ 0 ≤ eZ j := by
   rw [e, le_div_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 9), zero_mul]; norm_cast
 unfold termU termZ
 rw [if_neg hj, sinLook_eqZ, piMul_eqZ]
 by_cases h : 0 ≤ eZ j
 · rw [if_pos (hc.mpr h), if_pos h, e]; push_cast; ring
 · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, e]; push_cast; ring
theorem sumQ_termU_eqZ (i : ℕ) : sumQ (termU i) 17 = termU i 0 + (sumZ i 16 : ℚ) / 10 ^ 25 := by
 have key : ∀ n, sumQ (termU i) (n + 1) = termU i 0 + (sumZ i n : ℚ) / 10 ^ 25 := by
   intro n
   induction n with
   | zero => simp [sumQ, sumZ]
   | succ n ih => rw [sumQ, ih, sumZ, termU_eqZ i (n + 1) (by omega)]; push_cast; ring
 exact key 16
theorem pvCheck2_eq (ρ : ℚ) : pvCheck2 ρ = pvCheck ρ := by
 have h : (fun i => max (cellB i) 0) = (fun i => max (cellU i) 0) := by
   funext i; rw [cellB, cellU, sumQ_termU_eqZ]
 rw [pvCheck2, pvCheck, h, tabOk2_eq]
set_option maxRecDepth 100000 in
theorem pvCheck_AM : pvCheck (1 / 25) = true := by
 rw [← pvCheck2_eq]; decide +kernel
