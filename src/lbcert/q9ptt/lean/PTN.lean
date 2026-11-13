/- Tangent point table with a per-point zside piece count (prototype for the q = 9 entry).
Each table entry (o, w) stores the point word in the low 140 bits of w and n - 1 above them; the check of
the point is `ivOk` with that n (`tangent_valZC` holds for every n > 0), so the leaves' lemma
`∀ x, PVI x (PT x)` is unchanged. -/
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the piece count of an entry: bits 140- plus one -/
def nOf (w : ℕ) : ℕ := Nat.add (Nat.shiftRight w 140) 1
/-- the stored point word of an entry: bits 0-139 -/
def wOf (w : ℕ) : ℕ := Nat.land w 1393796574908163946345982392040522594123775

def ptlN (L : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ ih => Bool.rec (motive := fun _ => ℕ) ih (pwD x (wOf e.2)) (Nat.beq e.1 (Nat.mod x 1024))) L
def ptlOkN (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (csh j : ℕ)
    (L : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => pt3e (Nat.add (Nat.mul 1024 j) e.1) (trip (pwD (Nat.add (Nat.mul 1024 j) e.1) (wOf e.2)))
      && ivOk R top bk tD bD (nOf e.2) csh (Nat.add (Nat.mul 1024 j) e.1) (pwD (Nat.add (Nat.mul 1024 j) e.1) (wOf e.2))
      && ih) L

theorem ptlN_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {csh : ℕ} (j : ℕ) :
    ∀ L : List (ℕ × ℕ), ptlOkN R top bk tD bD csh j L = true → ∀ x, x / 1024 = j → PVI x (ptlN L x) := by
  intro L
  induction L with
  | nil => intro _ x _; exact pvi_zero x
  | cons e r ih =>
    intro h x hx
    have h' : (pt3e (Nat.add (Nat.mul 1024 j) e.1) (trip (pwD (Nat.add (Nat.mul 1024 j) e.1) (wOf e.2)))
      && ivOk R top bk tD bD (nOf e.2) csh (Nat.add (Nat.mul 1024 j) e.1) (pwD (Nat.add (Nat.mul 1024 j) e.1) (wOf e.2))
      && ptlOkN R top bk tD bD csh j r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨he, hiv⟩, hr⟩ := h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptlN r x) (pwD x (wOf e.2)) (Nat.beq e.1 (Nat.mod x 1024)))
    cases hb : Nat.beq e.1 (Nat.mod x 1024)
    · exact ih hr x hx
    · have he1 : e.1 = x % 1024 := Nat.eq_of_beq_eq_true hb
      have hxe : Nat.add (Nat.mul 1024 j) e.1 = x := by
        show 1024 * j + e.1 = x
        rw [he1, ← hx]; exact Nat.div_add_mod x 1024
      rw [hxe] at he hiv
      simp only [pt3e, Bool.and_eq_true] at he
      have hpv : PV x (trip (pwD x (wOf e.2))) := ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩
      have hn : 0 < nOf e.2 := Nat.succ_pos _
      exact ⟨hpv, ivOk_sound hlb hD hR hn hpv hiv⟩

def ptGetN (t : PTrD) (x : ℕ) : ℕ :=
  PTrD.rec (motive := fun _ => ℕ) (fun j L => Bool.rec (motive := fun _ => ℕ) 0 (ptlN L x) (Nat.beq (Nat.div x 1024) j))
    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt (Nat.div x 1024) k)) t
def ptOkTN (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (csh : ℕ) (t : PTrD) : Bool :=
  PTrD.rec (motive := fun _ => Bool) (fun j L => ptlOkN R top bk tD bD csh j L) (fun _ _ _ bl br => bl && br) t

theorem ptTN_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {csh : ℕ} :
    ∀ t : PTrD, ptOkTN R top bk tD bD csh t = true → ∀ x, PVI x (ptGetN t x) := by
  intro t
  induction t with
  | lf j L =>
    intro h x
    show PVI x (Bool.rec (motive := fun _ => ℕ) 0 (ptlN L x) (Nat.beq (Nat.div x 1024) j))
    cases hb : Nat.beq (Nat.div x 1024) j
    · exact pvi_zero x
    · exact ptlN_sound hlb hD hR j L h x (Nat.eq_of_beq_eq_true hb)
  | nd k l r ihl ihr =>
    intro h x
    have h' : (ptOkTN R top bk tD bD csh l && ptOkTN R top bk tD bD csh r) = true := h
    simp only [Bool.and_eq_true] at h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptGetN r x) (ptGetN l x) (Nat.blt (Nat.div x 1024) k))
    cases Nat.blt (Nat.div x 1024) k
    · exact ihr h'.2 x
    · exact ihl h'.1 x

theorem ptOkTN_nd {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {csh k : ℕ}
    {l r : PTrD} (hl : ptOkTN R top bk tD bD csh l = true) (hr : ptOkTN R top bk tD bD csh r = true) :
    ptOkTN R top bk tD bD csh (.nd k l r) = true := by
  show (ptOkTN R top bk tD bD csh l && ptOkTN R top bk tD bD csh r) = true
  rw [hl, hr]; rfl

end AMW.Cert.PCell
end
