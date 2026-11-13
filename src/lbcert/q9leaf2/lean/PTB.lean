/- Tangent point table as a balanced binary tree over the points (q9leaf2). A leaf holds the point x, its looked-up
word g (the stored word with its interval ends made absolute, as `pwD x` gives them) and its zside piece count
less one; a lookup compares x with one key per level and returns g, or 0 for a point outside the table. The check
of a point is the one ptlOkN makes (pt3e, then ivOk with the point's piece count), so `∀ x, PVI x (PT x)` keeps
its statement. -/
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

inductive PTB where
  | lf (x g m : ℕ)
  | nd (k : ℕ) (l r : PTB)

def ptGetB (t : PTB) (x : ℕ) : ℕ :=
  PTB.rec (motive := fun _ => ℕ) (fun k g _ => Bool.rec (motive := fun _ => ℕ) 0 g (Nat.beq x k))
    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt x k)) t
def ptOkB (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (csh : ℕ) (t : PTB) : Bool :=
  PTB.rec (motive := fun _ => Bool) (fun k g m => pt3e k (trip g) && ivOk R top bk tD bD (Nat.add m 1) csh k g)
    (fun _ _ _ bl br => bl && br) t

theorem ptTB_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {csh : ℕ} :
    ∀ t : PTB, ptOkB R top bk tD bD csh t = true → ∀ x, PVI x (ptGetB t x) := by
  intro t
  induction t with
  | lf k g m =>
    intro h x
    show PVI x (Bool.rec (motive := fun _ => ℕ) 0 g (Nat.beq x k))
    cases hb : Nat.beq x k
    · exact pvi_zero x
    · have hxk : x = k := Nat.eq_of_beq_eq_true hb
      subst hxk
      have h' : (pt3e x (trip g) && ivOk R top bk tD bD (Nat.add m 1) csh x g) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨he, hiv⟩ := h'
      simp only [pt3e, Bool.and_eq_true] at he
      have hpv : PV x (trip g) := ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩
      exact ⟨hpv, ivOk_sound hlb hD hR (Nat.succ_pos m) hpv hiv⟩
  | nd k l r ihl ihr =>
    intro h x
    have h' : (ptOkB R top bk tD bD csh l && ptOkB R top bk tD bD csh r) = true := h
    simp only [Bool.and_eq_true] at h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptGetB r x) (ptGetB l x) (Nat.blt x k))
    cases Nat.blt x k
    · exact ihr h'.2 x
    · exact ihl h'.1 x

theorem ptOkB_nd {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {csh k : ℕ}
    {l r : PTB} (hl : ptOkB R top bk tD bD csh l = true) (hr : ptOkB R top bk tD bD csh r = true) :
    ptOkB R top bk tD bD csh (.nd k l r) = true := by
  show (ptOkB R top bk tD bD csh l && ptOkB R top bk tD bD csh r) = true
  rw [hl, hr]; rfl

end AMW.Cert.PCell
end
namespace PackDec
open Lean
/-- the balanced point tree over the entries `es[a:b]` (x increasing; word with n − 1 above bit 140) -/
def ptbTree (es : Array (Nat × Nat)) : Nat → Nat → Nat → MacroM Term
  | 0, _, _ => Macro.throwError "zfPTB: tree too deep"
  | f + 1, a, b => do
    if b ≤ a + 1 then
      let (x, w) := es[a]!
      let v := w % 2 ^ 140
      let g := v % 2 ^ 96 + ((x - (v >>> 96) % 2 ^ 20) <<< 96) + ((x + (v >>> 116)) <<< 120)
      `(($(mkIdent `AMW.Cert.PCell.PTB.lf) $(num x) $(num g) $(num (w >>> 140))))
    else
      let m := a + (b - a) / 2
      `(($(mkIdent `AMW.Cert.PCell.PTB.nd) $(num es[m]!.1) $(← ptbTree es f a m) $(← ptbTree es f m b)))
end PackDec
macro "zfPTB " payload:str : term => do
  match PackDec.run PackDec.pttN payload.getString with
  | .ok es => PackDec.ptbTree es (es.size + 1) 0 es.size
  | .error message => Lean.Macro.throwErrorAt payload message
