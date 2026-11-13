namespace ZeroForgePack
open Lean
structure Rd where
  d : Array Nat
  p : Nat
abbrev M := StateT Rd (Except String)
def bit : M Nat := do
  let s ← get
  match s.d[s.p / 6]? with
  | some c => set { s with p := s.p + 1 }; return (c >>> (5 - s.p % 6)) % 2
  | none => throw "zfPack: payload ends early"
def bits : Nat → M Nat
  | 0 => pure 0
  | n + 1 => do let v ← bits n; return 2 * v + (← bit)
def zeros : Nat → M Nat
  | 0 => throw "zfPack: code too long"
  | f + 1 => do if (← bit) = 1 then return 0 else return (← zeros f) + 1
def eg (k : Nat) : M Nat := do
  let z ← zeros 64
  return (← bits (z + k)) + 2 ^ (z + k) - 2 ^ k
def sg (k : Nat) : M Int := do
  let u ← eg k
  return if u % 2 = 0 then (u / 2 : Nat) else -((u / 2 : Nat) : Int) - 1
def run {α : Type} (m : M α) (text : String) : Except String α := do
  let d ← text.toUTF8.toList.toArray.mapM ZeroForgePackedNat.digit64
  let (a, s) ← m.run ⟨d, 0⟩
  let pad := 6 * d.size - s.p
  if pad ≥ 6 then throw "zfPack: trailing characters"
  let (z, _) ← (bits pad).run s
  if z ≠ 0 then throw "zfPack: nonzero padding"
  return a
def num (n : Nat) : Term := Syntax.mkNumLit (toString n)
def ptt : M (Array (Nat × Nat)) := do
  let n ← eg 0
  let kx ← eg 0; let kP ← eg 0; let kV ← eg 0; let kS ← eg 0; let kA ← eg 0; let kB ← eg 0
  let mut out := #[]
  let mut x : Int := 0; let mut P : Int := 0; let mut dP : Int := 0; let mut dx' : Int := 1
  let mut V : Int := 0; let mut S : Int := 0; let mut A : Int := 0; let mut B : Int := 0
  for _ in [0:n] do
    let dx : Int := 8 * ((← eg kx) + 1)
    let P' := P + dP * dx / dx' + (← sg kP)
    let V' := V + 10 * dx * (P + P' - 4000000000) / 65536 + (← sg kV)
    S := S + (← sg kS); A := A + (← sg kA); B := B + (← sg kB)
    let x' := x + dx
    let Mv := 4000000000 - P' + S
    unless 0 ≤ V' ∧ V' < 2 ^ 32 ∧ 0 ≤ P' ∧ P' < 2 ^ 32 ∧ 0 ≤ Mv ∧ Mv < 2 ^ 32 ∧ 0 ≤ x' - A ∧ x' - A < 2 ^ 20 ∧ x' ≤ B do
      throw "zfPTT: field out of range"
    out := out.push (x'.toNat, (V' + 2 ^ 32 * P' + 2 ^ 64 * Mv + 2 ^ 96 * (x' - A) + 2 ^ 116 * (B - x')).toNat)
    dP := P' - P; dx' := dx; x := x'; P := P'; V := V'
  return out
/-- `ptt` with one more field per entry: the piece count n − 1, stored above bit 140 -/
def pttN : M (Array (Nat × Nat)) := do
  let n ← eg 0
  let kx ← eg 0; let kP ← eg 0; let kV ← eg 0; let kS ← eg 0; let kA ← eg 0; let kB ← eg 0; let kN ← eg 0
  let mut out := #[]
  let mut x : Int := 0; let mut P : Int := 0; let mut dP : Int := 0; let mut dx' : Int := 1
  let mut V : Int := 0; let mut S : Int := 0; let mut A : Int := 0; let mut B : Int := 0
  for _ in [0:n] do
    let dx : Int := 8 * ((← eg kx) + 1)
    let P' := P + dP * dx / dx' + (← sg kP)
    let V' := V + 10 * dx * (P + P' - 4000000000) / 65536 + (← sg kV)
    S := S + (← sg kS); A := A + (← sg kA); B := B + (← sg kB)
    let nn ← eg kN
    let x' := x + dx
    let Mv := 4000000000 - P' + S
    unless 0 ≤ V' ∧ V' < 2 ^ 32 ∧ 0 ≤ P' ∧ P' < 2 ^ 32 ∧ 0 ≤ Mv ∧ Mv < 2 ^ 32 ∧ 0 ≤ x' - A ∧ x' - A < 2 ^ 20 ∧ x' ≤ B do
      throw "zfPTT: field out of range"
    out := out.push (x'.toNat, (V' + 2 ^ 32 * P' + 2 ^ 64 * Mv + 2 ^ 96 * (x' - A) + 2 ^ 116 * (B - x') + 2 ^ 140 * nn).toNat)
    dP := P' - P; dx' := dx; x := x'; P := P'; V := V'
  return out
def pttLeaves (es : Array (Nat × Nat)) : Array (Nat × Array (Nat × Nat)) :=
  es.foldl (init := #[]) fun G (x, w) =>
    match G.back? with
    | some (j, L) => if j = x / 1024 then G.pop.push (j, L.push (x % 1024, w)) else G.push (x / 1024, #[(x % 1024, w)])
    | none => #[(x / 1024, #[(x % 1024, w)])]
def pttTree (G : Array (Nat × Array (Nat × Nat))) : Nat → Nat → Nat → MacroM Term
  | 0, _, _ => Macro.throwError "zfPTT: tree too deep"
  | f + 1, a, b => do
    if b ≤ a + 1 then
      let (j, L) := G[a]!
      let es ← L.mapM fun (o, w) => `(($(num o), $(num w)))
      `(($(mkIdent `AMW.Cert.PCell.PTrD.lf) $(num j) [$es,*]))
    else
      let m := a + (b - a) / 2
      `(($(mkIdent `AMW.Cert.PCell.PTrD.nd) $(num G[m]!.1) $(← pttTree G f a m) $(← pttTree G f m b)))
def pyr (lanes : Nat) : M (Nat × Array (Nat × Nat)) := do
  let nb ← eg 0
  let kj ← eg 0; let kr ← eg 0; let kl ← eg 0; let ki ← eg 0; let kt ← eg 0
  let mut blocks : Array (Nat × Nat) := #[]
  let mut roots : Array (Array Int) := Array.replicate 512 (Array.replicate lanes 0)
  let mut j : Int := -1
  let mut r : Int := 0
  let mut hist : Array (Int × Int) := Array.replicate lanes (0, 0)
  for _ in [0:nb] do
    j := j + 1 + (← eg kj); r := r + (← sg kr)
    unless 0 ≤ r ∧ r ≤ 10 ∧ j < 512 do throw "zfPyr: block out of range"
    let D := 10 - r.toNat
    let mut F : Array (Array Int) := Array.replicate lanes (Array.replicate (2 ^ (D + 1) - 1) 0)
    for l in [0:lanes] do
      let mut f := F[l]!
      for t in [0:2 ^ D] do
        let (u, v) := hist[l]!
        let w := 2 * v - u + (← sg kl)
        hist := hist.set! l (v, w); f := f.set! (2 ^ D - 1 + t) w
      F := F.set! l f
    for l in [0:lanes] do
      let mut f := F[l]!
      for i' in [0:2 ^ D - 1] do
        let i := 2 ^ D - 2 - i'
        f := f.set! i (min f[2 * i + 1]! f[2 * i + 2]! - (← sg ki))
      F := F.set! l f
    let mut X : Int := r
    for i in [0:2 ^ (D + 1) - 1] do
      for l in [0:lanes] do
        let v := (F[l]!)[i]!
        unless 0 ≤ v ∧ v < 2 ^ 32 do throw "zfPyr: field out of range"
        X := X + v * 2 ^ (5 + 32 * lanes * i + 32 * l)
    blocks := blocks.push (j.toNat, X.toNat)
    roots := roots.set! j.toNat (F.map (·[0]!))
  let mut top : Int := 0
  for l in [0:lanes] do
    let mut T : Array Int := Array.replicate 512 0
    T := T.set! 0 (← sg kt)
    for h' in [0:511] do
      let h := 511 - h'
      let (a, b) := if h ≥ 256 then ((roots[2 * (h - 256)]!)[l]!, (roots[2 * (h - 256) + 1]!)[l]!) else (T[2 * h]!, T[2 * h + 1]!)
      T := T.set! h (min a b - (← sg kt))
    for h in [0:512] do
      unless 0 ≤ T[h]! ∧ T[h]! < 2 ^ 32 do throw "zfPyr: top field out of range"
      top := top + T[h]! * 2 ^ (32 * lanes * h + 32 * l)
  return (top.toNat, blocks)
def blockName (bk : Name) (s : String) : Ident := mkIdent (Name.mkSimple (bk.toString ++ s))
def dispatch (bk : Name) (blocks : Array (Nat × Nat)) : Nat → Nat → Nat → StateT (Array Syntax) MacroM Term
  | 0, _, _ => Macro.throwError "zfPyr: dispatch too deep"
  | f + 1, a, b => do
    if b ≤ a + 1 then
      `(($(mkIdent `dpk) $(mkIdent `j) $(num blocks[a]!.1) $(blockName bk s!"_{blocks[a]!.1}")))
    else
      let m := a + (b - a) / 2
      let lt ← dispatch bk blocks f a m
      let rt ← dispatch bk blocks f m b
      let n := blockName bk s!"s{a}_{b}"
      let d ← `(def $n ($(mkIdent `j) : ℕ) : ℕ := $(mkIdent `dsel) $(mkIdent `j) $(num blocks[m]!.1) $lt $rt)
      modify (·.push d)
      `(($n $(mkIdent `j)))
def pyrCmds (top bk : Name) (v : Nat) (blocks : Array (Nat × Nat)) : MacroM (Array Syntax) := do
  let mut cmds := #[← `(def $(mkIdent top) : ℕ := $(num v))]
  for (k, X) in blocks do
    cmds := cmds.push (← `(def $(blockName bk s!"_{k}") : ℕ := $(num X)))
  let (t, ds) : Term × Array Syntax ← if blocks.isEmpty then pure (← `(0), #[]) else (dispatch bk blocks (blocks.size + 1) 0 blocks.size).run #[]
  return (cmds ++ ds).push (← `(def $(mkIdent bk) ($(mkIdent `j) : ℕ) : ℕ := $t))
end ZeroForgePack
macro "zfPTT " payload:str : term => do
  match ZeroForgePack.run ZeroForgePack.ptt payload.getString with
  | .ok es => ZeroForgePack.pttTree (ZeroForgePack.pttLeaves es) (es.size + 1) 0 (ZeroForgePack.pttLeaves es).size
  | .error message => Lean.Macro.throwErrorAt payload message
macro "zfPTTN " payload:str : term => do
  match ZeroForgePack.run ZeroForgePack.pttN payload.getString with
  | .ok es => ZeroForgePack.pttTree (ZeroForgePack.pttLeaves es) (es.size + 1) 0 (ZeroForgePack.pttLeaves es).size
  | .error message => Lean.Macro.throwErrorAt payload message
macro "zfPyr " top:ident bk:ident lanes:num payload:str : command => do
  match ZeroForgePack.run (ZeroForgePack.pyr lanes.getNat) payload.getString with
  | .ok (v, blocks) => return ⟨Lean.mkNullNode (← ZeroForgePack.pyrCmds top.getId bk.getId v blocks)⟩
  | .error message => Lean.Macro.throwErrorAt payload message
