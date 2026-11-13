open Lean Elab Command in
/-- Compares every constant `Old.X` of this file with `New.X` after renaming `Old.Y` to `New.Y`:
type and value must be alpha-equivalent (`Expr.eqv`: identical except binder names and binder info);
`alphaOnly` counts the constants that are not also `Expr.equal` (identical including binder names). -/
elab "#zfCompare" : command => do
  let env ← getEnv
  let ren (e : Expr) : Expr := e.replace fun
    | .const (.str `Old s) us => some (.const (.str `New s) us)
    | _ => none
  let mut nOld : Nat := 0
  let mut nNew : Nat := 0
  let mut bad : Array Name := #[]
  let mut alphaOnly : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    match n with
    | .str `New _ => nNew := nNew + 1
    | .str `Old s =>
      nOld := nOld + 1
      match env.find? (.str `New s) with
      | some cj =>
        let same (eq : Expr → Expr → Bool) : Bool := eq (ren ci.type) cj.type && match ci.value?, cj.value? with
          | some a, some b => eq (ren a) b
          | none, none => true
          | _, _ => false
        if !same Expr.eqv then bad := bad.push n
        else if !same Expr.equal then alphaOnly := alphaOnly.push n
      | none => bad := bad.push n
    | _ => pure ()
  logInfo m!"zfCompare: {nOld} Old constants, {nNew} New constants, {bad.size} mismatches {bad.toList.take 10}, {alphaOnly.size} equal only up to binder names {alphaOnly.toList.take 40}"
  unless bad.isEmpty && nOld == nNew && nOld > 0 do throwError "zfCompare: FAILED"
#zfCompare
