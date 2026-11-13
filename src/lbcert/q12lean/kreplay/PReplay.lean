import Export.Parse
import Lean
/-! Parallel Lean kernel replay of a lean4export export (by Rishi Khan, 2026-10-25), after Lean's
`Environment.replay` (Lean/Replay.lean, Kim Morrison, Apache-2.0) and q9fixed/replay/TReplay.lean.

The constants are visited in the same dependency order as `Environment.replay`. Each definition, theorem and
opaque constant is added to the running environment without checking, and a task checks it with the kernel
(`addDeclCore`) against the environment as it was just before it, which is the environment the sequential replay
checks it in. Axioms, inductive types and the quotient are added with the kernel check, in order. The run fails
unless every task's check succeeds, so it accepts exactly the exports the sequential replay accepts.
The checks run after the ordering pass on THREADS dedicated worker threads; worker w checks the queued declarations w, w + THREADS, ...

Usage: lean --run PReplay.lean EXPORT [TOP] [THREADS] -/
open Lean

namespace PR
structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  jobs : Array (Name × Kernel.Environment × Declaration) := #[]

abbrev M := ReaderT (Std.HashMap Name ConstantInfo) <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  if (← get).remaining.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  return false

/-- the kernel check of `d` against `env`, timed (ns) -/
def check (env : Kernel.Environment) (d : Declaration) : BaseIO (Except String Nat) := do
  let t0 ← IO.monoNanosNow
  match env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok _ => return .ok ((← IO.monoNanosNow) - t0)
  | .error _ => return .error "rejected"

/-- checked, in order (axioms, inductives, quotient) -/
def addSeq (n : Name) (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error _ => throw <| .userError s!"kernel rejected {n}"

/-- added unchecked; its check (against the environment before it) is queued for the workers -/
def addPar (n : Name) (d : Declaration) : M Unit := do
  let env0 := (← get).env
  match env0.addDeclWithoutChecking d with
  | .ok env => modify fun s => { s with env := env, jobs := s.jobs.push (n, env0, d) }
  | .error _ => throw <| .userError s!"could not add {n}"

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read)[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo info => addPar name (Declaration.defnDecl info)
      | .thmInfo info => addPar name (Declaration.thmDecl info)
      | .axiomInfo info => addSeq name (Declaration.axiomDecl info)
      | .opaqueInfo info => addPar name (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let all ← info.all.mapM fun n => do pure ((← read)[n]!)
        for o in all do
          modify fun s => { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure ((← read)[n]!))
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name, type := ci.type, ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addSeq name (Declaration.inductDecl info.levelParams info.numParams types false)
      | .ctorInfo _ => pure ()
      | .recInfo _ => pure ()
      | .quotInfo _ =>
        replayConstant `Eq
        addSeq name Declaration.quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end
end PR

def main (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let h ← IO.FS.Handle.mk args[0]! .read
  let sol ← Export.parseStream (IO.FS.Stream.ofHandle h)
  let top := (args[1]? >>= String.toNat?).getD 30
  let t1 ← IO.monoMsNow
  let env ← Lean.mkEmptyEnvironment
  let cm := sol.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  let mut remaining : NameSet := ∅
  for (n, ci) in cm.toList do
    if !ci.isUnsafe && !ci.isPartial then remaining := remaining.insert n
  let (_, s) ← (ReaderT.run (do for n in remaining do PR.replayConstant n) cm).run { env := env.toKernelEnv, remaining }
  let t2 ← IO.monoMsNow
  let nthr := (args[2]? >>= String.toNat?).getD 4
  let jobs := s.jobs
  let names := jobs.map (·.1)
  -- worker w checks the queued declarations w, w + N, w + 2N, ... (no shared state between workers)
  let worker (w : Nat) : IO (Array (Nat × Except String Nat)) := do
    let mut out := #[]
    let mut i := w
    while i < jobs.size do
      if let some (_, env0, d) := jobs[i]? then
        out := out.push (i, ← PR.check env0 d)
      i := i + nthr
    return out
  let ws ← (List.range nthr).mapM fun w => IO.asTask (worker w) (prio := .dedicated)
  let mut bad : Array Name := #[]
  let mut times : Array (Nat × Name) := #[]
  for t in ws do
    match ← IO.wait t with
    | .ok rs =>
      for (i, r) in rs do
        match r with
        | .ok ns => times := times.push (ns, names[i]!)
        | .error _ => bad := bad.push names[i]!
    | .error e => throw e
  let t3 ← IO.monoMsNow
  let ts := times.qsort (fun a b => a.1 > b.1)
  let tot := ts.foldl (fun a x => a + x.1) 0
  IO.println s!"parse {t1 - t0} ms, order {t2 - t1} ms, checks {t3 - t2} ms on {nthr} threads, replay wall {t3 - t1} ms, kernel sum {tot / 1000000} ms, checked {ts.size}, rejected {bad.size}"
  for (t, n) in ts.toList.take top do
    IO.println s!"{t / 1000000}\t{n}"
  if bad.isEmpty then
    IO.println "PARALLEL REPLAY OK"
    return 0
  for n in bad do IO.println s!"rejected: {n}"
  return 1
