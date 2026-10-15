import TranscendentalNakamaye.Pending.CoherentIdealColon
open Lean Elab Command
partial def binderNames (e : Expr) : Array Name :=
  match e with
  | .lam n t b _ | .forallE n t b _ => #[n] ++ binderNames t ++ binderNames b
  | .letE n t v b _ => #[n] ++ binderNames t ++ binderNames v ++ binderNames b
  | .app f a => binderNames f ++ binderNames a
  | .mdata _ b | .proj _ _ b => binderNames b
  | _ => #[]
run_cmd do
  let env ← getEnv
  for owner in #[`TranscendentalNakamaye.Pending.CoherentIdealColon] do
    let some idx := env.header.moduleNames.findIdx? (· == owner)
      | throwError "Missing actual module {owner}"
    let some ci := env.header.moduleData[idx]!.constants.find? (·.name == `TranscendentalNakamaye.Pending.CoherentIdealColon.isInSpanAt_range_iff)
      | throwError "Missing actual callee in {owner}"
    let ns := binderNames ci.type ++ ((ci.value? (allowOpaque := true)).map binderNames).getD #[]
    let witnesses := ns.filter fun name =>
      (name.toString.splitOn s!"{owner}.1599403507._hygCtx._hyg.44").length > 1
    if witnesses.isEmpty then throwError "No original exact scoped binder witness {owner}"
    for n in witnesses do
      logInfo m!"ACTUAL_CALLEE_OWNER {owner}; {ci.name}; EXACT_BINDER {n}"
    let axs ← collectAxioms ci.name
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax}"
