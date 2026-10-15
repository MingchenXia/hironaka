import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.StepOneWellFounded
import Hironaka.MarkedIdeal.DerivativeIdealAlong
open Lean Elab Command
partial def contextNames (e : Expr) : Array Name :=
  match e with
  | .lam n t b _ | .forallE n t b _ => #[n] ++ contextNames t ++ contextNames b
  | .letE n t v b _ => #[n] ++ contextNames t ++ contextNames v ++ contextNames b
  | .app f a => contextNames f ++ contextNames a
  | .mdata _ b | .proj _ _ b => contextNames b
  | _ => #[]
run_cmd do
  let env ← getEnv
  for (m, scope) in #[(`Hironaka.Invariant.ResolutionInvariantSeq,2228578503),
      (`Hironaka.Invariant.StepOneWellFounded,307985626),
      (`Hironaka.MarkedIdeal.DerivativeIdealAlong,128644472)] do
    let some idx := env.header.moduleNames.findIdx? (· == m) | throwError "owner missing {m}"
    let mut count := 0
    for ci in env.header.moduleData[idx]!.constants do
      let names := contextNames ci.type ++ ((ci.value? (allowOpaque := true)).map contextNames).getD #[]
      for name in names do
        if (name.toString.splitOn s!"{m}.{scope}._hygCtx").length > 1 then
          logInfo m!"ACTUAL_IMPORTED_OWNER {m}; scope {scope}; declaration {ci.name}; exact binder {name}"
          count := count + 1
    if count == 0 then throwError "No actual imported binder context witness {m}/{scope}"
