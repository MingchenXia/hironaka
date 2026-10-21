import TranscendentalNakamaye.Pending.HironakaActualClosedContactControlledRestriction
open Lean
partial def inspectStringLiterals : Expr → Array String
  | .lit (.strVal s) => #[s]
  | .app f a => inspectStringLiterals f ++ inspectStringLiterals a
  | .lam _ t b _ | .forallE _ t b _ => inspectStringLiterals t ++ inspectStringLiterals b
  | .letE _ t v b _ => inspectStringLiterals t ++ inspectStringLiterals v ++ inspectStringLiterals b
  | .mdata _ b | .proj _ _ b => inspectStringLiterals b
  | _ => #[]
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.findIdx? (· == `TranscendentalNakamaye.Pending.HironakaActualClosedContactControlledRestriction)
    | throwError "Missing native module"
  for ci in env.header.moduleData[idx]!.constants do
    if ci.name.toString.contains "term" || ci.name.toString.contains "macro" || ci.name.toString.contains "unexpand" then
      logInfo m!"NATIVE_GENERATED {ci.name} STRINGS {((ci.value? (allowOpaque := true)).map inspectStringLiterals).getD #[] }"
