import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  let raw ← IO.FS.readFile "audit/local-coefficients-and-curve-overlaps-20261015/complete-blueprint-local-bindings.json"
  let parsed ← IO.ofExcept (Json.parse raw)
  let names ← IO.ofExcept (fromJson? parsed : Except String (Array String))
  for name in names do
    let n := name.toName
    unless env.contains n do throwError "Unresolved synchronized blueprint binding {n}"
    for ax in (← collectAxioms n) do
      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax} at {n}"
  logInfo m!"ALL_SYNCHRONIZED_BLUEPRINT_BINDINGS {names.size} STANDARD_THREE_ONLY"
