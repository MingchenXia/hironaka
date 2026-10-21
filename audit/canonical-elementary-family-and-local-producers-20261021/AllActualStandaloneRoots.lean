import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  let roster ← IO.FS.lines "audit/canonical-elementary-family-and-local-producers-20261021/all-standalone-modules.txt"
  let targets := roster.map String.toName
  let actual := env.header.moduleNames.filter fun m => (`Hironaka).isPrefixOf m
  unless actual.size == targets.size do
    throwError "Actual standalone module count {actual.size} differs from exact source roster {targets.size}"
  for m in actual do
    unless targets.contains m do throwError "Unexpected actual standalone module {m}"
  let mut total := 0
  for target in targets do
    let some idx := env.header.moduleNames.findIdx? (· == target)
      | throwError "Missing actual standalone module {target}"
    let roots := env.header.moduleData[idx]!.constants
    for ci in roots do
      let axs ← collectAxioms ci.name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Nonstandard transitive axiom {ax} in actual root {ci.name} owned by {target}"
      logInfo m!"ACTUAL_ROOT {target} {ci.name} AXIOMS {axs}"
    logInfo m!"MODULE_ACTUAL_ROOTS {target} {roots.size}"
    total := total + roots.size
  logInfo m!"ALL_LIBRARY_MODULES {targets.size}"
  logInfo m!"ALL_ACTUAL_ROOTS {total} standard axioms only; every actual moduleData root retained"
