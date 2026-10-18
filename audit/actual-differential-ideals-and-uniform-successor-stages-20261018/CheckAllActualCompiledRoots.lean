import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  let readNames (path : String) : IO (Array Name) := do
    let raw ← IO.FS.readFile path
    let parsed ← IO.ofExcept (Json.parse raw)
    let xs ← IO.ofExcept (fromJson? parsed : Except String (Array String))
    pure (xs.map String.toName)
  let targets ← readNames "audit/actual-differential-ideals-and-uniform-successor-stages-20261018/new-module-targets.json"
  let bindings ← readNames "audit/actual-differential-ideals-and-uniform-successor-stages-20261018/new-local-bindings.json"
  let mut modules : Nat := 0
  let mut total : Nat := 0
  let mut allNames : NameSet := {}
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`Hironaka).isPrefixOf m do continue
    modules := modules+1
    for ci in env.header.moduleData[i]!.constants do
      total := total+1
      allNames := allNames.insert ci.name
      for ax in (← collectAxioms ci.name) do
        unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "Nonstandard axiom {ax} at {ci.name}"
  let mut fresh : Nat := 0
  for target in targets do
    let some idx := env.header.moduleNames.findIdx? (· == target)
      | throwError "Missing actual new module {target}"
    let roots := env.header.moduleData[idx]!.constants
    fresh := fresh+roots.size
    logInfo m!"ACTUAL_NEW_MODULE {target}: {roots.size} compiled roots"
  let mut missing : Array Name := #[]
  for binding in bindings do
    unless allNames.contains binding do
      missing := missing.push binding
      logInfo m!"MISSING_EXACT_BINDING {binding}"
  logInfo m!"ALL_LIBRARY_MODULES {modules}; ALL_LIBRARY_ACTUAL_ROOTS {total}; NEW_MODULES {targets.size}; NEW_ACTUAL_ROOTS {fresh}; EXACT_BINDINGS {bindings.size}; MISSING {missing.size}; STANDARD_THREE_ONLY"
  unless missing.isEmpty do throwError "Missing {missing.size} exact blueprint bindings"
  for (label,path,expected) in #[
      ("SYNCHRONIZED_BLUEPRINT", "audit/actual-differential-ideals-and-uniform-successor-stages-20261018/complete-blueprint-local-bindings.json", 4378),
      ("ALL_DOCUMENT_BLUEPRINT", "audit/actual-differential-ideals-and-uniform-successor-stages-20261018/all-document-local-bindings.json", 5537)] do
    let names ← readNames path
    unless names.size == expected do throwError "Changed {label} binding inventory"
    let mut absent : Array Name := #[]
    for name in names do
      unless allNames.contains name do
        absent := absent.push name
        logInfo m!"MISSING_{label}_BINDING {name}"
    logInfo m!"{label}_EXACT_LOCAL_BINDINGS {names.size}; MISSING {absent.size}"
    unless absent.isEmpty do throwError "Missing {label} bindings: {absent.size}"
