import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  for (label,path,expected) in #[
      ("NEW_SOURCE_CHAPTERS", "audit/canonical-elementary-family-and-local-producers-20261021/new-blueprint-binding-names.txt", 1978),
      ("WHOLE_DOCUMENT", "audit/canonical-elementary-family-and-local-producers-20261021/all-document-binding-names.txt", 8104)] do
    let names ← IO.FS.lines path
    unless names.size == expected do throwError "Changed exact literal inventory {label}"
    let mut missing : Array String := #[]
    for name in names do
      unless env.contains name.toName do
        missing := missing.push name
        logInfo m!"MISSING_EXACT_LITERAL_BINDING {label} {name}"
    logInfo m!"EXACT_LITERAL_BINDINGS {label} {names.size} MISSING {missing.size}"
    unless missing.isEmpty do throwError "Missing {missing.size} exact local binding names in {label}"
