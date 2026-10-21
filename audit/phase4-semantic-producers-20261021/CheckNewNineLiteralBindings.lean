import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  let names ← IO.FS.lines "audit/phase4-semantic-producers-20261021/new-nine-literal-bindings.txt"
  unless names.size == 42 do throwError "Changed nine-chapter literal attachment inventory"
  for name in names do
    unless env.contains name.toName do throwError "Missing exact literal local attachment {name}"
  logInfo m!"PASS_EXACT_LITERAL_ATTACHMENTS {names.size}"
