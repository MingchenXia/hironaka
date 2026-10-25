import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  let names ← IO.FS.lines "audit/phase5-original-producers-20261021/new14-literal-bindings.txt"
  unless names.size == 81 do throwError "Changed exact literal attachment inventory"
  for name in names do
    unless env.contains name.toName do throwError "Missing exact literal local attachment {name}"
  logInfo m!"PASS_EXACT_LITERAL_ATTACHMENTS {names.size}"
