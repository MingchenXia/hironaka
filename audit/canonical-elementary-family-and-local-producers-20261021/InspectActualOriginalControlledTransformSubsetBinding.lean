import TranscendentalNakamaye.Pending.BlowupDerivativeIdeal
open Lean
set_option pp.all true
run_cmd do
  let env ← getEnv
  let name := `TranscendentalNakamaye.Pending.MaximalContact.IsMaximalOrder.controlledTransform_of_subset_cosupport
  let some ci := env.find? name | throwError "Missing exact original declaration"
  let some owner := env.getModuleIdxFor? name | throwError "Missing actual module owner"
  let axs ← collectAxioms name
  for ax in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Nonstandard original axiom {ax}"
  let row := Json.mkObj [
    ("status", toJson "ACTUAL_ORIGINAL_DECLARATION_TYPE_AND_STANDARD_AXIOMS_VERIFIED"),
    ("original_binding", toJson name.toString),
    ("actual_owner", toJson env.header.moduleNames[owner.toNat]!.toString),
    ("actual_full_type_repr", toJson (reprStr ci.type)),
    ("transitive_axioms", toJson (axs.map Name.toString))]
  IO.FS.writeFile "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/actual-original-controlled-transform-subset-binding.json" row.pretty
  logInfo m!"ACTUAL_ORIGINAL_CONTROLLED_TRANSFORM_SUBSET {name} STANDARD_AXIOMS_ONLY"
  logInfo m!"ACTUAL_ORIGINAL_FULL_TYPE {ci.type}"
