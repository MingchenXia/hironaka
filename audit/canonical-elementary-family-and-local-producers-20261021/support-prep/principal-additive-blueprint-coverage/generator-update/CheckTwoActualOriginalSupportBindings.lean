import TranscendentalNakamaye.Pending.OrderMultiplicativity
import TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform
import Lean.Util.CollectAxioms

open Lean
set_option pp.all true

run_cmd do
  let env ← getEnv
  let requested := #[
    `TranscendentalNakamaye.Pending.OrderMultiplicativity.cosupport_sumIdeal_idealPow,
    `TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform.controlledTransform_sumIdeal_idealPow]
  let mut rows : Array Json := #[]
  for name in requested do
    let some ci := env.find? name | throwError "Missing exact actual original declaration {name}"
    let some owner := env.getModuleIdxFor? name | throwError "Missing actual owning module {name}"
    let physical := env.header.moduleData[owner.toNat]!.constants.filter (·.name == name)
    unless physical.size == 1 do throwError "Expected one exact physical original owner CI {name}"
    unless Expr.equal physical[0]!.type ci.type do throwError "Physical original type mismatch {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Nonstandard original axiom {name}: {ax}"
    rows := rows.push (Json.mkObj [
      ("status", toJson "ACTUAL_ORIGINAL_PHYSICAL_DECLARATION_FULL_TYPE_OWNER_AND_STANDARD_AXIOMS_WITNESS"),
      ("original_binding", toJson name.toString),
      ("actual_owner", toJson env.header.moduleNames[owner.toNat]!.toString),
      ("actual_physical_CIs_matching_name", toJson physical.size),
      ("actual_full_type_repr", toJson (reprStr physical[0]!.type)),
      ("transitive_axioms", toJson (axs.map Name.toString))])
  IO.FS.writeFile "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/support-prep/principal-additive-blueprint-coverage/generator-update/two-actual-original-support-bindings.json" (toJson rows).pretty
  logInfo "TWO_ACTUAL_ORIGINAL_SUPPORT_BINDINGS_FULL_TYPE_OWNER_STANDARD_AXIOMS_ONLY; no build, kernel replay or expression DAG export"
