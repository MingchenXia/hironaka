import TranscendentalNakamaye.Pending.StepFourOnStrictTransform
open Lean
run_cmd do
  let env ← getEnv
  let name := `TranscendentalNakamaye.Pending.StepFourOnStrictTransform.fderiv_coordinateMap_val_injective
  unless env.contains name do throwError "Absent actual original immersion theorem"
  let some owner := env.getModuleIdxFor? name | throwError "No actual original owning module"
  let axioms ← collectAxioms name
  for a in axioms do
    unless #[``propext,``Classical.choice,``Quot.sound].contains a do throwError "Nonstandard original axiom {a}"
  let row := Json.mkObj [("status",toJson "ACTUAL_ORIGINAL_EXPORT_STANDARD_AXIOMS_ONLY"),
    ("original_binding",toJson name.toString),
    ("actual_owner",toJson env.header.moduleNames[owner.toNat]!.toString),
    ("transitive_axioms",toJson (axioms.map Name.toString))]
  IO.FS.writeFile "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/actual-original-submanifold-immersion-binding.json" row.pretty
  logInfo m!"ACTUAL_ORIGINAL_SUBMANIFOLD_IMMERSION_BINDING {name} STANDARD_AXIOMS_ONLY; existing artifact, no build or kernel replay"
