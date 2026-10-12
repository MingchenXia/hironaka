import Hironaka.Resolution.HironakaStepOneMemberLowerOrderPredicates
import Hironaka.Resolution.HironakaNormalCrossingsMarkedAdmissibility
import Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients
import Hironaka.Resolution.HironakaSmoothSubmersionHomogenization
import Hironaka.Resolution.FactorizationAmbientExact
import Hironaka.Resolution.HironakaControlledTransform
import Hironaka.MarkedIdeal.HomogenizedAmbientMarkedDataExact
import Hironaka.MarkedIdeal.HomogenizedAmbientCoherenceExact
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaStepOneMemberLowerOrderPredicates, `Hironaka.Resolution.HironakaNormalCrossingsMarkedAdmissibility, `Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients, `Hironaka.Resolution.HironakaSmoothSubmersionHomogenization, `Hironaka.Resolution.FactorizationAmbientExact, `Hironaka.Resolution.HironakaControlledTransform, `Hironaka.MarkedIdeal.HomogenizedAmbientMarkedDataExact, `Hironaka.MarkedIdeal.HomogenizedAmbientCoherenceExact]
  let mut count : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless roots.contains env.header.moduleNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      let axioms ← liftCoreM <| collectAxioms ci.name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError m!"Unexpected axiom {ax} in {ci.name}"
      logInfo m!"{ci.name}: {axioms}"
      count := count + 1
  logInfo m!"All actual new moduleData constants: {count}"
