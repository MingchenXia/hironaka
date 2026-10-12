import Hironaka.Resolution.HironakaStepOneMemberCompanionHistoryExtension
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis
import Hironaka.Resolution.HironakaStepOneMemberCompanionPositiveSpecialLoci
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaStepOneMemberCompanionHistoryExtension, `Hironaka.Resolution.HironakaRelativeNormalMonomialBasis, `Hironaka.Resolution.HironakaStepOneMemberCompanionPositiveSpecialLoci]
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
