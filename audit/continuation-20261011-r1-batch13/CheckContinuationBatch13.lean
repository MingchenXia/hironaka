import Hironaka.Resolution.HironakaRelativeNormalAssociatedGraded
import Hironaka.Resolution.HironakaStepOneMemberCompanionMaskedPositiveValues
import Hironaka.Resolution.HironakaSmoothSubmersionInvertibleQuotients
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaRelativeNormalAssociatedGraded, `Hironaka.Resolution.HironakaStepOneMemberCompanionMaskedPositiveValues, `Hironaka.Resolution.HironakaSmoothSubmersionInvertibleQuotients]
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
