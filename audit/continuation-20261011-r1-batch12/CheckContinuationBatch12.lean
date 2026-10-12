import Hironaka.Resolution.HironakaRelativeNormalIdealMatrices
import Hironaka.Resolution.HironakaSmoothSubmersionDivisorExponents
import Hironaka.Resolution.HironakaNormalCrossingsOriginalExponents
import Hironaka.Invariant.MonomialAmbientDataExact
import Hironaka.Invariant.MemberNonContainedPullbackExact
import Hironaka.MarkedIdeal.ControlledProductTransformExact
import Hironaka.Invariant.MemberPrincipalPullbackExact
import Hironaka.Blowup.ControlledTransformZeroExact
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaRelativeNormalIdealMatrices, `Hironaka.Resolution.HironakaSmoothSubmersionDivisorExponents, `Hironaka.Resolution.HironakaNormalCrossingsOriginalExponents, `Hironaka.Invariant.MonomialAmbientDataExact, `Hironaka.Invariant.MemberNonContainedPullbackExact, `Hironaka.MarkedIdeal.ControlledProductTransformExact, `Hironaka.Invariant.MemberPrincipalPullbackExact, `Hironaka.Blowup.ControlledTransformZeroExact]
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
