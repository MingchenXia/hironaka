import Hironaka.Resolution.HironakaCoherentTransformExtension
import Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan
import Hironaka.Resolution.HironakaNormalCrossingsHighestStratumBlowup
import Hironaka.Resolution.HironakaSmoothPullbackDerivatives
import Hironaka.Resolution.HironakaGeneralTwoCompanionCurveLoci
import Hironaka.Resolution.HironakaNormalCrossingsBoundaryTransform
import Hironaka.Coherence.GeneralCoherentIdealColon
import Hironaka.Invariant.StepOneBarMarkedCarrierBoundary
import Hironaka.Analytic.HolomorphicGermDifferentiableSubtraction
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaCoherentTransformExtension, `Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan, `Hironaka.Resolution.HironakaNormalCrossingsHighestStratumBlowup, `Hironaka.Resolution.HironakaSmoothPullbackDerivatives, `Hironaka.Resolution.HironakaGeneralTwoCompanionCurveLoci, `Hironaka.Resolution.HironakaNormalCrossingsBoundaryTransform, `Hironaka.Coherence.GeneralCoherentIdealColon, `Hironaka.Invariant.StepOneBarMarkedCarrierBoundary, `Hironaka.Analytic.HolomorphicGermDifferentiableSubtraction]
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
