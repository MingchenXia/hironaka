import Hironaka.Resolution.HironakaCurrentEmbeddingDimension
import Hironaka.Resolution.HironakaDimensionTwoStepOneAnalyticSuperlevels
import Hironaka.Resolution.HironakaNormalCrossingsBranchOverlap
import Hironaka.Resolution.HironakaNormalCrossingsMultiplicityStrata
import Hironaka.Resolution.HironakaHolomorphicPointJets
import Hironaka.Resolution.HironakaCurveAnalyticPredicates
import Hironaka.Resolution.HironakaSmoothSubmersionOrder
import Hironaka.Analytic.RankDegeneracy
import Hironaka.Analytic.EuclideanHolomorphicGermSpan
import Hironaka.Analytic.PureSingularLocus
import Hironaka.Analytic.OrderInvariance
import Hironaka.Analytic.StokesSingularLocus
import Hironaka.Analytic.StokesSingularLocusAnalytic
import Hironaka.MarkedIdeal.CodimOneSupportAlongRemainder
import Hironaka.Coherence.CoherentIdealFiniteSpan
import Hironaka.Analytic.ThinDimensionBoundPredecessor
import Hironaka.Analytic.GeometricPureDimensionBound
import Hironaka.Analytic.HolomorphicGermMaximalIdeal
import Hironaka.Invariant.IdealPowerAddition
import Hironaka.Analytic.HolomorphicFlatteningRecenter
import Hironaka.Blowup.BlowupTowerSplitSuccessor
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaCurrentEmbeddingDimension, `Hironaka.Resolution.HironakaDimensionTwoStepOneAnalyticSuperlevels, `Hironaka.Resolution.HironakaNormalCrossingsBranchOverlap, `Hironaka.Resolution.HironakaNormalCrossingsMultiplicityStrata, `Hironaka.Resolution.HironakaHolomorphicPointJets, `Hironaka.Resolution.HironakaCurveAnalyticPredicates, `Hironaka.Resolution.HironakaSmoothSubmersionOrder, `Hironaka.Analytic.RankDegeneracy, `Hironaka.Analytic.EuclideanHolomorphicGermSpan, `Hironaka.Analytic.PureSingularLocus, `Hironaka.Analytic.OrderInvariance, `Hironaka.Analytic.StokesSingularLocus, `Hironaka.Analytic.StokesSingularLocusAnalytic, `Hironaka.MarkedIdeal.CodimOneSupportAlongRemainder, `Hironaka.Coherence.CoherentIdealFiniteSpan, `Hironaka.Analytic.ThinDimensionBoundPredecessor, `Hironaka.Analytic.GeometricPureDimensionBound, `Hironaka.Analytic.HolomorphicGermMaximalIdeal, `Hironaka.Invariant.IdealPowerAddition, `Hironaka.Analytic.HolomorphicFlatteningRecenter, `Hironaka.Blowup.BlowupTowerSplitSuccessor]
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
