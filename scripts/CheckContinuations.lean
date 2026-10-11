/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka
import Lean.Util.CollectAxioms
open Lean Elab Command

#print axioms Hironaka.HironakaCompleteDivisorSum.exists_canonical_principalization_componentSum
#print axioms Hironaka.HironakaLocallyFiniteDivisorSum.exists_locallyFinite_original_component_sums
#print axioms Hironaka.HironakaSmoothStageCenters.exists_tower_embeddedResolution_smooth_boundary_stage_centres

run_cmd do
  let env ← getEnv
  let modules : List Name := [`Hironaka.Resolution.HironakaAnalyticCentreExtension, `Hironaka.Resolution.HironakaEffectiveDivisorSum, `Hironaka.Invariant.IteratedChartDerivativeAppend, `Hironaka.Resolution.HironakaSNCComponentCoefficients, `Hironaka.Resolution.HironakaCompleteDivisorSum, `Hironaka.Resolution.HironakaCurrentStrictTransformIdeal, `Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence, `Hironaka.Resolution.HironakaConnectedBoundaryComponents, `Hironaka.Resolution.HironakaSmoothStageCenters, `Hironaka.Manifold.HolomorphicMapsContDiffOn, `Hironaka.MarkedIdeal.GermIdealOrderValue, `Hironaka.Invariant.CoherentZeroLocus, `Hironaka.Blowup.StrictVanishingIdealSupport, `Hironaka.Resolution.HironakaBlowupComparisonCocycle, `Hironaka.Resolution.HironakaHypersurfaceStageCenters, `Hironaka.Resolution.HironakaLocallyFiniteDivisorSum, `Hironaka.MarkedIdeal.DerivativeIdealCoherence, `Hironaka.Invariant.OrderTaylorCosupport, `Hironaka.MarkedIdeal.CoherentOrderUpperSemicontinuity, `Hironaka.Blowup.BlowupBijectiveComparison, `Hironaka.MarkedIdeal.GermIdealOrderBounds, `Hironaka.Analytic.GlobalSmoothHypersurfacePrimeComponent, `Hironaka.Analytic.SNCGlobalPrimeComponents, `Hironaka.Invariant.MonomialPartIntrinsic, `Hironaka.Analytic.HolomorphicLocalInverse, `Hironaka.MarkedIdeal.PointIdealPowerMonotonicity, `Hironaka.Analytic.IrreducibleComponentFilling, `Hironaka.Blowup.BlowupStrictIdealControlled, `Hironaka.Blowup.ControlledTransformUniqueness, `Hironaka.Invariant.PrincipalIdealProducts, `Hironaka.Invariant.PrincipalMonomialExponent, `Hironaka.Analytic.AnalyticJacobianSingularCore, `Hironaka.Analytic.HolomorphicGermReducednessBridge, `Hironaka.Analytic.RueckertNullstellensatz, `Hironaka.Analytic.RegularComponentClosureGeometry, `Hironaka.Analytic.AnalyticSubsetOpenMaps, `Hironaka.Resolution.HironakaPureRegularDensity, `Hironaka.Resolution.HironakaBlowupCompactPreimage, `Hironaka.Analytic.ActualWeierstrassGermQuotient, `Hironaka.Analytic.ActualHolomorphicGermFactoriality, `Hironaka.Analytic.HolomorphicCoordinatePrime, `Hironaka.Analytic.GermPrimeNullstellensatz, `Hironaka.Analytic.HolomorphicCoordinateFactorization, `Hironaka.Analytic.SNCDivisorLocalGenerator, `Hironaka.Resolution.HironakaDivisorResidualUnit, `Hironaka.Resolution.HironakaSNCSupportedMonomialIdeal, `Hironaka.Resolution.HironakaCanonicalPrincipalization, `Hironaka.Resolution.HironakaStageCenters]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless modules.contains env.header.moduleNames[i]! do continue
    for c in env.header.moduleData[i]!.constNames do
      n := n + 1
      for a in (← liftCoreM <| collectAxioms c) do
        unless allowed.contains a do throwError m!"Unexpected axiom {a} in {c}"
  logInfo m!"Continuation constant audit: {n} constants including private and compiler constants; all standard axioms"
