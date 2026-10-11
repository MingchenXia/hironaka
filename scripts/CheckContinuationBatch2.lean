/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`Hironaka.Resolution.HironakaOrderTupleAnalyticSuperlevels, `Hironaka.Resolution.HironakaBoundaryCountAnalyticSuperlevels, `Hironaka.Resolution.HironakaMonomialAnalyticSuperlevels, `Hironaka.Resolution.HironakaStepOneSpecialAnalyticLoci, `Hironaka.Resolution.HironakaStepOneDimZeroAnalyticSuperlevels, `Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels, `Hironaka.Resolution.HironakaCurveStrictFibres, `Hironaka.Resolution.HironakaNormalCrossingsLocalBranches, `Hironaka.Resolution.HironakaNormalCrossingsCompatibility, `Hironaka.Resolution.HironakaHypersurfaceStrictIdeal, `Hironaka.Resolution.HironakaPureCodimensionOneInvertibleIdeal, `Hironaka.Resolution.HironakaHypersurfaceMultiplicityDescent, `Hironaka.Analytic.ActualCodimensionOneLocalEquations, `Hironaka.Analytic.ActualNoetherGeometricDimension, `Hironaka.Analytic.ActualCodimensionOneNoetherIdeal, `Hironaka.Analytic.ActualReducedHolomorphicEquation, `Hironaka.Analytic.ActualPrimeRegularDifferentialAvoidance, `Hironaka.Analytic.ActualPrimeRegularFiniteAvoidance, `Hironaka.Analytic.ActualPrimeHolomorphicRegularZeros, `Hironaka.Analytic.ActualPrimeGermGenericAvoidance, `Hironaka.Analytic.ActualPrimeHypersurfacePureNeighbourhood, `Hironaka.Analytic.AnalyticJacobianCriterion, `Hironaka.Analytic.GrowingSeqTail, `Hironaka.Analytic.JacobianMinors, `Hironaka.Analytic.GermComponentGeometricDimension, `Hironaka.Analytic.GermCoordinateFirstProjection, `Hironaka.Invariant.InvariantClosedSuperlevels, `Hironaka.Analytic.PreconnectedZeroDimensionalPoints, `Hironaka.Analytic.ThinAnalyticDimensionBound, `Hironaka.Invariant.ResolutionCentreCounting, `Hironaka.Invariant.TowerCosupportCentreCounting, `Hironaka.Resolution.HironakaPureSingularSetDictionary, `Hironaka.Invariant.TowerRestrictionStep, `Hironaka.MarkedIdeal.MaximalOrderDefinition, `Hironaka.Invariant.CompanionMaximalOrder, `Hironaka.MarkedIdeal.MaximalOrderBound, `Hironaka.Blowup.BlowupDerivativeMaximalOrder]
  let mut n : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless modules.contains env.header.moduleNames[i]! do continue
    for c in env.header.moduleData[i]!.constNames do
      n := n + 1
      for a in (← liftCoreM <| collectAxioms c) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError m!"Unexpected axiom {a} in {c}"
      logInfo m!"{c}: {(← liftCoreM <| collectAxioms c)}"
  logInfo m!"Batch two: {n} actual constants including private/compiler; all standard axioms"
