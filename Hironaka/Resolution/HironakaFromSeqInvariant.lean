/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.FactorizationDomain
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Hironaka.Manifold.HolomorphicMaps
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bases
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Blowup.BlowupTowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The two Hironaka conclusions from a resolution invariant with per-sequence local finiteness

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), embedded resolution from the canonical resolution of `(X, X, ∅,
𝓘_V, 1)`.

## Main results

* `embeddingFields_of_seq`: the four properties used by H5b, from `IsInvValue`;
-/

open Set Filter
open scoped Topology Manifold

universe u v

namespace Hironaka.HironakaFromSeqInvariant

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor Hironaka.ResolutionInvariantSeq
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ} {Λ : Type v} [LinearOrder Λ]

/-! ### The inputs of the two reductions -/

/-- **The four properties used by the embedded-resolution argument**, (1), (4), (5), (6), from a resolution invariant of the
per-sequence structure. -/
theorem embeddingFields_of_seq {k : ℕ} (R : ResolutionInvariant.{u, v} n k Λ) :
    EmbeddedFromResolution.EmbeddingFields n k R.inv :=
  ⟨R.isInvValue.admissible, R.isInvValue.emptyStep, R.isInvValue.restrictOpen, R.isInvValue.towerIso⟩

end

end Hironaka.HironakaFromSeqInvariant
