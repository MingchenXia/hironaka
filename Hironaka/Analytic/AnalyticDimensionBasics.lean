/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.PositiveDimensionalComponent
import Hironaka.Resolution.StrictTransformSubvariety
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Manifold.ChartDifferentiable
import Hironaka.Analytic.HolomorphicIdealSheaves
import Mathlib.Data.EReal.Inv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Hironaka.Analytic.SingularLocus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Harmonic.MeanValue
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
import Mathlib.Analysis.Normed.Module.Connected
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Order.Disjointed
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Hironaka.Manifold.HolomorphicMaps
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Filter.Germ.Basic
import Hironaka.Analytic.HolomorphicGermNoetherian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Indicator
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.Compact
import Hironaka.Analytic.HolomorphicAnalytic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Hironaka.Analytic.LastVariableTaylorDivision
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Hironaka.Coherence.FiniteGeneratorIdealDescent
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Function.Jacobian
import Hironaka.Analytic.IdealPresentation
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Convex.Deriv
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupIsomorphismOff
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Hironaka.Blowup.BlowupCompact
import Hironaka.Analytic.HolomorphicBoundedQuotient
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.ENNReal.Real
import Hironaka.Analytic.AnalyticDescendingChain
import Hironaka.Blowup.BlowupSequences
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Hironaka.Blowup.BlowupFlatCoordinates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Analytic.RegularPatchNeighborhood
set_option autoImplicit false

/-!
# Dimension bounds for analytic subsets

For a subset `A` of a complex manifold:

* `DimLE A p`: every regular point of `A` has dimension `≤ p` (`dim A ≤ p`);
* `LocDimGE A x q`: every neighbourhood of `x` contains a regular point of `A` of dimension `≥ q`
  (`dim_x A ≥ q`);

Basic facts: the two local bounds are compatible; a regular point of dimension `k` has local dimension exactly `k`
(`locDimGE_of_regularAtDim`); every point of an analytic set has local dimension `≥ 0` (density of the regular
locus); and a point of local dimension `≤ 0` is isolated: otherwise it lies on a positive-dimensional irreducible
component, which fills `A` near one of its top-dimensional regular points.
-/

open Set Filter Topology

namespace Hironaka.AnalyticDimensionBasics

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `dim A ≤ p`: every regular point of `A` has dimension at most `p`. -/
def DimLE (A : Set M) (p : ℕ) : Prop :=
  ∀ y k, RegularAtDim (n := n) A y k → k ≤ p

/-- `dim_x A ≥ q`: every neighbourhood of `x` contains a regular point of `A` of dimension at
least `q`. -/
def LocDimGE (A : Set M) (x : M) (q : ℕ) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ y ∈ U, ∃ k, q ≤ k ∧ RegularAtDim (n := n) A y k

omit [IsComplexManifold n M] in
/-- A regular point of dimension `k` has local dimension `≥ k`. -/
theorem locDimGE_of_regularAtDim {A : Set M} {x : M} {k : ℕ} (hx : RegularAtDim (n := n) A x k) :
    LocDimGE (n := n) A x k :=
  fun _ hU => ⟨x, mem_of_mem_nhds hU, k, le_rfl, hx⟩

end Hironaka.AnalyticDimensionBasics
