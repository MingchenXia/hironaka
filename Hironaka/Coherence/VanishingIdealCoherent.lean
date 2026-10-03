/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Analytic.IdealPresentation
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
import Hironaka.Analytic.HolomorphicIdealSheaves
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The vanishing ideal of a closed submanifold is coherent

This module supplies the missing coherence.

Coherence is the conjunction of those two, with the family

  `gᵢ = flatCoord Φ i` for `i ≥ k`,  `gᵢ = 0` for `i < k`,

Together with the trivial chart off `C`, where `𝓘_C` is the unit ideal.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.VanishingIdealCoherent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `𝓘_A` absorbs holomorphic combinations of its own members. -/
theorem mem_vanishingIdeal_of_isInSpanAt {A : Set M} {N : ℕ} {g : Fin N → M → ℂ} {y : M}
    (hg : ∀ i, (vanishingIdeal (n := n) A).mem y (g i)) {f : M → ℂ}
    (hf : IsInSpanAt (n := n) (· ∈ range g) y f) :
    (vanishingIdeal (n := n) A).mem y f := by
  obtain ⟨hfhol, K, s, a, hs, -, hsum⟩ := hf
  refine ⟨hfhol, ?_⟩
  have hzero : ∀ᶠ y' in 𝓝 y, ∀ i, y' ∈ A → g i y' = 0 :=
    eventually_all.mpr fun i => (hg i).2
  filter_upwards [hsum, hzero] with y' h1 h2 hy'A
  rw [h1]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨i, hi⟩ := hs j
  rw [← hi, h2 i hy'A, mul_zero]

/-- **The vanishing ideal of a closed complex submanifold is coherent.** -/
theorem isCoherent_vanishingIdeal {C : Set M} (hC : IsClosedSubmanifold n C) :
    (vanishingIdeal (n := n) C).IsCoherent := by
  classical
  intro x
  by_cases hx : x ∈ C
  · obtain ⟨k, -, -, Φ, hΦsrc, -, hflat⟩ := hC.2 x hx
    refine ⟨flatDomain Φ, isOpen_flatDomain Φ, mem_flatDomain_self Φ, n,
      fun i => if k ≤ i.1 then flatCoord Φ i else 0, fun i => ?_, fun y hy f => ?_⟩
    · by_cases hik : k ≤ i.1
      · simp only [hik, if_true]
        exact fun z hz => (holomorphicAt_flatCoord Φ i hz).mdifferentiableAt.mdifferentiableWithinAt
      · simp only [hik, if_false]
        exact mdifferentiableOn_const
    · constructor
      · intro hf
        obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy hf
        refine ⟨hf.1, n, fun i => if k ≤ i.1 then flatCoord Φ i else 0, b,
          fun i => ⟨i, rfl⟩, hbhol, ?_⟩
        filter_upwards [hbeq] with y' h1
        rw [h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hik : k ≤ i.1
        · simp [hik]
        · rw [hb0 i (Nat.lt_of_not_le hik)]
          simp
      · refine mem_vanishingIdeal_of_isInSpanAt fun i => ?_
        by_cases hik : k ≤ i.1
        · simpa only [hik, if_true] using flatCoord_mem_vanishingIdeal Φ hflat hik hy
        · simp only [hik, if_false]
          exact ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩
  · refine ⟨Cᶜ, hC.1.isOpen_compl, hx, 1, fun _ => fun _ => (1 : ℂ),
      fun i => mdifferentiableOn_const, fun y hy f => ?_⟩
    constructor
    · intro hf
      exact isInSpanAt_of_eq_mul ⟨0, rfl⟩ hf.1 hf.1 (Eventually.of_forall fun _ => by simp)
    · intro hf
      refine ⟨hf.1, ?_⟩
      filter_upwards [hC.1.isOpen_compl.mem_nhds hy] with y' h1 h2
      exact absurd h2 h1

end

end Hironaka.VanishingIdealCoherent
