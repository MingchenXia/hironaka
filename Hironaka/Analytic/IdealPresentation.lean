/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicIdealSheaves
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.EReal.Inv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false

/-!
# Generators of a local presentation

Every generator of a local presentation of an ideal sheaf is a member of the ideal.

Declarations:
* `mem_of_isPresentation`
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealWeightComparison

noncomputable section

open Hironaka.HolomorphicIdealSheaves

/-! ### Monotonicity, well-definedness and boundedness of ideal weights -/

section Ideal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Every generator of a local presentation is a member of the ideal it
presents. -/
theorem mem_of_isPresentation {𝔞 : GermIdeal n M} {U : Set M} (hU : IsOpen U)
    {x : M} (hxU : x ∈ U) {N : ℕ} {g : Fin N → M → ℂ}
    (hgdiff : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U)
    (hgiff : ∀ y ∈ U, ∀ k, 𝔞.mem y k ↔ IsInSpanAt (n := n) (· ∈ range g) y k)
    (i : Fin N) : 𝔞.mem x (g i) := by
  have hhol : HolomorphicAt n (g i) x :=
    Filter.eventually_of_mem (hU.mem_nhds hxU)
      fun y hy => (hgdiff i y hy).mdifferentiableAt (hU.mem_nhds hy)
  refine (hgiff x hxU (g i)).mpr ?_
  exact isInSpanAt_of_eq_mul (S := fun s => s ∈ range g) ⟨i, rfl⟩ hhol
    (holomorphicAt_const 1) (Filter.Eventually.of_forall fun y => (one_mul _).symm)

end Ideal

end

end Hironaka.IdealWeightComparison
