/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.SingularLocus
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
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Hironaka.Manifold.HolomorphicMaps
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Resolution.StrictTransformComposition
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Harmonic.MeanValue
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
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Analytic.ComplexAnalyticSubvarieties
set_option autoImplicit false

/-!
# Transporting regular patches across a local biholomorphism

Source: CT22, Lemma 4.3 (first inequality: "identify absolutely continuous masses through the biholomorphism `W̃ \ E
≅ W \ C`").

Let `g: Z → Y` be holomorphic, `W ⊆ Y` and `W̃ ⊆ Z` subvarieties of the same dimension which correspond under `g` on
an open set `O` (`u ∈ W̃ ↔ g u ∈ W` for `u ∈ O`), and `P` a regular patch of `W` with parameter `w₀` over `g z`,
where `z ∈ O` is not exceptional. Write `F = φ_{P} ∘ g ∘ φ_z⁻¹` for the chart expression of `g` (`φ_z` the preferred
chart at `z`, `φ_P` the one at the centre of `P`); it is a local biholomorphism at `φ_z z`. Put `Φ' = τ ∘ Φ_P ∘ F`
with `τ` the translation by `-(w₀, 0)`. This is a flattening of `W̃` at `z`, so it defines a regular patch `Q` with
`g (Q (w - w₀)) = P w` for `w` near `w₀`. Its parametrization is `F⁻¹ ∘ γ_P ∘ (· + w₀)`, so `γ_P = F ∘ γ_Q ∘ (· -
w₀)` near `w₀`, and by the chain rule the restriction of `g^*β` along `γ_Q` equals the restriction of `β` along
`γ_P`, for smooth forms `β` and for `ddᶜ` of smooth functions.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

namespace RegularPatchPullback

open Hironaka.BlowupSequences

noncomputable section

section Planar

variable {n : ℕ}

/-- Post-composition of a local holomorphic equivalence with the translation `x ↦ x - a`. -/
def subConst {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (a : ComplexModel n) : LocalHolomorphicEquivAt (n := n) p where
  source := Φ.source
  target := (fun x => x + a) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source
  isOpen_target := Φ.isOpen_target.preimage (continuous_add_const a)
  center_mem_source := Φ.center_mem_source
  toFun := fun u => Φ.toFun u - a
  invFun := fun x => Φ.invFun (x + a)
  toFun_holomorphic := Φ.toFun_holomorphic.sub_const a
  invFun_holomorphic :=
    Φ.invFun_holomorphic.comp (differentiableOn_id.add_const a) (fun _ hx => hx)
  mapsTo_toFun := fun u hu => by
    simpa only [mem_preimage, sub_add_cancel] using Φ.mapsTo_toFun hu
  mapsTo_invFun := fun _ hx => Φ.mapsTo_invFun hx
  left_inv := fun u hu => by
    simp only [sub_add_cancel]
    exact Φ.left_inv u hu
  right_inv := fun x hx => by
    simp only [Φ.right_inv _ hx, add_sub_cancel_right]

end Planar

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

end

end RegularPatchPullback

end Hironaka
