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
# Regular patches parametrize regular points

Let `Φ` flatten an analytic set `A` onto `ℂ^k × {0}` in the preferred chart `e_x` at a
point `x` (`RegularAtDim A x k`).  If `y ∈ A` lies in the chart source and `e_x y` lies in
the source of `Φ`, then `A` is also flattened at `y` in the preferred chart `e_y`, by

`Ψ := (· - Φ(e_x y)) ∘ Φ ∘ (e_x ∘ e_y⁻¹)`,

whose inverse is `e_y ∘ e_x⁻¹ ∘ Φ⁻¹ ∘ (· + Φ(e_x y))`.  The chart transition is
holomorphic because the manifold structure is holomorphic, and translating by
`Φ(e_x y) ∈ ℂ^k × {0}` preserves the coordinate plane.

Consequently the whole image of a `RegularPatch` lies in the regular locus of the
certified dimension, and the patch parametrization is continuous.

* `regularAtDim_of_flattening`, `eventually_regularAtDim`: openness of regularity in `A`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.RegularPatchNeighborhood

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Chart transitions of a complex manifold are holomorphic on their source. -/
theorem differentiableOn_chartTransition (e f : ComplexChart n M) :
    DifferentiableOn ℂ (chartTransition e f) (chartTransition e f).source := by
  have h := chartTransition_mem_groupoid e f
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have h1 := h.1
  simp only [contDiffPregroupoid] at h1
  simpa using h1.differentiableOn (by simp)

/-- Inverse chart transitions of a complex manifold are holomorphic on their target. -/
theorem differentiableOn_chartTransition_symm (e f : ComplexChart n M) :
    DifferentiableOn ℂ (chartTransition e f).symm (chartTransition e f).target := by
  have h := chartTransition_mem_groupoid e f
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have h1 := h.2
  simp only [contDiffPregroupoid] at h1
  simpa using h1.differentiableOn (by simp)

omit [IsComplexManifold n M] in
/-- Translating by a point of the coordinate plane preserves the plane. -/
theorem sub_mem_complexCoordinatePlane_iff {k : ℕ} {z c : ComplexModel n}
    (hc : c ∈ complexCoordinatePlane n k) :
    z - c ∈ complexCoordinatePlane n k ↔ z ∈ complexCoordinatePlane n k := by
  simp only [complexCoordinatePlane, mem_ofPred_eq, PiLp.sub_apply]
  constructor
  · intro h i hi
    have := h i hi
    rwa [hc i hi, sub_zero] at this
  · intro h i hi
    rw [h i hi, hc i hi, sub_zero]

/-- **Regularity propagates along a flattening.**  If `Φ` flattens `A` in the preferred
chart at `x`, then `A` is regular of the same dimension at every point `y ∈ A` of the chart
source with `e_x y` in the source of `Φ`. -/
theorem regularAtDim_of_flattening {A : Set M} {x y : M} {k : ℕ} (hk : k ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hflat : ∀ {y : M},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k))
    (hyA : y ∈ A) (hy : y ∈ (complexChartAt (n := n) x).val.source)
    (hyΦ : (complexChartAt (n := n) x).val y ∈ Φ.source) :
    RegularAtDim (n := n) A y k := by
  set ey := (complexChartAt (n := n) y).val with hey
  set T := chartTransition (complexChartAt (n := n) y) (complexChartAt (n := n) x) with hT
  set c := Φ.toFun ((complexChartAt (n := n) x).val y) with hc
  have hcPlane : c ∈ complexCoordinatePlane n k := (hflat hy hyΦ).1 hyA
  have hTsource :
      T.source = ey.target ∩ ey.symm ⁻¹' (complexChartAt (n := n) x).val.source := by
    simp [hT, chartTransition, hey]
  have hTapply : ∀ z, T z = (complexChartAt (n := n) x).val (ey.symm z) := fun z => rfl
  have hTholo := differentiableOn_chartTransition (complexChartAt (n := n) y)
    (complexChartAt (n := n) x)
  have hTsymmholo := differentiableOn_chartTransition_symm (complexChartAt (n := n) y)
    (complexChartAt (n := n) x)
  have hyey : y ∈ ey.source := mem_complexChartAt_source y
  let Ψ : LocalHolomorphicEquivAt (n := n) (ey y) :=
    { source := T.source ∩ T ⁻¹' Φ.source
      target := (fun v => v + c) ⁻¹' (Φ.target ∩ Φ.invFun ⁻¹' T.target)
      isOpen_source := T.isOpen_inter_preimage Φ.isOpen_source
      isOpen_target :=
        (Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target
          T.open_target).preimage (continuous_id.add continuous_const)
      center_mem_source := by
        refine ⟨?_, ?_⟩
        · rw [hTsource]
          exact ⟨ey.map_source hyey, by simpa [ey.left_inv hyey] using hy⟩
        · simpa [mem_preimage, hTapply, ey.left_inv hyey] using hyΦ
      toFun := fun z => Φ.toFun (T z) - c
      invFun := fun v => T.symm (Φ.invFun (v + c))
      toFun_holomorphic := by
        refine DifferentiableOn.sub_const ?_ c
        exact Φ.toFun_holomorphic.comp (hTholo.mono inter_subset_left)
          (fun z hz => hz.2)
      invFun_holomorphic := by
        refine hTsymmholo.comp ?_ (fun v hv => hv.2)
        exact Φ.invFun_holomorphic.comp ((differentiableOn_id.add_const c))
          (fun v hv => hv.1)
      mapsTo_toFun := by
        intro z hz
        refine ⟨?_, ?_⟩
        · simpa using Φ.mapsTo_toFun hz.2
        · simp only [mem_preimage, sub_add_cancel, Φ.left_inv _ hz.2]
          exact T.map_source hz.1
      mapsTo_invFun := by
        intro v hv
        refine ⟨T.map_target hv.2, ?_⟩
        simp only [mem_preimage, T.right_inv hv.2]
        exact Φ.mapsTo_invFun hv.1
      left_inv := by
        intro z hz
        simp only [sub_add_cancel, Φ.left_inv _ hz.2]
        exact T.left_inv hz.1
      right_inv := by
        intro v hv
        simp only [T.right_inv hv.2, Φ.right_inv _ hv.1, add_sub_cancel_right] }
  refine ⟨hk, hyA, Ψ, ?_, ?_, ?_⟩
  · intro z hz
    have := hz.1
    rw [hTsource] at this
    exact this.1
  · change Φ.toFun (T (ey y)) - c = 0
    rw [hTapply, ey.left_inv hyey, sub_self]
  · intro y' hy' hy'Ψ
    change ey y' ∈ T.source ∩ T ⁻¹' Φ.source at hy'Ψ
    change y' ∈ A ↔ Φ.toFun (T (ey y')) - c ∈ complexCoordinatePlane n k
    have hTy' : T (ey y') = (complexChartAt (n := n) x).val y' := by rw [hTapply, ey.left_inv hy']
    have hsrc := hy'Ψ.1
    rw [hTsource] at hsrc
    have hy'ex : y' ∈ (complexChartAt (n := n) x).val.source := by
      simpa [mem_preimage, ey.left_inv hy'] using hsrc.2
    have hy'Φ : (complexChartAt (n := n) x).val y' ∈ Φ.source := by
      simpa [mem_preimage, hTy'] using hy'Ψ.2
    rw [hTy', sub_mem_complexCoordinatePlane_iff hcPlane]
    exact hflat hy'ex hy'Φ

/-- **Regularity is relatively open.**  Near a regular point, every point of `A` is regular
of the same dimension. -/
theorem eventually_regularAtDim {A : Set M} {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) A x k) :
    ∀ᶠ y in 𝓝 x, y ∈ A → RegularAtDim (n := n) A y k := by
  obtain ⟨hk, -, Φ, -, -, hflat⟩ := hx
  have hsrc : (complexChartAt (n := n) x).val.source ∈ 𝓝 x :=
    (complexChartAt (n := n) x).val.open_source.mem_nhds (mem_complexChartAt_source x)
  have hΦ : (complexChartAt (n := n) x).val ⁻¹' Φ.source ∈ 𝓝 x :=
    ((complexChartAt (n := n) x).val.continuousAt (mem_complexChartAt_source x)).preimage_mem_nhds
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  filter_upwards [hsrc, hΦ] with y hy hyΦ hyA
  exact regularAtDim_of_flattening hk Φ hflat hyA hy hyΦ

end

end Hironaka.RegularPatchNeighborhood
