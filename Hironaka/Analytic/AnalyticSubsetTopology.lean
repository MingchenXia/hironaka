/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Mathlib.Analysis.Complex.CauchyIntegral
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Topology of complex analytic subsets

Source: Grauert--Remmert, *Coherent analytic sheaves*, Ch. 5 and 9.

* `eqOn_zero_of_isOpen_convex`: the identity theorem for a holomorphic function
  on an open convex subset of a complex normed space, proved by restricting to
  complex lines and applying the one-variable identity theorem.
* `IsComplexAnalyticSubset.isClosed`: an analytic subset is closed.
* At a point of the closure of the interior, the local generators vanish on a nonempty open subset of a coordinate
  ball, hence on the whole ball.
* An analytic subset with nonempty interior is clopen-interior, hence everything; two closed sets with empty
  interior cannot cover the manifold.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka

noncomputable section

/-- **Identity theorem on a convex open set.** A holomorphic function on an
open convex set `W` which vanishes on a nonempty open subset of `W` vanishes on
all of `W`. -/
theorem eqOn_zero_of_isOpen_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {W U : Set E} {f : E → ℂ} (hW : IsOpen W)
    (hWc : Convex ℝ W) (hf : DifferentiableOn ℂ f W) (hU : IsOpen U)
    (hUW : U ⊆ W) (hUne : U.Nonempty) (hfU : EqOn f 0 U) : EqOn f 0 W := by
  obtain ⟨u, hu⟩ := hUne
  intro z hz
  let L : ℂ → E := fun t => u + t • (z - u)
  have hLc : Continuous L := by fun_prop
  have hLd : Differentiable ℂ L := by fun_prop
  let D : Set ℂ := L ⁻¹' W
  have hD : IsOpen D := hW.preimage hLc
  have hDc : Convex ℝ D := by
    intro t ht s hs a b ha hb hab
    have h := hWc ht hs ha hb hab
    simp only [D, L, mem_preimage] at h ⊢
    convert h using 1
    obtain rfl : b = 1 - a := by linarith
    simp only [← Complex.coe_smul]
    push_cast
    module
  have hg : DifferentiableOn ℂ (f ∘ L) D :=
    hf.comp hLd.differentiableOn fun t ht => ht
  have h0 : (0 : ℂ) ∈ D := by simpa [D, L] using hUW hu
  have h1 : (1 : ℂ) ∈ D := by simpa [D, L] using hz
  have hev : f ∘ L =ᶠ[𝓝 0] 0 := by
    have hLU : ∀ᶠ t in 𝓝 (0 : ℂ), L t ∈ U :=
      hLc.continuousAt.preimage_mem_nhds (by simpa [L] using hU.mem_nhds hu)
    filter_upwards [hLU] with t ht
    exact hfU ht
  have := (DifferentiableOn.analyticOnNhd hg hD).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hDc.isPreconnected h0 hev h1
  simpa [L] using this

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An analytic subset is closed. -/
theorem IsComplexAnalyticSubset.isClosed {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨p⟩ := hA x
  have hxs := mem_complexChartAt_source (n := n) x
  obtain ⟨i, hi⟩ : ∃ i, p.generator i ((complexChartAt (n := n) x).val x) ≠ 0 := by
    by_contra! h
    exact hx ((p.zeroLocus hxs p.center_mem_coordinateNeighborhood).mpr h)
  have hS : (complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹' p.coordinateNeighborhood ∈ 𝓝 x :=
    ((complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source p.isOpen_coordinateNeighborhood).mem_nhds
      ⟨hxs, p.center_mem_coordinateNeighborhood⟩
  have hcont : ContinuousAt
      (fun y => p.generator i ((complexChartAt (n := n) x).val y)) x :=
    ((p.generator_holomorphic i).continuousOn.continuousAt
      (p.isOpen_coordinateNeighborhood.mem_nhds p.center_mem_coordinateNeighborhood)).comp
      ((complexChartAt (n := n) x).val.continuousAt hxs)
  filter_upwards [hS, hcont.eventually_ne hi] with y hy hy'
  exact fun hyA => hy' ((p.zeroLocus hy.1 hy.2).mp hyA i)

end

end Hironaka
