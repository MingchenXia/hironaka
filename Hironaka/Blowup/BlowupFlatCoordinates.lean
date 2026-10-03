/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.CoordinatePlaneDivision
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Flattening coordinates of a smooth centre

Let `C ⊆ M` be regular of dimension `k` at `y₀`: in the preferred chart `e` at `y₀` a local
biholomorphism `Φ` flattens `C` onto `ℂᵏ × 0`.  The functions
`flatCoord Φ i = (Φ ∘ e)ᵢ` are holomorphic on `flatDomain Φ = e.source ∩ e⁻¹ Φ.source`, the
ones with `i ≥ k` lie in the ideal `𝓘_C`, and (Hadamard) they generate `𝓘_C` there:

* `holomorphicAt_flatCoord`, `flatCoord_mem_vanishingIdeal`;
* `exists_eq_sum_flatCoord`: every germ of `𝓘_C` at a point of `flatDomain Φ` is
  `∑_{i ≥ k} bᵢ · flatCoord Φ i` with `bᵢ` holomorphic.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.BlowupFlatCoordinates

open Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem HolomorphicAt.inv {f : M → ℂ} {x : M} (hf : HolomorphicAt n f x) (hx : f x ≠ 0) :
    HolomorphicAt n (fun y => (f y)⁻¹) x := by
  filter_upwards [hf.eventually, hf.continuousAt.eventually (isOpen_ne.mem_nhds hx)] with y hy hy0
  exact (differentiableAt_inv hy0).mdifferentiableAt.comp y hy.mdifferentiableAt

variable {y₀ : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))

/-- The flattening coordinates `(Φ ∘ e)ᵢ`. -/
def flatCoord (i : Fin n) : M → ℂ := fun y => Φ.toFun (chartAt (ComplexModel n) y₀ y) i

/-- The domain of the flattening coordinates. -/
def flatDomain : Set M := (chartAt (ComplexModel n) y₀).source ∩ chartAt (ComplexModel n) y₀ ⁻¹' Φ.source

theorem isOpen_flatDomain : IsOpen (flatDomain Φ) :=
  (chartAt (ComplexModel n) y₀).isOpen_inter_preimage Φ.isOpen_source

theorem mem_flatDomain_self : y₀ ∈ flatDomain Φ :=
  ⟨mem_chart_source _ y₀, Φ.center_mem_source⟩

theorem mdifferentiableAt_chart {y : M} (hy : y ∈ (chartAt (ComplexModel n) y₀).source) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) y₀) y :=
  ((contMDiffOn_chart (n := ∞)).contMDiffAt
    ((chartAt (ComplexModel n) y₀).open_source.mem_nhds hy)).mdifferentiableAt (by simp)

theorem mdifferentiableAt_chart_symm {z : ComplexModel n}
    (hz : z ∈ (chartAt (ComplexModel n) y₀).target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) y₀).symm z :=
  ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
    ((chartAt (ComplexModel n) y₀).open_target.mem_nhds hz)).mdifferentiableAt (by simp)

/-- A function on `ℂⁿ` holomorphic near `Φ (e y)` pulls back to a holomorphic germ at `y`. -/
theorem holomorphicAt_comp_flat {G : ComplexModel n → ℂ} {y : M} (hy : y ∈ flatDomain Φ)
    (hG : ∀ᶠ u in 𝓝 (Φ.toFun (chartAt (ComplexModel n) y₀ y)), DifferentiableAt ℂ G u) :
    HolomorphicAt n (fun y' => G (Φ.toFun (chartAt (ComplexModel n) y₀ y'))) y := by
  have hcont : ContinuousAt (fun y' => Φ.toFun (chartAt (ComplexModel n) y₀ y')) y :=
    ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).continuousAt).comp
      ((chartAt (ComplexModel n) y₀).continuousAt hy.1)
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy, hcont.eventually hG] with y' hy' hG'
  have hΦ : DifferentiableAt ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y') :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy'.2)
  exact (hG'.comp _ hΦ).mdifferentiableAt.comp y' (mdifferentiableAt_chart hy'.1)

theorem holomorphicAt_flatCoord (i : Fin n) {y : M} (hy : y ∈ flatDomain Φ) :
    HolomorphicAt n (flatCoord Φ i) y :=
  holomorphicAt_comp_flat Φ (G := fun u => u i) hy
    (Eventually.of_forall fun _ =>
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt)

variable {C : Set M} {k : ℕ}

theorem flatCoord_mem_vanishingIdeal
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {i : Fin n} (hi : k ≤ i.1) {y : M} (hy : y ∈ flatDomain Φ) :
    (vanishingIdeal (n := n) C).mem y (flatCoord Φ i) := by
  refine ⟨holomorphicAt_flatCoord Φ i hy, ?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with y' hy' hC
  exact (hflat hy'.1 hy'.2).mp hC i hi

/-- The chart-and-flattening inverse `u ↦ e⁻¹ (Φ⁻¹ u)` is continuous at `Φ (e y)` and sends it
back to `y`. -/
theorem tendsto_flatInverse {y : M} (hy : y ∈ flatDomain Φ) :
    Tendsto (fun u => (chartAt (ComplexModel n) y₀).symm (Φ.invFun u))
      (𝓝 (Φ.toFun (chartAt (ComplexModel n) y₀ y))) (𝓝 y) := by
  have hq : Φ.toFun ((chartAt (ComplexModel n) y₀) y) ∈ Φ.target := Φ.mapsTo_toFun hy.2
  have h1 : Φ.invFun (Φ.toFun ((chartAt (ComplexModel n) y₀) y)) = (chartAt (ComplexModel n) y₀) y := Φ.left_inv _ hy.2
  have hinv : ContinuousAt Φ.invFun (Φ.toFun ((chartAt (ComplexModel n) y₀) y)) :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hq)).continuousAt
  have hsymm : ContinuousAt (chartAt (ComplexModel n) y₀).symm (Φ.invFun (Φ.toFun ((chartAt (ComplexModel n) y₀) y))) := by
    rw [h1]; exact (chartAt (ComplexModel n) y₀).continuousAt_symm ((chartAt (ComplexModel n) y₀).map_source hy.1)
  have := hsymm.comp hinv
  rw [ContinuousAt, Function.comp_apply, h1, (chartAt (ComplexModel n) y₀).left_inv hy.1] at this
  exact this

theorem flatInverse_mem {u : ComplexModel n} (hu : u ∈ Φ.target)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) :
    (chartAt (ComplexModel n) y₀).symm (Φ.invFun u) ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) y₀ ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u))) = u := by
  have h1 : Φ.invFun u ∈ Φ.source := Φ.mapsTo_invFun hu
  have h2 := (chartAt (ComplexModel n) y₀).right_inv (hΦsrc h1)
  refine ⟨⟨(chartAt (ComplexModel n) y₀).map_target (hΦsrc h1), ?_⟩, ?_⟩
  · rw [mem_preimage, h2]; exact h1
  · rw [h2]; exact Φ.right_inv u hu

theorem flatInverse_flat {y : M} (hy : y ∈ flatDomain Φ) :
    (chartAt (ComplexModel n) y₀).symm (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) y₀ y))) = y := by
  rw [Φ.left_inv _ hy.2, (chartAt (ComplexModel n) y₀).left_inv hy.1]

/-- **Hadamard's lemma in flattening coordinates.** -/
theorem exists_eq_sum_flatCoord
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {y : M} (hy : y ∈ flatDomain Φ) {a : M → ℂ} (ha : (vanishingIdeal (n := n) C).mem y a) :
    ∃ b : Fin n → M → ℂ, (∀ i : Fin n, i.1 < k → b i = 0) ∧
      (∀ i, HolomorphicAt n (b i) y) ∧
      a =ᶠ[𝓝 y] fun y' => ∑ i, b i y' * flatCoord Φ i y' := by
  classical
  set q := Φ.toFun ((chartAt (ComplexModel n) y₀) y) with hq_def
  have hqT : q ∈ Φ.target := Φ.mapsTo_toFun hy.2
  by_cases hq : q ∈ complexCoordinatePlane n k
  · set F : ComplexModel n → ℂ := fun u => a ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u)) with hF_def
    have hTnhds : ∀ᶠ u in 𝓝 q, u ∈ Φ.target := Φ.isOpen_target.mem_nhds hqT
    have hFd : ∀ᶠ u in 𝓝 q, DifferentiableAt ℂ F u := by
      filter_upwards [hTnhds, (tendsto_flatInverse Φ hy).eventually ha.1.eventually] with u hu hau
      have hm := flatInverse_mem Φ hu hΦsrc
      have hinvT : Φ.invFun u ∈ (chartAt (ComplexModel n) y₀).target := hΦsrc (Φ.mapsTo_invFun hu)
      have h1 := hau.mdifferentiableAt.comp (Φ.invFun u) (mdifferentiableAt_chart_symm hinvT)
      exact (mdifferentiableAt_iff_differentiableAt.mp h1).comp u
        (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hu))
    have hFvan : ∀ᶠ u in 𝓝 q, u ∈ complexCoordinatePlane n k → F u = 0 := by
      filter_upwards [hTnhds, (tendsto_flatInverse Φ hy).eventually ha.2] with u hu hau hplane
      obtain ⟨hm, hΦu⟩ := flatInverse_mem Φ hu hΦsrc
      exact hau ((hflat hm.1 hm.2).mpr (by rw [hΦu]; exact hplane))
    obtain ⟨H, hH0, hHd, hHeq⟩ :=
      CoordinatePlaneDivision.exists_eq_sum_coord_mul (n - k) k rfl hq hFd hFvan
    refine ⟨fun i y' => H i (Φ.toFun ((chartAt (ComplexModel n) y₀) y')), fun i hi => by funext y'; simp [hH0 i hi], fun i =>
      holomorphicAt_comp_flat Φ hy (hHd i), ?_⟩
    have hcont : ContinuousAt (fun y' => Φ.toFun ((chartAt (ComplexModel n) y₀) y')) y :=
      ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).continuousAt).comp
        ((chartAt (ComplexModel n) y₀).continuousAt hy.1)
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy, hcont.eventually hHeq] with y' hy' h'
    have : F (Φ.toFun ((chartAt (ComplexModel n) y₀) y')) = a y' := by simp only [hF_def]; rw [flatInverse_flat Φ hy']
    rw [← this, h']
    exact Finset.sum_congr rfl fun i _ => by simp only [flatCoord]; ring
  · obtain ⟨i₀, hi₀, hqi₀⟩ : ∃ i : Fin n, k ≤ i.1 ∧ q i ≠ 0 := by
      simpa [complexCoordinatePlane] using hq
    have hc := holomorphicAt_flatCoord Φ i₀ hy
    refine ⟨fun i => if i = i₀ then fun y' => a y' * (flatCoord Φ i₀ y')⁻¹ else 0,
      fun i hi => ?_, fun i => ?_, ?_⟩
    · have : i ≠ i₀ := fun h => by subst h; omega
      simp [this]
    · by_cases hi : i = i₀
      · simp only [hi, if_true]; exact ha.1.mul (HolomorphicAt.inv hc hqi₀)
      · simp only [hi, if_false]; exact holomorphicAt_const 0
    · filter_upwards [hc.continuousAt.eventually (isOpen_ne.mem_nhds hqi₀)] with y' hy'
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
      simp only [if_true]
      field_simp [hy']

end

end Hironaka.BlowupFlatCoordinates
