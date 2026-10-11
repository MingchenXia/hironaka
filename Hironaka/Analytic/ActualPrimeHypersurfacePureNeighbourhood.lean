/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualPrimeHolomorphicRegularZeros
import Hironaka.Analytic.GermComponentDimension
import Hironaka.Analytic.AnalyticJacobianCriterion


set_option autoImplicit false

/-!
# Pure hypersurface neighbourhood produced by the original prime equation

Complete mathematical statement and ENTIRE proof precede the baseline.
Actual original regular-zero frequency supplies the dimension internally.
-/

open Hironaka

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Hironaka.ActualPrimeHypersurfacePureNeighbourhood

open HolGerm

private theorem frequently_original_regular_zeros {m : ℕ}
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq)) :
    ∃ v : ComplexModel (m + 1), v ≠ 0 ∧
      ∃ᶠ x in 𝓝 0, q x = 0 ∧ DifferentiableAt ℂ q x ∧ fderiv ℂ q x v ≠ 0 := by
  let e := euclideanSnocCLE m
  let p : ComplexModel m × ℂ → ℂ := fun x => q (e.symm x)
  have hp := eventually_differentiableAt_comp_clm
    (e.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1)) hq
  have hP : Prime (HolGerm.mk p hp) := by
    change Prime (comapEquiv e.symm (HolGerm.mk q hq))
    exact (MulEquiv.prime_iff (e := (comapEquiv e.symm).toMulEquiv)).mpr hQ
  obtain ⟨v, hv, hf⟩ :=
    ActualPrimeHolomorphicRegularZeros.exists_direction_frequently_regular_zeros p hp hP
  let w : ComplexModel (m + 1) := e.symm v
  have hw : w ≠ 0 := by
    intro hzero
    apply hv
    apply e.symm.injective
    rw [map_zero]
    exact hzero
  have ht : Tendsto (fun x : ComplexModel m × ℂ => e.symm x) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using e.symm.continuous.tendsto (0 : ComplexModel m × ℂ)
  refine ⟨w, hw, Filter.Tendsto.frequently_map (fun x => e.symm x) ht ?_
    (hf.and_eventually (ht.eventually hq))⟩
  rintro x ⟨⟨hpx, hpAt, hpd⟩, hqAt⟩
  have hc : HasFDerivAt p
      ((fderiv ℂ q (e.symm x)).comp
        (e.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1))) x :=
    hqAt.hasFDerivAt.comp x
      (e.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1)).hasFDerivAt
  have heq := hpAt.hasFDerivAt.unique hc
  refine ⟨hpx, hqAt, fun hzero => hpd ?_⟩
  rw [heq]
  exact hzero

/-- The original prime equation produces one pure hypersurface neighbourhood
before all smaller open representatives; no dimension or density is assumed. -/
theorem exists_pure_hypersurface_neighbourhood {m : ℕ}
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq)) :
    ∃ Ω : Set (ComplexModel (m + 1)), IsOpen Ω ∧ (0 : ComplexModel (m + 1)) ∈ Ω ∧
      ∀ Ω' : Set (ComplexModel (m + 1)), IsOpen Ω' → Ω' ⊆ Ω →
        (∀ {y : ComplexModel (m + 1)} {k : ℕ},
          RegularAtDim (n := m + 1) ({x | q x = 0} ∩ Ω') y k → k = m) ∧
        {x | q x = 0} ∩ Ω' ⊆ closure (regularLocus (n := m + 1) ({x | q x = 0} ∩ Ω') m) := by
  have hB := (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).2
  obtain ⟨v, _hv, hf⟩ := frequently_original_regular_zeros q hq hQ
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp hq
  have hqN : DifferentiableOn ℂ q (ball (0 : ComplexModel (m + 1)) R) :=
    fun x hx => (hball x hx).differentiableWithinAt
  apply GermComponentDimension.exists_pure_nhds_dim hB
  intro ε hε
  obtain ⟨x, hx, hqx, hqAt, hd⟩ := Filter.frequently_iff.mp hf
    (ball_mem_nhds (0 : ComplexModel (m + 1)) (lt_min hε hR))
  have hxε : x ∈ ball (0 : ComplexModel (m + 1)) ε :=
    ball_subset_ball (min_le_left ε R) hx
  have hxR : x ∈ ball (0 : ComplexModel (m + 1)) R :=
    ball_subset_ball (min_le_right ε R) hx
  let g : Fin 1 → ComplexModel (m + 1) → ℂ := fun _ => q
  have hli : LinearIndependent ℂ (fun i : Fin 1 => fderiv ℂ (g i) x) := by
    rw [linearIndependent_unique_iff]
    intro hz
    apply hd
    rw [hz]
    rfl
  obtain ⟨Φ, _hΦN, hΦ0, hΦflat⟩ :=
    AnalyticJacobianCriterion.exists_flattening_of_localCompleteIntersection
      (S := {z | q z = 0}) (N := ball (0 : ComplexModel (m + 1)) R)
      (q := x) (g := g) isOpen_ball hxR hqx (fun _ => hqN)
      (fun z _ => ⟨fun hz _ => hz, fun hz => hz 0⟩) hli
  have hchart : (complexChartAt (n := m + 1) x).val =
      OpenPartialHomeomorph.refl (ComplexModel (m + 1)) := by
    simp [complexChartAt, chartAt_self_eq]
  have hreg : RegularAtDim (n := m + 1) {z | q z = 0} x m := by
    unfold RegularAtDim
    rw [hchart]
    refine ⟨Nat.le_succ m, hqx, Φ, subset_univ _, hΦ0, ?_⟩
    intro y _ hy
    simpa only [Nat.add_sub_cancel, OpenPartialHomeomorph.refl_apply, id_eq] using hΦflat y hy
  refine ⟨x, hxε, univ, isOpen_univ, mem_univ _, ?_⟩
  simpa only [inter_univ] using hreg

end Hironaka.ActualPrimeHypersurfacePureNeighbourhood
