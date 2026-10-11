/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualPrimeHolomorphicRegularZeros
import Hironaka.Analytic.ActualPrimeRegularFiniteAvoidance
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Coherence.OkaRelationSheaf


set_option autoImplicit false

/-! # A genuine same-piece differential and finite avoidance

The differential is internally produced from the original prime and
then made one of the actual finite tests. No unrelated frequent sets
are silently intersected.
-/

open Hironaka

noncomputable section
open Set Filter
open scoped Topology
namespace Hironaka.ActualPrimeRegularDifferentialAvoidance
open HolGerm OkaRelationSheaf AnalyticGermDecomposition

private theorem exists_original_direction {m : ℕ}
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq)) :
    ∃ v : ComplexModel (m + 1), v ≠ 0 ∧
      ∃ᶠ x in 𝓝 (0 : ComplexModel (m + 1)),
        q x = 0 ∧ DifferentiableAt ℂ q x ∧ fderiv ℂ q x v ≠ 0 := by
  let L := euclideanSnocCLE m
  let qp := fun y : ComplexModel m × ℂ => q (L.symm y)
  have hqp : ∀ᶠ y in 𝓝 (0 : ComplexModel m × ℂ), DifferentiableAt ℂ qp y :=
    eventually_differentiableAt_comp_clm
      (L.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1)) hq
  have hQp : Prime (HolGerm.mk qp hqp) := by
    change Prime (comapEquiv L.symm (HolGerm.mk q hq))
    exact (MulEquiv.prime_iff (e := (comapEquiv L.symm).toMulEquiv)).mpr hQ
  obtain ⟨vp, hvp, hf⟩ :=
    ActualPrimeHolomorphicRegularZeros.exists_direction_frequently_regular_zeros qp hqp hQp
  let v := L.symm vp
  have hv : v ≠ 0 := by
    intro hv0
    apply hvp
    apply L.symm.injective
    simpa only [map_zero] using hv0
  have hqd : ∀ᶠ y in 𝓝 (0 : ComplexModel m × ℂ), DifferentiableAt ℂ q (L.symm y) :=
    (HolGerm.tendsto_clm_nhds_zero
      (L.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1))).eventually hq
  refine ⟨v, hv, ?_⟩
  rw [Filter.frequently_iff] at hf ⊢
  intro S hS
  have hLS : ∀ᶠ y in 𝓝 (0 : ComplexModel m × ℂ), L.symm y ∈ S :=
    (HolGerm.tendsto_clm_nhds_zero
      (L.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1))).eventually hS
  obtain ⟨y, ⟨hyS, hqy⟩, hq0, hdy, hne⟩ := hf (hLS.and hqd)
  have hcomp : HasFDerivAt qp
      ((fderiv ℂ q (L.symm y)).comp
        (L.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1))) y :=
    hqy.hasFDerivAt.comp y
      (L.symm : (ComplexModel m × ℂ) →L[ℂ] ComplexModel (m + 1)).hasFDerivAt
  have heq := DFunLike.congr_fun (hcomp.unique hdy.hasFDerivAt) vp
  simp only [ContinuousLinearMap.comp_apply] at heq
  refine ⟨L.symm y, hyS, hq0, hqy, ?_⟩
  intro hz
  apply hne
  rw [← heq]
  exact hz

/-- The original prime itself produces a fixed nonzero differential,
simultaneously on the same regular piece avoiding all original tests. -/
theorem exists_direction_frequently_regular_avoiding_tests {m : ℕ} {ι : Type*} [Fintype ι]
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq))
    (a : ι → ComplexModel (m + 1) → ℂ)
    (ha : ∀ i, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (a i) x)
    (hnot : ∀ i, ¬HolGerm.mk q hq ∣ HolGerm.mk (a i) (ha i)) :
    ∃ v : ComplexModel (m + 1), v ≠ 0 ∧
      ∃ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), q x = 0 ∧
        RegularAtDim (n := m + 1) {y | q y = 0} x m ∧
        DifferentiableAt ℂ q x ∧ fderiv ℂ q x v ≠ 0 ∧ ∀ i, a i x ≠ 0 := by
  classical
  obtain ⟨v, hv, hfreq⟩ := exists_original_direction q hq hQ
  obtain ⟨H, hHo, hH0, hqH⟩ := OkaRelationSheaf.HolAt.exists_isOpen hq
  let δ := fun x => fderiv ℂ q x v
  have hδH : DifferentiableOn ℂ δ H :=
    Hironaka.differentiableOn_fderiv_apply_of_isOpen hqH hHo v
  have hδ : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ δ x := by
    filter_upwards [hHo.mem_nhds hH0] with x hx
    exact hδH.differentiableAt (hHo.mem_nhds hx)
  have hnotδ : ¬HolGerm.mk q hq ∣ HolGerm.mk δ hδ := by
    intro hdiv
    have hI := (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1
    have hmem : HolGerm.mk δ hδ ∈ vanishingIdeal {x | q x = 0} := by
      rw [hI]
      exact Ideal.mem_span_singleton.mpr hdiv
    have hevent : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), q x = 0 → δ x = 0 :=
      mem_vanishingIdeal_mk.mp hmem
    obtain ⟨x, ⟨hqx, _hqd, hdx⟩, hzero⟩ := (hfreq.and_eventually hevent).exists
    exact hdx (hzero hqx)
  let tests : Option ι → ComplexModel (m + 1) → ℂ := fun i => i.elim δ a
  have htests : ∀ i, ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (tests i) x := by
    intro i
    cases i with
    | none => exact hδ
    | some i => exact ha i
  have htestnot : ∀ i, ¬HolGerm.mk q hq ∣ HolGerm.mk (tests i) (htests i) := by
    intro i
    cases i with
    | none => exact hnotδ
    | some i => exact hnot i
  have hsame := ActualPrimeRegularFiniteAvoidance.frequently_regular_zero_avoiding_finite_family
    q hq hQ tests htests htestnot
  refine ⟨v, hv, (hsame.and_eventually (hHo.mem_nhds hH0)).mono ?_⟩
  intro x hx
  exact ⟨hx.1.1, hx.1.2.1, hqH.differentiableAt (hHo.mem_nhds hx.2),
    hx.1.2.2 none, fun i => hx.1.2.2 (some i)⟩

end Hironaka.ActualPrimeRegularDifferentialAvoidance
