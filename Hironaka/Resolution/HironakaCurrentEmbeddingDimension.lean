/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RankDegeneracy

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-! # The actual current embedding dimension

Complete reduced ideal differentials produce the intrinsic finite value,
all of its analytic superlevels, the exact pure singular threshold, and an
internally attained singular maximum locus. No smooth-centre, transformation
presentation or Hilbert--Samuel descent certificate is an input.
-/

open Set Filter Module
open scoped Topology Manifold

namespace Hironaka.HironakaCurrentEmbeddingDimension

open Hironaka.HolomorphicIdealSheaves
open RankDegeneracy StokesSingularLocusAnalytic AnalyticJacobianSingularCore
open AnalyticDimensionBasics

open Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual complete reduced ideal's common differential kernel. -/
def embeddingDimension (A : Set M) (x : M) : ℕ :=
  finrank ℂ (tangentSpaceIn (complexChartAt (n := n) x) A x)

/-- The value is computed from all actual ideal germs in any true chart. -/
theorem embeddingDimension_eq_finrank_tangentSpaceIn (A : Set M) (x : M)
    (e : ComplexChart n M) (hxe : x ∈ e.val.source) :
    embeddingDimension (n := n) A x = finrank ℂ (tangentSpaceIn e A x) := by
  let e₀ := complexChartAt (n := n) x
  let D : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (fderiv ℂ (fun w => e.val (e₀.val.symm w)) (e₀.val x) :
      ComplexModel n →L[ℂ] ComplexModel n)
  have h₀ : x ∈ e₀.val.source := mem_complexChartAt_source x
  have hinj : Function.Injective D := injective_fderiv_transition e₀ e h₀ hxe
  have hsurj : Function.Surjective D := surjective_fderiv_transition e₀ e h₀ hxe
  have heq := ((tangentSpaceIn e A x).comap D).equivMapOfInjective D hinj |>.finrank_eq
  rw [Submodule.map_comap_eq_of_surjective hsurj] at heq
  unfold embeddingDimension
  rw [tangentSpaceIn_eq_comap e₀ e A h₀ hxe]
  exact heq

omit [IsComplexManifold n M] in
/-- The actual kernel dimension is bounded by the ambient dimension. -/
theorem embeddingDimension_le (A : Set M) (x : M) :
    embeddingDimension (n := n) A x ≤ n := by
  have h := (tangentSpaceIn (complexChartAt (n := n) x) A x).finrank_le
  simpa only [embeddingDimension, finrank_euclideanSpace, Fintype.card_fin] using h

/-- The genuine regular flattening computes the actual value exactly. -/
theorem embeddingDimension_eq_of_regularAtDim {A : Set M} {x : M} {d : ℕ}
    (hreg : RegularAtDim (n := n) A x d) : embeddingDimension (n := n) A x = d :=
  finrank_tangentSpaceIn_of_regularAtDim (complexChartAt (n := n) x)
    (mem_complexChartAt_source x) hreg

/-- Actual complete Cartan generators give exact rank-nullity for this
intrinsic value; no derivative-rank certificate is supplied. -/
theorem rank_add_embeddingDimension_of_cartanGenerators {A U : Set M}
    (hU : IsOpen U) {N : ℕ} {s : Fin N → M → ℂ}
    (hs : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U)
    (hspan : ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) A).mem y g ↔
      IsInSpanAt (n := n) (· ∈ range s) y g)
    (hzero : ∀ y ∈ U, (y ∈ A ↔ ∀ i, s i y = 0)) (e : ComplexChart n M)
    {y : M} (hyU : y ∈ U) (hye : y ∈ e.val.source) (hyA : y ∈ A) :
    finrank ℂ (Submodule.span ℂ
      (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y))) +
      embeddingDimension (n := n) A y = n := by
  rw [embeddingDimension_eq_finrank_tangentSpaceIn A y e hye,
    tangentSpaceIn_eq_iInf_ker hU hs hspan hzero e hyU hye hyA]
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    finrank_span_add_finrank_iInf_ker
      (fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y))

/-- Every whole actual tangent-dimension superlevel has an internally
produced finite holomorphic presentation, without pure-dimensionality. -/
theorem isComplexAnalyticSubset_embeddingDimension_superlevel {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (q : ℕ) :
    IsComplexAnalyticSubset (n := n) {y | y ∈ A ∧ q ≤ embeddingDimension (n := n) A y} := by
  classical
  by_cases hq : q ≤ n
  · intro x
    obtain ⟨U, hU, hxU, N, s, hs, hspan, hzeroU⟩ :=
      StokesSingularLocus.exists_cartanGenerators hA hA.isClosed x
    let e := (complexChartAt (n := n) x).val
    let g : Fin N → ComplexModel n → ℂ := fun i w => s i (e.symm w)
    let W : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' U
    have hWo : IsOpen W := e.isOpen_inter_preimage_symm hU
    have hgd : ∀ i, DifferentiableOn ℂ (g i) W := fun i z hz =>
      (differentiableAt_chart (complexChartAt (n := n) x) hz.1
        ((hs i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
    have hxe : x ∈ e.source := mem_complexChartAt_source x
    refine ⟨{ generatorCount := N + Fintype.card (JacobianMinorIndex N n (n - q + 1))
              generator := Fin.addCases g (jacobianMinorGenerator (n := n) (r := n - q + 1) g)
              coordinateNeighborhood := W
              isOpen_coordinateNeighborhood := hWo
              center_mem_coordinateNeighborhood :=
                ⟨e.map_source hxe, by rw [mem_preimage, e.left_inv hxe]; exact hxU⟩
              coordinateNeighborhood_subset_target := inter_subset_left
              generator_holomorphic := ?_
              zeroLocus := ?_ }⟩
    · intro a
      refine Fin.addCases ?_ ?_ a
      · intro j; simpa using hgd j
      · intro j
        simpa using differentiableOn_jacobianMinorGenerator (n := n) (r := n - q + 1) hWo hgd j
    · intro y hye hyW
      have hyU : y ∈ U := by
        have := hyW.2
        rwa [mem_preimage, e.left_inv hye] at this
      have hgy : ∀ i, g i (e y) = s i y := fun i => by
        change s i (e.symm (e y)) = s i y
        rw [e.left_inv hye]
      rw [Fin.forall_fin_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
      constructor
      · rintro ⟨hyA, hv⟩
        refine ⟨fun i => by rw [hgy]; exact (hzeroU y hyU).mp hyA i, fun b => ?_⟩
        have hrn := rank_add_embeddingDimension_of_cartanGenerators hU hs hspan hzeroU
          (complexChartAt (n := n) x) hyU hye hyA
        change finrank ℂ (Submodule.span ℂ
          (range fun i => fderiv ℂ (g i) (e y))) + embeddingDimension (n := n) A y = n at hrn
        have hlt : finrank ℂ (Submodule.span ℂ
            (range fun i => fderiv ℂ (g i) (e y))) < n - q + 1 := by
          omega
        have hminor := (finrank_span_lt_iff_minors_eq_zero
          (fun i => fderiv ℂ (g i) (e y))).mp hlt
        exact hminor _ _
      · rintro ⟨hs0, hminor⟩
        have hyA := (hzeroU y hyU).mpr fun i => by rw [← hgy]; exact hs0 i
        refine ⟨hyA, ?_⟩
        have hlt : finrank ℂ (Submodule.span ℂ
            (range fun i => fderiv ℂ (g i) (e y))) < n - q + 1 := by
          apply (finrank_span_lt_iff_minors_eq_zero _).mpr
          intro rows cols
          have h := hminor ((Fintype.equivFin (JacobianMinorIndex N n (n - q + 1))) (rows, cols))
          simpa [jacobianMinorGenerator, jacobianMinor, g] using h
        have hrn := rank_add_embeddingDimension_of_cartanGenerators hU hs hspan hzeroU
          (complexChartAt (n := n) x) hyU hye hyA
        change finrank ℂ (Submodule.span ℂ
          (range fun i => fderiv ℂ (g i) (e y))) + embeddingDimension (n := n) A y = n at hrn
        omega
  · have heq : {y | y ∈ A ∧ q ≤ embeddingDimension (n := n) A y} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hq (hy.2.trans (embeddingDimension_le A y))
    rw [heq]
    exact isComplexAnalyticSubset_empty

/-- The true complete-ideal tangent dimension detects precisely the regular
points of a pure analytic set, even when its reduced order is one. -/
theorem regularAtDim_iff_embeddingDimension_le {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) A d) {x : M} (hx : x ∈ A) :
    RegularAtDim (n := n) A x d ↔ embeddingDimension (n := n) A x ≤ d := by
  constructor
  · intro hreg
    rw [embeddingDimension_eq_of_regularAtDim hreg]
  · intro hle
    obtain ⟨U, hU, hxU, N, s, hs, hspan, hzeroU⟩ :=
      StokesSingularLocus.exists_cartanGenerators hA hA.isClosed x
    let e := complexChartAt (n := n) x
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hrn := rank_add_embeddingDimension_of_cartanGenerators hU hs hspan hzeroU e hxU hxe hx
    have hge : n - d ≤ finrank ℂ (Submodule.span ℂ
        (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val x))) := by omega
    obtain ⟨rows, cols, hminor⟩ := exists_minor_ne_zero_of_le_finrank _ hge
    exact PureSingularLocus.regularAtDim_of_minor_ne_zero_of_isPureDim hd hpure x
      hU hs hzeroU hxU hxe hx rows cols hminor

/-- The whole current pure singular locus is exactly the first strict
tangent-dimension threshold, not a supplied Jacobian candidate. -/
theorem diff_regularLocus_eq_embeddingDimension_superlevel {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) A d) :
    A \ regularLocus (n := n) A d =
      {x | x ∈ A ∧ d + 1 ≤ embeddingDimension (n := n) A x} := by
  ext x
  by_cases hx : x ∈ A
  · simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hx, true_and]
    change (¬ RegularAtDim (n := n) A x d) ↔ _
    rw [regularAtDim_iff_embeddingDimension_le hA hd hpure hx]
    omega
  · simp [hx]

/-- Finite actual embedding dimensions internally produce an attained
singular maximum locus, without compactness or a maximum certificate. -/
theorem exists_maximum_embeddingDimension_singular_locus {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) A d)
    (hsing : ∃ x ∈ A, ¬ RegularAtDim (n := n) A x d) :
    ∃ q : ℕ, d < q ∧ q ≤ n ∧
      (∃ x ∈ A, embeddingDimension (n := n) A x = q) ∧
      (∀ x ∈ A, embeddingDimension (n := n) A x ≤ q) ∧
      IsComplexAnalyticSubset (n := n) {x | x ∈ A ∧ embeddingDimension (n := n) A x = q} ∧
      {x | x ∈ A ∧ embeddingDimension (n := n) A x = q} ⊆
        A \ regularLocus (n := n) A d := by
  classical
  obtain ⟨c, hc, hcreg⟩ := hsing
  let V := embeddingDimension (n := n) A '' A
  have hfin : V.Finite := (finite_Iic n).subset fun _ ⟨x, _, hxe⟩ => hxe ▸ embeddingDimension_le A x
  obtain ⟨q, ⟨x, hx, hxq⟩, hqmax⟩ :=
    Set.exists_max_image V id hfin ⟨embeddingDimension (n := n) A c, mem_image_of_mem _ hc⟩
  have hbound : ∀ y ∈ A, embeddingDimension (n := n) A y ≤ q :=
    fun y hy => hqmax _ (mem_image_of_mem _ hy)
  have hcval : d < embeddingDimension (n := n) A c := by
    have := mt (regularAtDim_iff_embeddingDimension_le hA hd hpure hc).mpr hcreg
    omega
  have hdq : d < q := hcval.trans_le (hbound c hc)
  have heq : {y | y ∈ A ∧ embeddingDimension (n := n) A y = q} =
      {y | y ∈ A ∧ q ≤ embeddingDimension (n := n) A y} := by
    ext y
    constructor
    · rintro ⟨hy, hyq⟩; exact ⟨hy, hyq.ge⟩
    · rintro ⟨hy, hyq⟩; exact ⟨hy, (hbound y hy).antisymm hyq⟩
  refine ⟨q, hdq, hxq ▸ embeddingDimension_le A x, ⟨x, hx, hxq⟩, hbound, ?_, ?_⟩
  · rw [heq]
    exact isComplexAnalyticSubset_embeddingDimension_superlevel hA q
  · intro y hy
    refine ⟨hy.1, ?_⟩
    intro hreg
    have hemb := embeddingDimension_eq_of_regularAtDim hreg
    rw [hy.2] at hemb
    omega

end
end Hironaka.HironakaCurrentEmbeddingDimension
