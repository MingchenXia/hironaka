/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalSumSeparation
import Hironaka.Resolution.HironakaOriginalPureBoundaryIndependentSource

/-!
# Actual empty sum stages are uniquely projection neutral

Disjoint original analytic parts internally force every actual canonical sum
centre empty. The SAME actual tower has unique biholomorphic projection and
literal whole boundary, including every empty born position. Deleting those
positions in subsequent canonical stages is a separate invariant statement.
Blueprint: `hironaka-original-empty-sum-stage-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalEmptySumStage
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings CanonicalCentres HironakaAdmissibleSequence HironakaOriginalCanonicalSumSeparation
  HironakaOriginalBoundaryCanonicalPrincipalization HironakaOriginalIndependentStoppedSource
  HironakaOriginalTerminalProjectionUniqueness HironakaNormalCrossingsSeparationChoiceComparison
open ResolutionInvariantSpec (IsCanonical IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X D : CMfd.{u} n}

/-- Disjoint actual parts force all centres empty and terminality for the SAME canonical sum stage. -/
theorem canonical_sum_stage_empty_of_disjoint {A B : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsComplexAnalyticSubset (n := n) B)
    (hint : interior A=∅) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hdis : Disjoint A B) (T : BlowupTower X D)
    (hc : IsCanonical (sumMarkedIdeal A B E₀)
      ((canonicalInvariant n).inv (sumMarkedIdeal A B E₀)) T) :
    let M := sumMarkedIdeal A B E₀
    M.cosupp=∅ ∧ IsEmptyTower T ∧ IsGeoResolution M T := by
  dsimp only
  have hM := isInvDomain_sumMarkedIdeal hA hB hint hE₀
  have hcos : (sumMarkedIdeal A B E₀).cosupp=∅ := by
    calc
      _=(sumMarkedIdeal A B E₀).ideal.zeroLocus := cosupp_univ_one hM.isWellFormed.isCoherent
      _=A∩B := HironakaSeparation.zeroLocus_sumIdeal_vanishingIdeal hA.isClosed hB.isClosed
      _=∅ := Set.disjoint_iff_inter_eq_empty.mp hdis
  exact ⟨hcos,canonical_histories_empty_of_original_cosupp_empty _ hM hcos T hc⟩

/-- The SAME all-empty canonical sum projection and every whole strict/boundary position are retained. -/
theorem existsUnique_projection_neutral_sum_stage {A B : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsComplexAnalyticSubset (n := n) B)
    (hint : interior A=∅) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hdis : Disjoint A B) (T : BlowupTower X D)
    (hc : IsCanonical (sumMarkedIdeal A B E₀)
      ((canonicalInvariant n).inv (sumMarkedIdeal A B E₀)) T) :
    let M := sumMarkedIdeal A B E₀
    IsEmptyTower T ∧ IsGeoResolution M T ∧
    ∃! η : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      (∀ z,η z=T.proj z) ∧
      (∀ P : Set X,IsClosed P → strictTransform n T.proj P=η ⁻¹' P) ∧
      (geoTransformAlong M T).E=E₀.map (η ⁻¹' ·)++List.replicate T.length ∅ ∧
      (geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)=
        (E₀.map (η ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  dsimp only
  let M := sumMarkedIdeal A B E₀
  have hM := isInvDomain_sumMarkedIdeal hA hB hint hE₀
  obtain ⟨hcos,heT,hrT⟩ := canonical_sum_stage_empty_of_disjoint hA hB hint E₀ hE₀ hdis T hc
  have hr0 : IsGeoResolution M (BlowupTower.refl : BlowupTower X X) := ⟨True.intro,hcos⟩
  obtain ⟨η,hη,_huniq⟩ := original_ambient_terminal_choice_existsUnique M hM T .refl hc True.intro hrT hr0
  have hp : ∀ z,η z=T.proj z := hη
  have hfun : (η : D → X)=T.proj := funext hp
  have hE : (geoTransformAlong M T).E=E₀.map (η ⁻¹' ·)++List.replicate T.length ∅ := by
    rw [boundary_of_all_empty_tower M hE₀.1 T heT,← hfun]
    rfl
  refine ⟨heT,hrT,η,⟨hp,?_,hE,?_⟩,?_⟩
  · intro P hP
    rw [← hfun]
    have he : exceptionalLocus n η=∅ := by
      ext x
      simp only [mem_empty_iff_false,iff_false]
      exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply x
    simp only [strictTransform,he,sdiff_empty,(hP.preimage η.contMDiff.continuous).closure_eq]
  · rw [hE,List.filter_append]
    simp only [List.filter_replicate,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,reduceIte,List.append_nil]
  · intro η' hη'
    apply Diffeomorph.ext
    intro z
    exact (hη'.1 z).trans (hp z).symm

end
end Hironaka.HironakaOriginalEmptySumStage
