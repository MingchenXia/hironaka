import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaOriginalActualEmptyNormalization

/-! Deleting an actual interior empty blowup preserves the empty-aware history. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3InteriorEmptyComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  MarkedIdealTowerTransport HironakaG3EmptyAwareHistory
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres HomogenizedIdealAlong
  HironakaOriginalInteriorEmptyHistory HironakaOriginalRecursiveEmptyDeletion
  HironakaOriginalActualEmptyNormalization

/-- An empty-aware prefix can be extended along physically isomorphic tails. -/
theorem emptyAware_append_isTowerIso {n : ℕ} {X₁ X₂ A₁ A₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {H₁ : BlowupTower X₁ A₁} {H₂ : BlowupTower X₂ A₂}
    {ψ : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A₂}
    (hH : EmptyAwareTowerIso Φ H₁ H₂ ψ)
    {Y₁ Y₂ : CMfd.{0} n} {S₁ : BlowupTower A₁ Y₁} {S₂ : BlowupTower A₂ Y₂}
    {χ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (hS : IsTowerIso ψ S₁ S₂ χ) :
    EmptyAwareTowerIso Φ (H₁.append S₁) (H₂.append S₂) χ := by
  induction hS with
  | refl => exact hH
  | step _ hπ₁ hπ₂ χ hcomm hC ih => exact .step ih hπ₁ hπ₂ χ hcomm hC

/-- Deletion of a genuine interior empty stage, with its transported actual suffix,
produces the structural comparison needed for ambient lifting. -/
theorem exists_emptyAware_actual_empty_deletion {n : ℕ} {X A B Y : CMfd.{0} n}
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y) :
    ∃ (Y' : CMfd.{0} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length = S.length ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (H.append S') ((H.step ∅ π hπ).append S) χ := by
  obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
  let F := transport φ.symm S
  have hprefix : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      H (H.step ∅ π hπ) φ.symm := by
    simpa only [Diffeomorph.refl_trans] using
      (EmptyAwareTowerIso.rightEmpty (emptyAware_of_isTowerIso (IsTowerIso.refl_self H)) hπ φ hφ)
  exact ⟨F.target,F.tower,F.back,(transport_isTowerIso φ.symm S).length_eq,
    emptyAware_append_isTowerIso hprefix (transport_isTowerIso φ.symm S)⟩

/-- Deleting one actual interior empty stage preserves canonicality and the
structural history comparison, without assuming a comparison certificate. -/
theorem original_recursive_family_actual_empty_deletion_with_comparison
    {n : ℕ} {X A B Y : CMfd.{0} n} (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : ResolutionInvariantSpec.IsInvDomain k M)
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y)
    (hcan : ResolutionInvariantSpec.IsCanonical M ((invFamily hn k).inv M)
      ((H.step ∅ π hπ).append S)) :
    ∃ (Y' : CMfd.{0} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length = S.length ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (H.append S') ((H.step ∅ π hπ).append S) χ ∧
      ResolutionInvariantSpec.IsCanonical M ((invFamily hn k).inv M) (H.append S') := by
  obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
  let F := transport φ.symm S
  have ht := transport_isTowerIso φ.symm S
  have hpref : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      H (H.step ∅ π hπ) φ.symm := by
    simpa only [Diffeomorph.refl_trans] using
      (EmptyAwareTowerIso.rightEmpty (emptyAware_of_isTowerIso (IsTowerIso.refl_self H)) hπ φ hφ)
  have hh : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)
      (H.step ∅ π hπ) φ.symm := by
    refine IsTowerIso.step (IsTowerIso.refl_self H)
      BlowupExistenceCodimOne.isBlowupAlong_id_empty hπ φ.symm (fun p => ?_) ?_
    · change π (φ.symm p) = p
      rw [← hφ, φ.apply_symm_apply]
    · exact preimage_empty
  have hi : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (interiorEmptyHistory H F.tower) ((H.step ∅ π hπ).append S) F.back := hh.append ht
  have hpull : MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have hcanI := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (X := X) (invFamily hn k) hM (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) hi hcan
  rw [hpull] at hcanI
  have hdel := original_recursive_family_empty_deletion_entire_values hn k M hM H F.tower hcanI
  exact ⟨F.target,F.tower,F.back,ht.length_eq,emptyAware_append_isTowerIso hpref ht,hdel.1⟩

end
end Hironaka.HironakaG3InteriorEmptyComparison
