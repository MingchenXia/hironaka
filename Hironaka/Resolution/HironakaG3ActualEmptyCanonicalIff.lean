import Hironaka.Resolution.HironakaG3FirstMeetingEmptyAware
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.G3ActualEmptyCanonicalIff
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareComposition HironakaG3InteriorEmptyAligned
  HironakaOriginalInteriorEmptyHistory HironakaOriginalActualEmptyNormalization
  HironakaOriginalRecursiveEmptyDeletion
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- An actual interior empty stage has a physical deletion whose canonicality is equivalent in both directions. -/
theorem original_family_actual_empty_canonical_iff {n : ℕ} {X A B Y : CMfd.{0} n}
    (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y) :
    ∃ (Y' : CMfd.{0} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length = S.length ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (H.append S') ((H.step ∅ π hπ).append S) χ ∧
      (IsCanonical M ((invFamily hn k).inv M) (H.append S') ↔
        IsCanonical M ((invFamily hn k).inv M) ((H.step ∅ π hπ).append S)) := by
  obtain ⟨Y',S',χ,hlen,hi⟩ := exists_actual_empty_step_normalization H π hπ S
  have hpull : MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have hPhys := HironakaG3EmptyAwareComposition.trans
    (interior_empty_aligned H S') (emptyAware_of_isTowerIso hi)
  refine ⟨Y',S',χ,hlen,?_,?_⟩
  · simpa only [Diffeomorph.refl_trans] using hPhys
  · constructor
    · intro hcan
      have hI := (original_recursive_family_empty_deletion_isCanonical_iff hn k M hM H S').mpr hcan
      have hT := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
        (invFamily hn k) hM (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) hi.symm hI
      rw [hpull] at hT
      exact hT
    · intro hcan
      have hI := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
        (invFamily hn k) hM (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) hi hcan
      rw [hpull] at hI
      exact (original_recursive_family_empty_deletion_isCanonical_iff hn k M hM H S').mp hI
end
end Hironaka.G3ActualEmptyCanonicalIff
