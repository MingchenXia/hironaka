import Hironaka.Resolution.HironakaG3ActualEmptyCanonicalIff
import Hironaka.Resolution.HironakaOriginalFiniteEmptyCompression
import Hironaka.Resolution.HironakaG3NonemptySeqCanonicalTransport
import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.G3EmptyAwareCanonicalCompression
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  MarkedIdeals CanonicalCentres HironakaStageCenters HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareComposition HironakaOriginalFiniteEmptyCompression G3ActualEmptyCanonicalIff
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Delete actual empty stages without assuming canonicality; physical comparison and original-family canonicality iff are retained. -/
theorem original_family_compress_empty_iff {n : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X Y) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ ∧
      (IsCanonical M ((invFamily hn k).inv M) Q ↔ IsCanonical M ((invFamily hn k).inv M) T) := by
  classical
  generalize hlen : T.length = ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,hne,hlen.le,
        emptyAware_of_isTowerIso (IsTowerIso.refl_self T),Iff.rfl⟩
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Y',S',χD,hlenD,hPhys,hIff⟩ := original_family_actual_empty_canonical_iff hn k M hM H π hπ S
    have hlt : (H.append S').length < ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length + 1 + S.length = ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,hQ,hleQ,hPhysQ,hIffQ⟩ := ih _ hlt (H.append S') rfl
    refine ⟨Z,Q,χQ.trans χD,hQ,hleQ.trans hlt.le,?_,hIffQ.trans hIff⟩
    simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans hPhysQ hPhys
end
end Hironaka.G3EmptyAwareCanonicalCompression

namespace Hironaka.G3EmptyAwareCanonicalTransport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  MarkedIdeals CanonicalCentres HironakaStageCenters HironakaG3EmptyAwareHistory
  G3EmptyAwareCanonicalCompression G3NonemptySeqCanonicalTransport
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Original-family canonicality transfers along an actual empty-aware comparison. -/
theorem original_family_canonical_of_emptyAware {n k : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (hn : 0 < n) {M : MarkedIdeal n X₂} (hM : IsInvDomain k M)
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    (hM₁ : IsInvDomain k (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M))
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T₂) :
    IsCanonical (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M)
      ((invFamily hn k).inv (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M)) T₁ := by
  obtain ⟨Z₁,Q₁,χ₁,hne₁,_hL₁,hP₁,hI₁⟩ :=
    original_family_compress_empty_iff hn k (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M) hM₁ T₁
  obtain ⟨Z₂,Q₂,χ₂,hne₂,_hL₂,hP₂,hI₂⟩ := original_family_compress_empty_iff hn k M hM T₂
  have hQ := HironakaG3EmptyAwareComposition.trans hP₁
    (HironakaG3EmptyAwareComposition.trans h (HironakaG3EmptyAwareSymmetry.symm hP₂))
  have he : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X₂ ∞).symm =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X₂ ∞ := by ext x; rfl
  have hQ' : EmptyAwareTowerIso Φ Q₁ Q₂ (χ₁.trans (ψ.trans χ₂.symm)) := by
    simpa only [Diffeomorph.refl_trans, Diffeomorph.trans_refl, he] using hQ
  have hcQ₂ := hI₂.mpr hcan
  have hcQ₁ := isCanonical_of_emptyAware_nonempty_seq (invFamily hn k) hM Φ hQ' hne₁ hne₂ hcQ₂
  exact hI₁.mp hcQ₁
end
end Hironaka.G3EmptyAwareCanonicalTransport
