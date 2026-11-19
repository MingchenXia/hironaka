import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
import Hironaka.Resolution.HironakaG3ActualEmptyCanonicalIff
import Hironaka.Resolution.HironakaOriginalCrossingValueTransport
import Hironaka.Resolution.HironakaG3NonemptyPhysicalCanonicalTransport
set_option autoImplicit false
open Set Function TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8EmptyAwareTestTransport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition
  HironakaG3InteriorEmptyAligned
  HironakaOriginalInteriorEmptyHistory HironakaOriginalActualEmptyNormalization
  HironakaOriginalCrossingValueTransport HironakaStageCenters HironakaOriginalFiniteEmptyCompression
  G3NonemptyPhysicalCanonicalTransport MarkedIdealTowerTransport

/-- Deleting one actual interior empty blowup preserves testness for any
well-formed record, without canonicality. -/
theorem actual_empty_test_iff {n : ℕ} {X A B Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y) :
    ∃ (Y' : CMfd.{0} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length = S.length ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (H.append S') ((H.step ∅ π hπ).append S) χ ∧
      (IsGeoTestTower M (H.append S') ↔ IsGeoTestTower M ((H.step ∅ π hπ).append S)) := by
  obtain ⟨Y',S',χ,hlen,hi⟩ := exists_actual_empty_step_normalization H π hπ S
  have hpull : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isCoherent
  have hIso := IsTowerIso.isGeoTestTower_iff (𝔪 := M)
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) hM.isClosedSubmanifold_N hM.isCoherent hi
  rw [hpull] at hIso
  have hPhys := HironakaG3EmptyAwareComposition.trans
    (interior_empty_aligned H S') (emptyAware_of_isTowerIso hi)
  refine ⟨Y',S',χ,hlen,?_,?_⟩
  · simpa only [Diffeomorph.refl_trans] using hPhys
  · constructor
    · intro hTest
      have hH := (isGeoTestTower_append_iff M H S').mp hTest |>.1
      exact hIso.mp ((isGeoTestTower_interior_empty_iff M hM H hH S').mpr hTest)
    · intro hTest
      have hInside := hIso.mpr hTest
      have hH : IsGeoTestTower M H := by
        have h := ((isGeoTestTower_append_iff M (H.step ∅ id
          BlowupExistenceCodimOne.isBlowupAlong_id_empty) S').mp hInside).1
        exact h.1
      exact (isGeoTestTower_interior_empty_iff M hM H hH S').mp hInside

/-- Every finite history has an empty-free physical compression with exactly
the same well-formed-record testness; canonicality is not needed. -/
theorem test_empty_free_compression {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T : BlowupTower X Y) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ ∧
      (IsGeoTestTower M Q ↔ IsGeoTestTower M T) := by
  classical
  generalize hlen : T.length = ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,hne,hlen.le,
        emptyAware_of_isTowerIso (IsTowerIso.refl_self T),Iff.rfl⟩
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Y',S',χD,hlenD,hPhys,hIff⟩ := actual_empty_test_iff M hM H π hπ S
    have hlt : (H.append S').length < ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length + 1 + S.length = ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,hQ,hleQ,hPhysQ,hIffQ⟩ := ih _ hlt (H.append S') rfl
    refine ⟨Z,Q,χQ.trans χD,hQ,hleQ.trans hlt.le,?_,hIffQ.trans hIff⟩
    simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans hPhysQ hPhys

/-- Actual empty-aware tower isomorphisms preserve testness for every
well-formed marked ideal, not only for canonical histories. -/
theorem isGeoTestTower_iff_of_emptyAware {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (M : MarkedIdeal n X₂) (hM : M.IsWellFormed)
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    IsGeoTestTower (MarkedIdeal.pullback Φ M) T₁ ↔ IsGeoTestTower M T₂ := by
  have hM₁ : (MarkedIdeal.pullback Φ M).IsWellFormed := IsWellFormed.pullback hM
  obtain ⟨Z₁,Q₁,χ₁,hne₁,_hL₁,hP₁,hI₁⟩ :=
    test_empty_free_compression (MarkedIdeal.pullback Φ M) hM₁ T₁
  obtain ⟨Z₂,Q₂,χ₂,hne₂,_hL₂,hP₂,hI₂⟩ := test_empty_free_compression M hM T₂
  have hQ := HironakaG3EmptyAwareComposition.trans hP₁
    (HironakaG3EmptyAwareComposition.trans h (HironakaG3EmptyAwareSymmetry.symm hP₂))
  have he : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X₂ ∞).symm =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X₂ ∞ := by ext x; rfl
  have hQ' : EmptyAwareTowerIso Φ Q₁ Q₂ (χ₁.trans (ψ.trans χ₂.symm)) := by
    simpa only [Diffeomorph.refl_trans, Diffeomorph.trans_refl, he] using hQ
  have hPhys := isTowerIso_of_emptyAware_nonempty hQ' hne₁ hne₂
  have hTests := IsTowerIso.isGeoTestTower_iff (𝔪 := M) Φ
    hM.isClosedSubmanifold_N hM.isCoherent hPhys
  exact hI₁.symm.trans (hTests.trans hI₂)
end
end Hironaka.HironakaG8EmptyAwareTestTransport
