/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalRecursiveEmptyDeletion
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
/-! Genuine arbitrary empty blowup deletion in original recursive histories.
Complete three-node mathematics preceded code. The actual empty blowup internally
supplies its biholomorphism and whole transported suffix; no normalization input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalActualEmptyNormalization
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealTowerTransport CanonicalCentres HomogenizedIdealAlong
  HironakaOriginalInteriorEmptyHistory HironakaOriginalRecursiveEmptyDeletion
  HironakaOriginalRecursiveBoundaryHistoryMap
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

theorem exists_actual_empty_step_normalization (H : BlowupTower X A) (π : B → A)
    (hπ : IsBlowupAlong n (∅ : Set A) π) (S : BlowupTower B Y) :
    ∃ (Y' : CMfd.{u} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length=S.length ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (interiorEmptyHistory H S') ((H.step ∅ π hπ).append S) χ := by
  obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
  let F := transport φ.symm S
  have ht := transport_isTowerIso φ.symm S
  have hh : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)
      (H.step ∅ π hπ) φ.symm := by
    refine IsTowerIso.step (IsTowerIso.refl_self H)
      BlowupExistenceCodimOne.isBlowupAlong_id_empty hπ φ.symm (fun p => ?_) ?_
    · change π (φ.symm p)=p
      rw [← hφ,φ.apply_symm_apply]
    · exact preimage_empty
  exact ⟨F.target,F.tower,F.back,ht.length_eq,hh.append ht⟩

/-- The original actual empty blowup and original canonical history INTERNALLY
supply the whole deleted family history, cosupport, values and terminal iff. -/
theorem original_recursive_family_actual_empty_deletion (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) ((H.step ∅ π hπ).append S)) :
    ∃ (Y' : CMfd.{u} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length=S.length ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (interiorEmptyHistory H S') ((H.step ∅ π hπ).append S) χ ∧
      IsCanonical M ((invFamily hn k).inv M) (H.append S') ∧
      (geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp=
        χ.symm ⁻¹' (geoTransformAlong M (H.append S')).cosupp ∧
      (∀ y∈(geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp,
        (invFamily hn k).inv M ((H.step ∅ π hπ).append S) y=
          recursiveHistoryShift k (M.E.length+H.length)
            ((invFamily hn k).inv M (H.append S') (χ.symm y))) ∧
      (IsGeoResolution M ((H.step ∅ π hπ).append S) ↔ IsGeoResolution M (H.append S')) := by
  obtain ⟨Y',S',χ,hlen,hi⟩ := exists_actual_empty_step_normalization H π hπ S
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  let T := (H.step ∅ π hπ).append S
  let I := interiorEmptyHistory H S'
  have hpull : MarkedIdeal.pullback Φ M=M := ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have hcanI := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (X := X) (invFamily hn k) hM Φ hi hcan
  rw [hpull] at hcanI
  have hdel := original_recursive_family_empty_deletion_entire_values hn k M hM H S' hcanI
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hM T hcan
  have hcI := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hi ht
  rw [hpull] at hcI
  have htD := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hM (H.append S') hdel.1
  have htH := (isGeoTestTower_append_iff M H S').mp htD |>.1
  have hcD := (geometric_dictionary M hM.isWellFormed H htH S').2.2.2.1
  have hc : (geoTransformAlong M T).cosupp=χ.symm ⁻¹' (geoTransformAlong M (H.append S')).cosupp := by
    ext y
    change y∈(geoTransformAlong M T).cosupp ↔ χ.symm y∈(geoTransformAlong M (H.append S')).cosupp
    rw [← hcD,hcI]
    simp only [mem_preimage,χ.apply_symm_apply]
    rfl
  have hr := IsTowerIso.isGeoResolution_iff Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hi
  rw [hpull] at hr
  refine ⟨Y',S',χ,hlen,hi,hdel.1,hc,?_,?_⟩
  · intro y hy
    have hyI : χ.symm y∈(geoTransformAlong M I).cosupp := by
      rw [hcI]
      change χ (χ.symm y)∈(geoTransformAlong M T).cosupp
      simpa only [χ.apply_symm_apply] using hy
    have hv := (invFamily hn k).isInvValue.towerIso Φ M hM I T χ hi hcan (χ.symm y)
      (by simpa only [χ.apply_symm_apply] using hy)
    rw [hpull,χ.apply_symm_apply] at hv
    exact hv.symm.trans (hdel.2 (χ.symm y) hyI)
  · constructor
    · intro hres
      exact ((original_recursive_family_empty_deletion_canonical_resolution_iff hn k M hM H S').mp
        ⟨hcanI,hr.mpr hres⟩).2
    · intro hres
      exact hr.mp ((original_recursive_family_empty_deletion_canonical_resolution_iff hn k M hM H S').mpr
        ⟨hdel.1,hres⟩).2

/-- The same original-only producer for the actual masked Step One value at
EVERY lower depth, including chosen-contact zero and all positive inner orders. -/
theorem original_recursive_step_actual_empty_deletion (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M)
      ((H.step ∅ π hπ).append S)) :
    ∃ (Y' : CMfd.{u} n) (S' : BlowupTower A Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length=S.length ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (interiorEmptyHistory H S') ((H.step ∅ π hπ).append S) χ ∧
      IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S') ∧
      (geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp=
        χ.symm ⁻¹' (geoTransformAlong M (H.append S')).cosupp ∧
      (∀ y∈(geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M ((H.step ∅ π hπ).append S) y=
          recursiveStepShift k (M.E.length+H.length)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S') (χ.symm y))) ∧
      (IsGeoResolution M ((H.step ∅ π hπ).append S) ↔ IsGeoResolution M (H.append S')) := by
  obtain ⟨Y',S',χ,hlen,hi⟩ := exists_actual_empty_step_normalization H π hπ S
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  let T := (H.step ∅ π hπ).append S
  let I := interiorEmptyHistory H S'
  have hpull : MarkedIdeal.pullback Φ M=M := ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have hVal := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) (invFamily hn k) hn
  have hcanI := hVal.isCanonical_of_isTowerIso (X := X) hM hmax Φ hi hcan
  rw [hpull] at hcanI
  have hdel := original_recursive_step_empty_deletion_entire_values hn k M hM hmax H S' hcanI
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn T hcan).2.1
  have hcI := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hi ht
  rw [hpull] at hcI
  have htD := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S') hdel.1).2.1
  have htH := (isGeoTestTower_append_iff M H S').mp htD |>.1
  have hcD := (geometric_dictionary M hM.isWellFormed H htH S').2.2.2.1
  have hc : (geoTransformAlong M T).cosupp=χ.symm ⁻¹' (geoTransformAlong M (H.append S')).cosupp := by
    ext y
    change y∈(geoTransformAlong M T).cosupp ↔ χ.symm y∈(geoTransformAlong M (H.append S')).cosupp
    rw [← hcD,hcI]
    simp only [mem_preimage,χ.apply_symm_apply]
    rfl
  have hr := IsTowerIso.isGeoResolution_iff Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hi
  rw [hpull] at hr
  refine ⟨Y',S',χ,hlen,hi,hdel.1,hc,?_,?_⟩
  · intro y hy
    have hyI : χ.symm y∈(geoTransformAlong M I).cosupp := by
      rw [hcI]
      change χ (χ.symm y)∈(geoTransformAlong M T).cosupp
      simpa only [χ.apply_symm_apply] using hy
    have hv := hVal.towerIso Φ M hM hmax I T χ hi hcan (χ.symm y)
      (by simpa only [χ.apply_symm_apply] using hy)
    rw [hpull,χ.apply_symm_apply] at hv
    exact hv.symm.trans (hdel.2 (χ.symm y) hyI)
  · constructor
    · intro hres
      exact ((original_recursive_step_empty_deletion_canonical_resolution_iff hn k M hM hmax H S').mp
        ⟨hcanI,hr.mpr hres⟩).2
    · intro hres
      exact hr.mp ((original_recursive_step_empty_deletion_canonical_resolution_iff hn k M hM hmax H S').mpr
        ⟨hdel.1,hres⟩).2

end
end Hironaka.HironakaOriginalActualEmptyNormalization
