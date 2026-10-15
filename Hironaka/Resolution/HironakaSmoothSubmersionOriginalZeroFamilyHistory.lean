/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionActualFamilyMonomialLeaf
/-! The actual original dimension-zero base of smooth family canonicity.
Complete mathematics preceded Lean in `Mathematics.tex`. The whole-value
formula is on the internally proved empty cosupport, with the genuine
source depth m-n. No source canonical or value certificate is a premise. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalZeroFamilyHistory
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem original_zero_canonical_empty (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 0 M) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D),
      IsCanonical M ((invFamily hn 0).inv M) T → IsEmptyTower T := by
  intro D T
  induction T with
  | refl => exact fun _ => trivial
  | step T C π hπ ih =>
    intro hcan
    obtain ⟨hcanT,hC⟩ := hcan
    refine ⟨ih hcanT,?_⟩
    rcases hC with hC | hC
    · exact hC
    · have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
        (invFamily hn 0).isInvValue hM T hcanT
      have he := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
      rw [hC,he]
      ext z
      simp only [ResolutionDriver.maxLocus,mem_ofPred_eq,notMem_empty,false_and]

theorem IsActualTowerPullback.empty_history (h : IsActualTowerPullback f Q T g)
    (hT : IsEmptyTower T) : IsEmptyTower Q := by
  induction h with
  | refl => trivial
  | step _ _ _ _ ih =>
    obtain ⟨hT,hC⟩ := hT
    exact ⟨ih hT,by rw [hC,preimage_empty]⟩

private theorem base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem original_zero_actual_family_history (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain 0 M)
    (hcan : IsCanonical M ((invFamily hn 0).inv M) T) :
    IsInvDomain (m-n) (markedPullback (m := m) f M) ∧
    IsEmptyTower T ∧ IsEmptyTower Q ∧
    IsCanonical (markedPullback (m := m) f M)
      ((invFamily hm (m-n)).inv (markedPullback (m := m) f M)) Q ∧
    (geoTransformAlong M T).cosupp = ∅ ∧
    (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp = ∅ ∧
    IsGeoResolution M T ∧ IsGeoResolution (markedPullback (m := m) f M) Q ∧
    ∀ z ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp,
      (invFamily hm ((m-n)+0)).inv (markedPullback (m := m) f M) Q z =
        familyDimensionMap (m-n) 0 ((invFamily hn 0).inv M T (g z)) := by
  have hte := original_zero_canonical_empty hn M hM T hcan
  have hqe := IsActualTowerPullback.empty_history h hte
  have hsourceDom : IsInvDomain (m-n) (markedPullback (m := m) f M) := by
    simpa only [Nat.zero_add] using isInvDomain_markedPullback_submersion (base_submersion h) M hM
  have hsourceCan := ResolutionInvariantExt.isCanonical_of_isEmptyTower
    (markedPullback (m := m) f M)
    ((invFamily hm (m-n)).inv (markedPullback (m := m) f M)) Q hqe
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 0).isInvValue hM T hcan
  have hzero := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
  have hq := (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed ht).1
  have hqzero : (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp = ∅ := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed ht,hzero,preimage_empty]
  refine ⟨hsourceDom,hte,hqe,hsourceCan,hzero,hqzero,⟨ht,hzero⟩,⟨hq,hqzero⟩,?_⟩
  intro z hz
  rw [hqzero] at hz
  exact False.elim hz

theorem exists_original_zero_actual_family_history (hn : 0 < n) (hm : 0 < m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain 0 M)
    (hcan : IsCanonical M ((invFamily hn 0).inv M) T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ Q.length = T.length ∧
      IsInvDomain (m-n) (markedPullback (m := m) f M) ∧
      IsEmptyTower T ∧ IsEmptyTower Q ∧
      IsCanonical (markedPullback (m := m) f M)
        ((invFamily hm (m-n)).inv (markedPullback (m := m) f M)) Q ∧
      IsGeoResolution M T ∧ IsGeoResolution (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q =
        markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp =
        g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ z ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp,
        (invFamily hm ((m-n)+0)).inv (markedPullback (m := m) f M) Q z =
          familyDimensionMap (m-n) 0 ((invFamily hn 0).inv M T (g z)) := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  obtain ⟨hd,hte,hqe,hc,_,_,htr,hqr,hvalue⟩ := original_zero_actual_family_history hn hm h M hM hcan
  exact ⟨D',Q,g,h,h.length_eq,hd,hte,hqe,hc,htr,hqr,
    (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed htr.1).2,
    IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed htr.1,hvalue⟩
end
end Hironaka.HironakaSmoothSubmersionOriginalZeroFamilyHistory
