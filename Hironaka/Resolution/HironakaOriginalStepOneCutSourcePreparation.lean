/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSourceStepOneCanonicalSmoothHistory
import Hironaka.Resolution.HironakaLocalPrincipalization

/-! Genuine original StepOne source preparation preserves the GIVEN
actual source prefix and constructs its true next source blowup. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOneCutSourcePreparation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres ResolutionDriver ResolutionInvariantDriver InvDomainTowerAlong HomogenizedIdealAlong
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionControlledTransform HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionOriginalRecursiveFamily HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X D Z : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private theorem actual_base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem original_stepone_cut_source_data (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (h : IsActualTowerPullback f Q T g)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T x≤Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T c) :
    let K := markedPullback (m := m) f M
    IsInvDomain ((m-n)+k+2) K ∧
      IsMaximalOrderAlong K.N K.ideal K.d ∧ IsGeoTestTower K Q ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K Q x≤Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K Q c := by
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)) M hM hmax hn T hc).2.1
  have hTarget := isInvDomain_geoTransformAlong hM T hT
  have hDom := isInvDomain_markedPullback_submersion (actual_base_submersion h) M hM
  have hSourceDom : IsInvDomain ((m-n)+k+2) (markedPullback (m := m) f M) := by
    convert hDom using 1
    omega
  have hSourceMax : IsMaximalOrderAlong (markedPullback (m := m) f M).N
      (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).d :=
    HironakaSmoothSubmersionTangentContact.isMaximalOrderAlong_preimage
      (actual_base_submersion h) hM.isWellFormed.isCoherent M.N M.d hmax
  have hTransport := HironakaOriginalSourceStepOneCanonicalSmoothHistory.IsActualTowerPullback.original_stepOne_family
    hn hm h M hM hmax hc
  obtain ⟨hSourceTest,hWhole⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hT
  have hSourceC : (geoTransformAlong (markedPullback (m := m) f M) Q).IsAdmissibleCentre (g ⁻¹' C) := by
    rw [hWhole]
    exact isAdmissibleCentre_markedPullback h.isSubmersion (geoTransformAlong M T)
      hTarget.isWellFormed.isCoherent hC
  refine ⟨hSourceDom,hSourceMax,hSourceTest,hTransport.1,hSourceC,?_⟩
  intro x hx c hcC
  have hxT : g x ∈ (geoTransformAlong M T).cosupp := by rwa [hCos] at hx
  have hcT : g c ∈ (geoTransformAlong M T).cosupp := hC.2.1 hcC
  rw [hTransport.2 x hxT,hTransport.2 c hcT]
  exact (strictMono_stepDimensionMap (strictMono_familyDimensionMap (m-n) (k+1))).monotone (hCuts (g x) hxT (g c) hcC)

theorem exists_actual_stepone_cut_source_extension (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (h : IsActualTowerPullback f Q T g)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T x≤Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T c) :
    let K := markedPullback (m := m) f M
    ∃ (Z' : CMfd.{u} m) (ρ : Z' → D') (hρ : IsBlowupAlong m (g ⁻¹' C) ρ),
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K) Q ∧
      (∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K Q x≤Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K Q c) ∧
      IsActualTowerPullback f (.step Q (g ⁻¹' C) ρ hρ) (.step T C π hπ)
        (actualLift h.isSubmersion hπ hρ) ∧
      IsGeoTestTower K (.step Q (g ⁻¹' C) ρ hρ) ∧ IsProperMap ρ ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ ρ ∧
      ((geoTransformAlong K Q).geoTransform (g ⁻¹' C) ρ).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor m ((geoTransformAlong K Q).E.map
        (BlowupStrictSubmanifold.geoStrictTransform ρ (g ⁻¹' C)) ++ [ρ ⁻¹' (g ⁻¹' C)]) := by
  let K := markedPullback (m := m) f M
  have hData := original_stepone_cut_source_data hn hm M hM hmax hc h C hC hCuts
  have hCurrent := isInvDomain_geoTransformAlong hData.1 Q hData.2.2.1
  have hSourceC := hData.2.2.2.2.1
  have hThin : interior (g ⁻¹' C)=∅ := eq_empty_of_subset_empty
    ((interior_mono hSourceC.2.1).trans (interior_cosupp_eq_empty hCurrent).subset)
  obtain ⟨Z',ρ,hρ⟩ := exists_blowup (g ⁻¹' C) hSourceC.1 hThin
  have hWF := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hCurrent.isWellFormed hSourceC hρ
  exact ⟨Z',ρ,hρ,hData.2.2.2.1,hData.2.2.2.2.2,
    IsActualTowerPullback.step h h.isSubmersion hπ hρ,⟨hData.2.2.1,hSourceC⟩,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hρ,hρ.contMDiff,hWF,hWF.isSNCDivisor⟩

end
end Hironaka.HironakaOriginalStepOneCutSourcePreparation
