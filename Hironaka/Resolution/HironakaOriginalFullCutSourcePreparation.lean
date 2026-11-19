/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalRecursiveFamily
import Hironaka.Resolution.HironakaLocalPrincipalization

/-! Genuine source cuts and actual next blowup preserve the GIVEN source
prefix, before noncanonical source-choice locality or new values are invoked. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutSourcePreparation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres ResolutionDriver ResolutionInvariantDriver InvDomainTowerAlong
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

theorem original_full_cut_source_data (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hc : IsCanonical M ((invFamily hn k).inv M) T)
    (h : IsActualTowerPullback f Q T g)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn k).inv M T x≤(invFamily hn k).inv M T c) :
    let K := markedPullback (m := m) f M
    IsInvDomain ((m-n)+k) K ∧ IsGeoTestTower K Q ∧
      IsCanonical K ((invFamily hm ((m-n)+k)).inv K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        (invFamily hm ((m-n)+k)).inv K Q x≤(invFamily hm ((m-n)+k)).inv K Q c := by
  have hT := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hTarget := isInvDomain_geoTransformAlong hM T hT
  have hDom := isInvDomain_markedPullback_submersion (actual_base_submersion h) M hM
  have hSourceDom : IsInvDomain ((m-n)+k) (markedPullback (m := m) f M) := by
    simpa only [Nat.add_comm k (m-n)] using hDom
  have hTransport := IsActualTowerPullback.original_recursive_family hn hm h M hM hc
  obtain ⟨hSourceTest,hWhole⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hT
  have hSourceC : (geoTransformAlong (markedPullback (m := m) f M) Q).IsAdmissibleCentre (g ⁻¹' C) := by
    rw [hWhole]
    exact isAdmissibleCentre_markedPullback h.isSubmersion (geoTransformAlong M T)
      hTarget.isWellFormed.isCoherent hC
  refine ⟨hSourceDom,hSourceTest,hTransport.1,hSourceC,?_⟩
  intro x hx c hcC
  have hxT : g x ∈ (geoTransformAlong M T).cosupp := by rwa [hCos] at hx
  have hcT : g c ∈ (geoTransformAlong M T).cosupp := hC.2.1 hcC
  rw [hTransport.2 x hxT,hTransport.2 c hcT]
  exact (strictMono_familyDimensionMap (m-n) k).monotone (hCuts (g x) hxT (g c) hcC)

theorem exists_actual_full_cut_source_extension (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hc : IsCanonical M ((invFamily hn k).inv M) T)
    (h : IsActualTowerPullback f Q T g)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn k).inv M T x≤(invFamily hn k).inv M T c) :
    let K := markedPullback (m := m) f M
    ∃ (Z' : CMfd.{u} m) (ρ : Z' → D') (hρ : IsBlowupAlong m (g ⁻¹' C) ρ),
      IsCanonical K ((invFamily hm ((m-n)+k)).inv K) Q ∧
      (∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        (invFamily hm ((m-n)+k)).inv K Q x≤(invFamily hm ((m-n)+k)).inv K Q c) ∧
      IsActualTowerPullback f (.step Q (g ⁻¹' C) ρ hρ) (.step T C π hπ)
        (actualLift h.isSubmersion hπ hρ) ∧
      IsGeoTestTower K (.step Q (g ⁻¹' C) ρ hρ) ∧ IsProperMap ρ ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ ρ ∧
      ((geoTransformAlong K Q).geoTransform (g ⁻¹' C) ρ).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor m ((geoTransformAlong K Q).E.map
        (BlowupStrictSubmanifold.geoStrictTransform ρ (g ⁻¹' C)) ++ [ρ ⁻¹' (g ⁻¹' C)]) := by
  let K := markedPullback (m := m) f M
  have hData := original_full_cut_source_data hn hm M hM hc h C hC hCuts
  have hCurrent := isInvDomain_geoTransformAlong hData.1 Q hData.2.1
  have hSourceC := hData.2.2.2.1
  have hThin : interior (g ⁻¹' C)=∅ := eq_empty_of_subset_empty
    ((interior_mono hSourceC.2.1).trans (interior_cosupp_eq_empty hCurrent).subset)
  obtain ⟨Z',ρ,hρ⟩ := exists_blowup (g ⁻¹' C) hSourceC.1 hThin
  have hWF := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hCurrent.isWellFormed hSourceC hρ
  exact ⟨Z',ρ,hρ,hData.2.2.1,hData.2.2.2.2,
    IsActualTowerPullback.step h h.isSubmersion hπ hρ,⟨hData.2.1,hSourceC⟩,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hρ,hρ.contMDiff,hWF,hWF.isSNCDivisor⟩

end
end Hironaka.HironakaOriginalFullCutSourcePreparation
