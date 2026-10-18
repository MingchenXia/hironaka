/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedJointSourceBoundValues
import Hironaka.Resolution.HironakaOriginalFullCutSourcePreparation
/-! Genuine compact-current simultaneous selection extends the SAME given old
source prefix before ALL prepared original FULL values at arbitrary bounds. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCompactPreparedSmoothHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres ResolutionDriver HironakaHolomorphicJetChartInvariance
  HironakaOriginalSimultaneousHSAdmissibleCentre HironakaOriginalFullCutSourcePreparation
  HironakaOriginalPreparedJointSourceBoundValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionControlledTransform HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

/-- ONLY original compact-current inputs select the actual centre and target
blowup, then append a real source blowup to the SAME given old source Q. -/
theorem exists_compact_prepared_same_source_extension
    (hn : 0<n) (hm : 0<m) (j : ℕ) (hj : 2≤j)
    (M : MarkedIdeal n X) (hM : IsInvDomain j M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn j).inv M) T)
    (hK : IsCompact (geoTransformAlong M T).cosupp)
    (hne : (geoTransformAlong M T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'}
    (h : IsActualTowerPullback f Q T g) :
    let K := markedPullback (m := m) f M
    ∃ (a : D) (C : Set D) (Z : CMfd.{u} n) (π : Z → D) (hπ : IsBlowupAlong n C π),
      a ∈ maxLocus ((invFamily hn j).inv M T) (geoTransformAlong M T).cosupp ∧
      C.Nonempty ∧ C ⊆ maxLocus ((invFamily hn j).inv M T) (geoTransformAlong M T).cosupp ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      (∀ c ∈ C,(invFamily hn j).inv M T c=(invFamily hn j).inv M T a) ∧
      (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      ∃ (Z' : CMfd.{u} m) (ρ : Z' → D') (hρ : IsBlowupAlong m (g ⁻¹' C) ρ),
        IsCanonical K ((invFamily hm ((m-n)+j)).inv K) Q ∧
        IsActualTowerPullback f (.step Q (g ⁻¹' C) ρ hρ) (.step T C π hπ)
          (actualLift h.isSubmersion hπ hρ) ∧
        IsGeoTestTower K (.step Q (g ⁻¹' C) ρ hρ) ∧ IsProperMap ρ ∧
        ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ ρ ∧
        NormalCrossings.IsSNCDivisor m ((geoTransformAlong K Q).E.map
          (BlowupStrictSubmanifold.geoStrictTransform ρ (g ⁻¹' C)) ++ [ρ ⁻¹' (g ⁻¹' C)]) ∧
        geoTransformAlong K (.step Q (g ⁻¹' C) ρ hρ)=
          markedPullback (m := m) (actualLift h.isSubmersion hπ hρ)
            (geoTransformAlong M (.step T C π hπ)) ∧
        (geoTransformAlong K (.step Q (g ⁻¹' C) ρ hρ)).cosupp=
          (actualLift h.isSubmersion hπ hρ) ⁻¹' (geoTransformAlong M (.step T C π hπ)).cosupp ∧
        ∀ z : Z',actualLift h.isSubmersion hπ hρ z ∈
          (geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+(d+j))).inv K (.step Q (g ⁻¹' C) ρ hρ) z=
            familyDimensionMap (m-n) (d+j)
              ((invFamily hn (d+j)).inv M (.step T C π hπ) (actualLift h.isSubmersion hπ hρ z)) := by
  dsimp only
  obtain ⟨a,C,Z,π,ha,hCne,hCL,hC,hR,hHS,hπ,hProper,hHolo,_hWF,hSNC⟩ :=
    exists_original_current_compact_simultaneous_first_blowup hn j M hM T hc hK hne A hA
  have hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn j).inv M T x≤(invFamily hn j).inv M T c :=
    fun x hx c hcC => (hCL hcC).2 x hx
  have hT := (invFamily hn j).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  obtain ⟨Z',ρ,hρ,hOldSource,_hSourceCut,hCart,hSourceTest,hProperSource,hHoloSource,
      _hSourceWF,hSourceSNC⟩ :=
    exists_actual_full_cut_source_extension hn hm M hM hc h C hC π hπ hCuts
  obtain ⟨_hTest,hRecord⟩ := IsActualTowerPullback.relative_marked_dictionary hCart M hM.isWellFormed hP
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary hCart M hM.isWellFormed hP
  refine ⟨a,C,Z,π,hπ,ha,hCne,hCL,hC,hR,hHS,hP,hProper,hHolo,hSNC,
    Z',ρ,hρ,hOldSource,hCart,hSourceTest,hProperSource,hHoloSource,hSourceSNC,hRecord,hCos,?_⟩
  intro z hz d
  exact prepared_full_smooth_values hn hm j hj M hM T hc C hC π hπ hCuts hCart z hz d

/-- ONLY the initial smooth map is supplied: the real old source tower is
internally selected once, then extended before all new points and depths. -/
theorem exists_original_compact_prepared_smooth_history
    (hn : 0<n) (hm : 0<m) (j : ℕ) (hj : 2≤j)
    (M : MarkedIdeal n X) (hM : IsInvDomain j M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn j).inv M) T)
    (hK : IsCompact (geoTransformAlong M T).cosupp)
    (hne : (geoTransformAlong M T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    {f : Y → X} (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
    ∃ (a : D) (C : Set D) (Z : CMfd.{u} n) (π : Z → D) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ maxLocus ((invFamily hn j).inv M T) (geoTransformAlong M T).cosupp ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      (∀ c ∈ C,(invFamily hn j).inv M T c=(invFamily hn j).inv M T a) ∧
      (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      ∃ (Z' : CMfd.{u} m) (Q : BlowupTower Y Z') (g : Z' → Z),
        IsActualTowerPullback f Q (.step T C π hπ) g ∧
        IsGeoTestTower (markedPullback (m := m) f M) Q ∧
        geoTransformAlong (markedPullback (m := m) f M) Q=
          markedPullback (m := m) g (geoTransformAlong M (.step T C π hπ)) ∧
        (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp=
          g ⁻¹' (geoTransformAlong M (.step T C π hπ)).cosupp ∧
        ∀ z : Z',g z∈(geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+(d+j))).inv (markedPullback (m := m) f M) Q z=
            familyDimensionMap (m-n) (d+j)
              ((invFamily hn (d+j)).inv M (.step T C π hπ) (g z)) := by
  have hT := (invFamily hn j).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  obtain ⟨D',Q,g,h,_hg,_hLength,_hSquare,_hOldTest,_hOldRecord,_hOldWF,_hOldCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  obtain ⟨a,C,Z,π,hπ,_ha,hCne,hCL,hC,hR,hHS,hP,hProper,hHolo,hSNC,
      Z',ρ,hρ,_hOldCanon,hCart,hSourceTest,_hProperSource,_hHoloSource,_hSourceSNC,
      hRecord,hCos,hValues⟩ :=
    exists_compact_prepared_same_source_extension hn hm j hj M hM T hc hK hne A hA h
  exact ⟨a,C,Z,π,hπ,hCne,hCL,hC,hR,hHS,hP,hProper,hHolo,hSNC,
    Z',.step Q (g ⁻¹' C) ρ hρ,actualLift h.isSubmersion hπ hρ,
    hCart,hSourceTest,hRecord,hCos,hValues⟩

end
end Hironaka.HironakaOriginalCompactPreparedSmoothHistory
