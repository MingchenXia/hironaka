/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFrozenCompanionPresentation
import Hironaka.Resolution.HironakaOriginalFullCutCompanionTestStep

/-! Actual FULL original cuts induce genuine whole Step One cuts and real
preparation of the SAME old companion, without next canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutInheritedCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HironakaOriginalFrozenCompanionPresentation
  HironakaOriginalFullCutCompanionTestStep
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

theorem original_full_cut_inherited_companion_values (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M) (T : BlowupTower X Y)
    (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hq : 1≤orderAt M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn (k+1)).inv M T x≤(invFamily hn (k+1)).inv M T c) :
    ∀ c : patchAt M T y,c.val ∈ C →
      c ∈ (geoTransformAlong (companionAt M T y) (companionTailAt M T y)).cosupp ∧
      ∀ p : patchAt M T y,
        p ∈ (geoTransformAlong (companionAt M T y) (companionTailAt M T y)).cosupp →
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k)
              (companionAt M T y) (companionTailAt M T y) p≤
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn k)
              (companionAt M T y) (companionTailAt M T y) c := by
  have hData := actual_frozen_companion_domain_and_cosupport hn M hM T hc y hy hq
  have hAt (p : patchAt M T y)
      (hp : p ∈ (geoTransformAlong (companionAt M T y) (companionTailAt M T y)).cosupp)
      (c : patchAt M T y) (hcC : c.val ∈ C) :
      c ∈ (geoTransformAlong (companionAt M T y) (companionTailAt M T y)).cosupp ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k)
            (companionAt M T y) (companionTailAt M T y) p≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k)
            (companionAt M T y) (companionTailAt M T y) c := by
    have hpUpper := ((hData.2.2.2.2 p).mp hp).1
    have hpValue := original_value_eq_actual_frozen_companion hn M hM T hc y hy hq p hp
    have hBound := hCuts p hpUpper c hcC
    rw [hpValue] at hBound
    have hThreshold := original_superlevel_pullback_eq_actual_frozen_companion hn M hM T hc y hy hq
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k)
        (companionAt M T y) (companionTailAt M T y) p)
    have hResult := (Set.ext_iff.mp hThreshold c).mp ⟨hC.2.1 hcC,hBound⟩
    exact ⟨hResult.1,WithTop.coe_le_coe.mp hResult.2⟩
  have hyComp : (⟨y,hData.1⟩ : patchAt M T y) ∈
      (geoTransformAlong (companionAt M T y) (companionTailAt M T y)).cosupp :=
    (hData.2.2.2.2 ⟨y,hData.1⟩).mpr ⟨hy,rfl⟩
  intro c hcC
  exact ⟨(hAt ⟨y,hData.1⟩ hyComp c hcC).1,fun p hp => (hAt p hp c hcC).2⟩

theorem original_full_cut_prepared_companion_data (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M) (T : BlowupTower X Y)
    (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hq : 1≤orderAt M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn (k+1)).inv M T x≤(invFamily hn (k+1)).inv M T c) :
    let J := companionAt M T y
    let R := companionTailAt M T y
    let RNext := restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)
    IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) R ∧
      IsGeoTestTower J RNext ∧ IsInvDomain (k+1) (geoTransformAlong J RNext) ∧
        (Subtype.val : patchAt M T y → Y) ⁻¹' C ⊆
          maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J R)
            (geoTransformAlong J R).cosupp := by
  have hData := actual_frozen_companion_domain_and_cosupport hn M hM T hc y hy hq
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hPos : 0<orderAt M T y := lt_of_lt_of_le Nat.zero_lt_one hq
  have hNext := original_full_value_cut_compAt_test hn M hM T hT hc y hy hPos C hC π hπ
    (hCuts y hy)
  have hLowerCut := original_full_cut_inherited_companion_values hn M hM T hc y hy hq C hC hCuts
  exact ⟨hData.2.1,hData.2.2.1,hData.2.2.2.1,hNext.1,hNext.2,hLowerCut⟩

end
end Hironaka.HironakaOriginalFullCutInheritedCompanion
