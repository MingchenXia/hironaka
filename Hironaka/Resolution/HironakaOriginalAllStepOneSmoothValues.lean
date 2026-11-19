/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroOwnLargeSmoothValues
import Hironaka.Resolution.HironakaOriginalPositiveStepOneSmoothValues
/-! ONE actual original upper history compares all original DOMAIN2 StepOne
branches at every positive lower depth and any smooth relative dimension. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAllStepOneSmoothValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain
  StepOneValueMasked StepOneRegime HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalZeroOwnLargeSmoothValues
  HironakaOriginalPositiveStepOneSmoothValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y : CMfd.{u} m}

theorem exists_original_any_test_zero_step_one_smooth_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z=
          stepDimensionMap (familyDimensionMap (m-n) (k+1))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  obtain ⟨D',Q,g,h,hQ,hValues⟩ := exists_original_zero_own_large_smooth_values hf hn hm M hM hmax T hT
  refine ⟨D',Q,g,h,hQ,fun z hy hns hl k => ?_⟩
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hpOwn,hFull⟩ := hValues z hy hns hl
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hLevel : level K Q z=0 :=
    (IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z).trans hl
  have hNS : ¬IsSpecial K Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mp hs)
  have hRun : regimeRun (stepRegime K (level K Q z)) Q z=r := by
    rw [hLevel]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed hBar 0 z
  have hSource : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) K Q z=
      toLex (0,((invFamily hm ((m-n)+k+1)).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩ :
        WithTop (ValTy ((m-n)+k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hNS,hRun,hLevel,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hpOwn]
  have hTarget : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)=
      toLex (0,((invFamily hn (k+1)).inv J (restrict U (tail T r)) ⟨g z,hp⟩ : WithTop (ValTy (k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hSource,hTarget]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+k+1) => toLex (0,(v : WithTop (ValTy ((m-n)+k+1))))) (hFull k)

/-- ONE history is chosen before all points, depths and branches. -/
theorem exists_original_any_test_all_step_one_smooth_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z=
          stepDimensionMap (familyDimensionMap (m-n) (k+1))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  obtain ⟨D',Q,g,h,hQ,hZero⟩ := exists_original_any_test_zero_step_one_smooth_values hf hn hm M hM hmax T hT
  refine ⟨D',Q,g,h,hQ,fun z hy k => ?_⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  by_cases hSpecial : IsSpecial M T (g z)
  · have hSource := (IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mpr hSpecial
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hSource,if_pos hSpecial,hLevel]
    simp only [stepDimensionMap,ofLex_toLex,WithTop.map_top]
  · rcases Nat.eq_zero_or_pos (level M T (g z)) with hl | hl
    · exact hZero z hy hSpecial hl k
    · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
      exact original_positive_step_one_smooth_value_of_test hn hm k h M hM hT s z hy hSpecial hs

end
end Hironaka.HironakaOriginalAllStepOneSmoothValues
