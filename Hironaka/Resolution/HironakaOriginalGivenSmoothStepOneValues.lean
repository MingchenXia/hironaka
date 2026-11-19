/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGivenSmoothZeroChoices
import Hironaka.Resolution.HironakaOriginalAllStepOneSmoothValues
/-! Same GIVEN actual upperCartesian history, independent OWN LARGE full
values and all unchanged original StepOne branches; no replacement Q. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalGivenSmoothStepOneValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MaxLocusLocal CanonicalCentres
  HironakaOriginalRunCompanionSpecialSmooth HironakaOriginalZeroOwnSmallSmoothValues
  HironakaOriginalSourceChoiceCartesian HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalUntestedMemberCurveFullValues HironakaOriginalUntestedControlledSmoothPullback
  HironakaOriginalUntestedCompanionSmoothPullback HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionPositiveMemberHistory
  HironakaOriginalActualSmoothZeroMaskHistories HironakaSmoothSubmersionTangentContact
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain StepOneRegime
  StepOneValueMasked
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  GeneralValue GeneralCompare GeneralCanonicalTail CompanionRebase CompanionReductionAlong
  InvDomainTowerAlong
open HironakaOriginalGivenSmoothZeroChoices HironakaOriginalZeroOwnLargeSmoothValues
  HironakaOriginalPositiveStepOneSmoothValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n m b : ℕ} {X D : CMfd.{u} n} {Y D' A B : CMfd.{u} m}

private theorem actual_base_submersion {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D} (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

/-- Independent OWN LARGE record and its whole values on the SAME GIVEN
upper history; all source TEST, run and current-point inputs are internal. -/
theorem original_given_zero_own_large_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    {f : Y → X} {Q : BlowupTower Y D'} {g : D' → D}
    (hCart : IsActualTowerPullback f Q T g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ (z : D'),g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) T (g z)
        let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
        let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail T r).proj (g z) ∈ U) (hpOwn : (tail Q r).proj z ∈ W),
          ∀ k : ℕ,(invFamily hm ((m-n)+k+1)).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩=
            familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv J
              (restrict U (tail T r)) ⟨g z,hp⟩) := by
  obtain ⟨hQ,hSmall⟩ := original_given_zero_own_small_smooth_values hn hm M hM hmax T hT hCart
  have hf := actual_base_submersion hCart
  refine ⟨hQ,?_⟩
  intro z hy hns hl
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,Vv,hVvW,hzv,p,q,hCurve,hRecord,hEndpoint,_hSmallTest,_hzSmall,_hSmallValues⟩ := hSmall z hy hns hl
  obtain ⟨_hpTarget,hJ,hJT,_hJWhole,hJP,_hJCurrent⟩ :=
    actual_original_test_zero_mask_history hn M hM hmax T hT (g z) hy hns hl
  have hK : IsInvDomain ((m-n)+2) K := by
    convert isInvDomain_markedPullback_submersion hf M hM using 1
    omega
  have hMaxK : IsMaximalOrderAlong K.N K.ideal K.d :=
    isMaximalOrderAlong_preimage hf hM.isWellFormed.isCoherent M.N M.d hmax
  have heM := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (heM.2 T).1.mpr hT
  have hzK : z ∈ (geoTransformAlong K Q).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary hCart M hM.isWellFormed hT]
    exact hy
  have hlK : level K Q z=0 :=
    (IsActualTowerPullback.bar_level_dictionary hCart M hM.isWellFormed hBar z).trans hl
  have hnsK : ¬IsSpecial K Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary hCart M hM.isWellFormed hBar z).mp hs)
  have hRun : regimeRun (stepRegime K 0) Q z=r :=
    IsActualTowerPullback.all_stepRegime_run hCart M hM.isWellFormed hBar 0 z
  have hOwn := actual_original_test_zero_mask_history hm K hK hMaxK Q hQ z hzK hnsK hlK
  rw [hRun] at hOwn
  obtain ⟨hpOwn,hOwnD,hOwnT,_hOwnWhole,_hzOwn,_hOwnCurrent⟩ := hOwn
  have hSmallLarge := smaller_open_cartesian (Y := (split Q r).1) hVvW (tail Q r)
  refine ⟨hp,hpOwn,fun k => ?_⟩
  have hyCurve : q (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
      (geoTransformAlong J (restrict U (tail T r))).cosupp := by
    rw [hEndpoint]
    exact hJP
  have hValue := curve_model_full_value_via_same_ambient_cartesian
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := m) W)
    hn hm k hSmallLarge hCurve JOwn hOwnD hOwnT J hJ hJT hRecord ⟨z,hzv⟩ hyCurve
  rw [hEndpoint] at hValue
  exact hValue

/-- Original computed run/mask values precede literal zero StepOne
substitution on this actual SAME GIVEN Cartesian upper history. -/
theorem original_given_zero_step_one_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    {f : Y → X} {Q : BlowupTower Y D'} {g : D' → D}
    (h : IsActualTowerPullback f Q T g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z=
          stepDimensionMap (familyDimensionMap (m-n) (k+1))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  obtain ⟨hQ,hValues⟩ := original_given_zero_own_large_smooth_values hn hm M hM hmax T hT h
  refine ⟨hQ,fun z hy hns hl k => ?_⟩
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


/-- The SAME GIVEN source history is retained before EVERY endpoint,
positive recursive depth and ALL THREE unchanged original branch cases. -/
theorem original_given_all_step_one_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    {f : Y → X} {Q : BlowupTower Y D'} {g : D' → D}
    (h : IsActualTowerPullback f Q T g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z=
          stepDimensionMap (familyDimensionMap (m-n) (k+1))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  obtain ⟨hQ,hZero⟩ := original_given_zero_step_one_smooth_values hn hm M hM hmax T hT h
  refine ⟨hQ,fun z hy k => ?_⟩
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
end Hironaka.HironakaOriginalGivenSmoothStepOneValues
