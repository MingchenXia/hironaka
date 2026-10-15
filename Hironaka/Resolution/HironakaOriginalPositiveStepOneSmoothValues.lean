/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedCurveSmoothValues
import Hironaka.Resolution.HironakaOriginalPositiveMemberCurrentCosupport
/-! Original DOMAIN2 positive StepOne smooth values on ANY upper TEST.
Actual run masks/current points and independent source records come first. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveStepOneSmoothValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionPositiveLowerHistory
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalUntestedMemberOpenFullValues HironakaOriginalPositiveMemberCurrentCosupport
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  StepOneValue StepOneLowerDomain StepOneValueMasked StepOneRegime CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower HironakaCoherentTransformExtension
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen InvDomainTowerAlong
  InvDomainMemberRestriction BoundaryCount RelativePrincipalizationSpan
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

/-- Genuine whole open-member naturality supplies actual reference domains
before all full GENERAL values, without declaring a lower TEST. -/
theorem original_open_member_untested_smooth_full_value (hn : 0<n) (hm : 0<m) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (E₀ : List (Set X))
    (hE₀ : ∀ F ∈ E₀,F ∈ M.E) (U : Opens X) (p₀ : U)
    (hPos : 1≤boundaryCount E₀ (p₀ : X)) (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    {f : Y → U} {g : D' → openPreimage T U} {Q : BlowupTower Y D'}
    (h : IsActualTowerPullback (X := CMfd.of (n := n) U) f Q (restrict U T) g) (z : D')
    (hy : g z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (memberRemainderMarked M (membersThrough M.E E₀ p₀))) (restrict U T)).cosupp) :
    let K := MarkedIdeal.pullback (Subtype.val : U → X)
      (memberRemainderMarked M (membersThrough M.E E₀ p₀))
    (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f K) Q z=
      familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv K (restrict U T) (g z)) := by
  let mU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let F₀ := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let S := membersThrough mU.E F₀ p₀
  have hmU : IsInvDomain 2 mU := isInvDomain_pullback_val U hM
  have hF₀ : ∀ F ∈ F₀,F ∈ mU.E := by
    intro F hF
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hF
    exact List.mem_map_of_mem (hE₀ A hA)
  have hCount : boundaryCount F₀ p₀=boundaryCount E₀ (p₀ : X) :=
    CodimOnePartCanonical.boundaryCount_map_preimage _ _ p₀
  have hS : S.Nonempty := membersThrough_nonempty hF₀ (by rw [hCount];exact hPos)
  have hEq := pullback_val_memberRemainder_membersThrough hn M hM.isWellFormed hM.one_le_d E₀ hE₀ U p₀
  have hTest := isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  dsimp only
  rw [hEq] at hy ⊢
  exact original_member_untested_smooth_full_value (X := CMfd.of (n := n) U)
    hn hm k h mU hmU S hS hTest z hy

variable {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- ONLY the genuine original positive run supplies actual mask endpoints
before the WHOLE independently computed SOURCE lower GENERAL comparison. -/
theorem original_positive_run_lower_smooth_values (hn : 0<n) (hm : 0<m) (k : ℕ)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hT : IsGeoTestTower M T) (s : ℕ) (z : D')
    (hy : g z ∈ (geoTransformAlong M T).cosupp) (hns : ¬ IsSpecial M T (g z))
    (hl : level M T (g z)=s+1) :
    let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
    let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
    let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
    let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
    let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
    ∃ hp : (tail T r).proj (g z) ∈ U,∃ hp' : (tail Q r).proj z ∈ V,
      (invFamily hm ((m-n)+k+1)).inv J' (restrict V (tail Q r)) (⟨z,hp'⟩ : openPreimage (tail Q r) V)=
        familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv J (restrict U (tail T r))
          (⟨g z,hp⟩ : openPreimage (tail T r) U)) := by
  let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
  let H := head T r
  let R := tail T r
  let U := lowerMask M (s+1) H (R.proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) H (R.proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let L := restrict U R
  let L' := restrict V (tail Q r)
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hyBar : g z ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar];exact hy
  have hh := (stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hyBar hns).1
  have hHeadLevel : level M H (R.proj (g z))=s+1 := hh.1.trans hl
  obtain ⟨hp,hPoint⟩ := original_run_positive_member_current_cosupport hn M hM T hT (g z) hy hns hl
  obtain ⟨hH,hR⟩ := (isGeoTestTower_iff_head_tail (barMarked M) T r).mp hBar
  obtain ⟨a,hHead,hTail,p,q,hpSmooth,_hpcoord,hqcoord,hRecord,hRestr⟩ :=
    IsActualTowerPullback.exists_split_actual_positive_lower_diagram h M hM.isWellFormed hBar r s z
  have hPre := IsActualTowerPullback.all_maskA_dictionary hHead M hM.isWellFormed hH ((tail Q r).proj z)
  rw [←hTail.proj_comm z] at hPre
  have hV : (V : Set (split Q r).1)=a ⁻¹' (U : Set (split T r).1) := hPre
  have hp' : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hV]
    change a ((tail Q r).proj z) ∈ U
    rw [←hTail.proj_comm z]
    exact hp
  let zV : openPreimage (tail Q r) V := ⟨z,hp'⟩
  let yU : openPreimage R U := ⟨g z,hp⟩
  have hq : q zV=yU := Subtype.ext (hqcoord zV)
  have hCurrent : yU ∈ (geoTransformAlong J L).cosupp := hPoint
  let mH := geoTransformAlong (barMarked M) H
  have hmH : IsInvDomain 2 mH := isInvDomain_geoTransformAlong (isInvDomain_barMarked M hM) H hH
  let E₀ := origMembers M H
  have hE₀ : ∀ F ∈ E₀,F ∈ mH.E := fun F hF => List.mem_of_mem_take hF
  have hPos : 1≤boundaryCount E₀ (R.proj (g z)) := by
    change 1≤level M H (R.proj (g z))
    rw [hHeadLevel]
    omega
  have hInit := pullback_memberLowerExtension_eq_lowerMarked_succ hn M hM.isWellFormed H hH (R.proj (g z)) hHeadLevel
  change MarkedIdeal.pullback (Subtype.val : U → (split T r).1)
    (memberRemainderMarked mH (membersThrough mH.E E₀ (R.proj (g z))))=J at hInit
  have hyOpen : q zV ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → (split T r).1)
      (memberRemainderMarked mH (membersThrough mH.E E₀ (R.proj (g z))))) L).cosupp := by
    rw [hInit,hq]
    exact hCurrent
  have hv := original_open_member_untested_smooth_full_value (X := (split T r).1)
    (Y := CMfd.of (n := m) V) hn hm k mH hmH E₀ hE₀ U ⟨R.proj (g z),hp⟩ hPos
    R hR hRestr zV hyOpen
  dsimp only at hv
  change markedPullback (m := m) p J=J' at hRecord
  rw [hInit,hRecord,hq] at hv
  exact ⟨hp,hp',hv⟩

/-- WHOLE unchanged original positive StepOne smooth equality on ANY genuine
upper TEST, with actual lower points supplied internally and no canonicality. -/
theorem original_positive_step_one_smooth_value_of_test (hn : 0<n) (hm : 0<m) (k : ℕ)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hT : IsGeoTestTower M T) (s : ℕ) (z : D')
    (hy : g z ∈ (geoTransformAlong M T).cosupp) (hns : ¬ IsSpecial M T (g z))
    (hl : level M T (g z)=s+1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z=
      stepDimensionMap (familyDimensionMap (m-n) (k+1))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
  let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  obtain ⟨hp,hp',hv⟩ := original_positive_run_lower_smooth_values hn hm k h M hM hT s z hy hns hl
  let yU : openPreimage (tail T r) U := ⟨g z,hp⟩
  let zV : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  have hRun : regimeRun
      (stepRegime (markedPullback (m := m) f M) (level (markedPullback (m := m) f M) Q z)) Q z=r := by
    rw [hLevel]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed hBar _ z
  have hnsSource : ¬ IsSpecial (markedPullback (m := m) f M) Q z :=
    fun hs => hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mp hs)
  have hSource : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1))
      (markedPullback (m := m) f M) Q z=
      toLex (s+1,((invFamily hm ((m-n)+k+1)).inv J' L' zV : WithTop (ValTy ((m-n)+k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hnsSource,hRun,hLevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp']
  have hTarget : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)=
      toLex (s+1,((invFamily hn (k+1)).inv J L yU : WithTop (ValTy (k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns]
    change toLex (level M T (g z),Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) M
      (lowerMarkedM M) (level M T (g z)) (head T r) (tail T r) (g z))=_
    rw [hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hSource,hTarget]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+k+1) => toLex (s+1,(v : WithTop (ValTy ((m-n)+k+1))))) hv

end
end Hironaka.HironakaOriginalPositiveStepOneSmoothValues
