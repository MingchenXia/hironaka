/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFixedCompanionRunOrder
import Hironaka.Resolution.HironakaOriginalBoundTwoCompanionStepOneRebase
import Hironaka.Resolution.HironakaOriginalBoundTwoStepOneLocalReferenceComparison
import Hironaka.Resolution.HironakaOriginalBoundTwoStepOneCutLocality
/-! Genuine avoided middles and independently local companion masks compare
whole original StepOne values before any future whole-FULL cut induction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFixedCompanionStepOneComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal InvDomainRebase
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen InvDomainTowerAlong InvDomainCompanion
  StepOneLowerDomain CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower CompanionRebase CompanionOpen GeneralCompare
  GeneralValue StepOneRegime GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  RestrictEmptyTower HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalFiniteOrderCutMiddleHistory
  HironakaOriginalFixedCompanionRunOrder HironakaOriginalBoundTwoCompanionStepOneRebase
  HironakaOriginalBoundTwoStepOneLocality HironakaOriginalBoundTwoStepOneCutLocality
  HironakaOriginalBoundTwoStepOneLocalReferenceComparison
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
variable {n : ℕ} {X A Y : CMfd.{u} n}

private theorem actual_maximal_order (J N : MarkedIdeal n X) (hEq : RestrictEquiv J N)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d) : IsMaximalOrderAlong N.N N.ideal N.d := by
  let Jplus : MarkedIdeal n X := ⟨J.N,J.E,J.ideal,J.d+1⟩
  let Nplus : MarkedIdeal n X := ⟨N.N,N.E,N.ideal,N.d+1⟩
  have he : RestrictEquiv Jplus Nplus :=
    ⟨hEq.N_eq,hEq.E_eq,congrArg (fun d : ℕ => d+1) hEq.d_eq,hEq.le,hEq.ge⟩
  intro x hx
  apply hmax x
  change x∈Jplus.cosupp
  rw [he.cosupp_eq]
  exact hx

/-- Actual old-preimage and later-mask geometry precedes EVERY entire
StepOne value equality. The earlier real cut is an honest history input. -/
theorem avoided_middle_two_mask_step_one (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (q : ℕ) (hq : 0<q)
    (B : BlowupTower X A) (hB : IsGeoTestTower M B)
    (hAvoid : CentresAvoid (ordMask M q) B) (S : BlowupTower A Y)
    (hCut : IsStepOneCutTower hn (k+1)
      (MarkedIdeal.pullback (Subtype.val : ordMask M q → X) (companionOf n M q))
      (restrict (ordMask M q) (B.append S)))
    (hLater : IsGeoTestTower
      (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong M B) q → A)
        (companionOf n (geoTransformAlong M B) q))
      (restrict (ordMask (geoTransformAlong M B) q) S))
    (z : Y) (hzOld : (B.append S).proj z∈ordMask M q)
    (hzNew : S.proj z∈ordMask (geoTransformAlong M B) q)
    (hz : (⟨z,hzOld⟩ : openPreimage (B.append S) (ordMask M q))∈
      (geoTransformAlong
        (MarkedIdeal.pullback (Subtype.val : ordMask M q → X) (companionOf n M q))
        (restrict (ordMask M q) (B.append S))).cosupp) :
    (⟨z,hzNew⟩ : openPreimage S (ordMask (geoTransformAlong M B) q))∈
      (geoTransformAlong
        (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong M B) q → A)
          (companionOf n (geoTransformAlong M B) q))
        (restrict (ordMask (geoTransformAlong M B) q) S)).cosupp ∧
      ∀ t : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1))
        (MarkedIdeal.pullback (Subtype.val : ordMask M q → X) (companionOf n M q))
        (restrict (ordMask M q) (B.append S)) ⟨z,hzOld⟩=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1))
        (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong M B) q → A)
          (companionOf n (geoTransformAlong M B) q))
        (restrict (ordMask (geoTransformAlong M B) q) S) ⟨z,hzNew⟩ := by
  let W := ordMask M q
  let J := MarkedIdeal.pullback (Subtype.val : W → X) (companionOf n M q)
  let R := restrict W B
  let U := openPreimage B W
  let V := ordMask (geoTransformAlong M B) q
  let K := companionOf n (geoTransformAlong M B) q
  let N := MarkedIdeal.pullback (Subtype.val : U → A) K
  have hJ : IsInvDomain 2 J := isInvDomain_pullback_val_companionAlong hn hM W hq
  have hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d := by
    have h := isMaximalOrderAlong_compAt hn q (.refl : BlowupTower X X) hM
    rw [compAt_eq_pullback hn q .refl hM] at h
    exact h
  have hFlatCut := step_one_cut_restrict_append hn k W J hJ hMaxJ B S hCut
  have hLevel : IsLevelCutTower J (R.append (restrict U S)) :=
    stepOneCutTower_levelCut (X := CMfd.of (n := n) W)
      (Y := CMfd.of (n := n) (openPreimage S U)) (k := k+1) hn J
      (R.append (restrict U S)) hFlatCut
  obtain ⟨hN,hNT,_hNC,hCos,hValues⟩ := companion_step_one_rebase_values
    hn M hM q hq B hB hAvoid (restrict U S) hLevel
  have hOldLevel : IsLevelCutTower J (restrict W (B.append S)) :=
    stepOneCutTower_levelCut (X := CMfd.of (n := n) W)
      (Y := CMfd.of (n := n) (openPreimage (B.append S) W)) (k := k+1) hn J
      (restrict W (B.append S)) hCut
  have hOldTest : IsGeoTestTower J (restrict W (B.append S)) :=
    levelCutTower_geoTest (X := CMfd.of (n := n) W)
      (Y := CMfd.of (n := n) (openPreimage (B.append S) W)) J (restrict W (B.append S)) hOldLevel
  have hFlat := step_one_value_restrict_append hn W J hJ hMaxJ B S hOldTest
  have hzU : S.proj z∈U := by
    change B.proj (S.proj z)∈W
    simpa only [BlowupTower.proj_append,Function.comp_apply] using hzOld
  obtain ⟨hzFlat,hFlatVal⟩ := hFlat.2 z hzOld hzU hz
  have hzN : (⟨z,hzU⟩ : openPreimage S U)∈(geoTransformAlong N (restrict U S)).cosupp := by
    rw [←hCos]
    exact hzFlat
  have he : IsEmptyTower R := (isEmptyTower_restrict_iff W B).mpr hAvoid
  have hRT := isGeoTestTower_of_isEmptyTower J R he
  have hBaseMax := isMaximalOrderAlong_geoTransformAlong hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hMaxJ R hRT
  have hEq := CompanionRebase.restrictEquiv_companionOf_rebase hn hM hq B hB W hAvoid
  have hMaxN := actual_maximal_order _ N (restrictEquiv_symm hEq) hBaseMax
  have hCurrent := isInvDomain_geoTransformAlong hM B hB
  have hK : K.ideal.IsCoherent := (isInvDomain_companionAlong hn hCurrent hq).isWellFormed.isCoherent
  have hV : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : V → A) K) :=
    isInvDomain_pullback_val_companionAlong hn hCurrent V hq
  have hMaxV : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : V → A) K).N
      (MarkedIdeal.pullback (Subtype.val : V → A) K).ideal
      (MarkedIdeal.pullback (Subtype.val : V → A) K).d := by
    have h := isMaximalOrderAlong_compAt hn q (.refl : BlowupTower A A) hCurrent
    rw [compAt_eq_pullback hn q .refl hCurrent] at h
    exact h
  obtain ⟨hCosUV,hValUV⟩ := local_step_one_two_opens hn K hK U V hN hV hMaxN hMaxV S hNT hLater z hzU hzNew
  refine ⟨hCosUV.mp hzN,?_⟩
  intro t
  exact (hFlatVal t).symm.trans ((hValues t _ hzFlat).trans (hValUV hzN t))

private theorem actual_cosupp_history_eq (W : Opens X)
    (J : MarkedIdeal n (CMfd.of (n := n) W)) (S T : BlowupTower X Y)
    (h : S=T) (z : Y) (hpS : S.proj z∈W) (hpT : T.proj z∈W) :
    (⟨z,hpS⟩ : openPreimage S W)∈(geoTransformAlong J (restrict W S)).cosupp ↔
      (⟨z,hpT⟩ : openPreimage T W)∈(geoTransformAlong J (restrict W T)).cosupp := by
  cases h
  rfl

private theorem actual_value_history_eq (hn : 0<n) (t : ℕ) (W : Opens X)
    (J : MarkedIdeal n (CMfd.of (n := n) W)) (S T : BlowupTower X Y)
    (h : S=T) (z : Y) (hpS : S.proj z∈W) (hpT : T.proj z∈W) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1)) J (restrict W S) ⟨z,hpS⟩=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1)) J (restrict W T) ⟨z,hpT⟩ := by
  cases h
  rfl

private theorem actual_companion_value_eq (hn : 0<n) (t q : ℕ)
    (J N : MarkedIdeal n X) (h : J=N) (S : BlowupTower X Y) (z : Y)
    (hpJ : S.proj z∈ordMask J q) (hpN : S.proj z∈ordMask N q) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1))
      (MarkedIdeal.pullback (Subtype.val : ordMask J q → X) (companionOf n J q))
      (restrict (ordMask J q) S) ⟨z,hpJ⟩=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1))
        (MarkedIdeal.pullback (Subtype.val : ordMask N q → X) (companionOf n N q))
        (restrict (ordMask N q) S) ⟨z,hpN⟩ := by
  cases h
  rfl

/-- Genuine fixed reference geometry and actual query cosupport construct
both masks and the real avoided middle before comparing the two companions. -/
theorem fixed_companion_step_one_eq_own (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X Y) (hT : IsOrderCutTower M T) (q : ℕ) (hq : 0<q)
    (p : Y) (hp : p∈(geoTransformAlong M T).cosupp)
    (hpq : nmOrd (geoTransformAlong M T) p=q)
    (z : openPreimage (tail T (regimeRun (OrdRegime M q) T p))
      (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q))
    (hz : z∈(geoTransformAlong (compAt M q (head T (regimeRun (OrdRegime M q) T p)))
      (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q)
        (tail T (regimeRun (OrdRegime M q) T p)))).cosupp)
    (hOwn : IsStepOneCutTower hn (k+1)
      (compAt M q (head T (regimeRun (OrdRegime M q) T z.val)))
      (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T z.val))) q)
        (tail T (regimeRun (OrdRegime M q) T z.val)))) :
    ∃ hzOwn : (tail T (regimeRun (OrdRegime M q) T z.val)).proj z.val∈
      ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T z.val))) q,
      ∀ t : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1))
        (compAt M q (head T (regimeRun (OrdRegime M q) T p)))
        (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q)
          (tail T (regimeRun (OrdRegime M q) T p))) z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1))
        (compAt M q (head T (regimeRun (OrdRegime M q) T z.val)))
        (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T z.val))) q)
          (tail T (regimeRun (OrdRegime M q) T z.val))) ⟨z.val,hzOwn⟩ := by
  let rp := regimeRun (OrdRegime M q) T p
  let rz := regimeRun (OrdRegime M q) T z.val
  let Hp := head T rp
  let Hz := head T rz
  let Sp := tail T rp
  let Sz := tail T rz
  let Mz := geoTransformAlong M Hz
  let Wz := ordMask Mz q
  have hRun := order_cut_fixed_companion_point_run hn M hM T hT q hq p z hz
  have hUpper := orderCutTower_geoTest M T hT
  obtain ⟨hHz,hSz⟩ := (isGeoTestTower_iff_head_tail M T rz).mp hUpper
  obtain ⟨hHp,hSp⟩ := (isGeoTestTower_iff_head_tail M T rp).mp hUpper
  have hDz := isInvDomain_geoTransformAlong hM Hz hHz
  have hDp := isInvDomain_geoTransformAlong hM Hp hHp
  have hFixedTest := orderCutTower_current_companion_test hn M hM T hT q hq p
  have hQueryTest := orderCutTower_current_companion_test hn M hM T hT q hq z.val
  have hDict := mem_cosupp_compAt_iff hn hM hq Hp Sp hHp hSp hFixedTest z
  rw [←geoTransformAlong_head_tail M T rp] at hDict
  obtain ⟨hzUpper,hzq⟩ := hDict.mp hz
  obtain ⟨B,hB₁,hB₂,hAvoid,_hRel⟩ := exists_actual_middle_of_order_cut
    hn M hM T hT p z.val hp q hq hpq rp rz rfl rfl hRun.2
  have hGeo : IsGeoTestTower M (Hz.append B) := by rw [hB₁];exact hHp
  have hB : IsGeoTestTower Mz B := ((isGeoTestTower_append_iff M Hz B).mp hGeo).2
  have hModel : geoTransformAlong Mz B=geoTransformAlong M Hp := by
    rw [←geoTransformAlong_append,hB₁]
  have hOwnMask : Sz.proj z.val∈Wz :=
    (proj_tail_mem_ordMask hn hM T hUpper hzUpper (o := q) hzq).2
  have hOwnCos : (⟨z.val,hOwnMask⟩ : openPreimage Sz Wz)∈
      (geoTransformAlong (compAt M q Hz) (restrict Wz Sz)).cosupp := by
    have hd := mem_cosupp_compAt_iff hn hM hq Hz Sz hHz hSz hQueryTest ⟨z.val,hOwnMask⟩
    rw [←geoTransformAlong_head_tail M T rz] at hd
    exact hd.mpr ⟨hzUpper,hzq⟩
  have hCut : IsStepOneCutTower hn (k+1)
      (MarkedIdeal.pullback (Subtype.val : Wz → (split T rz).1) (companionOf n Mz q))
      (restrict Wz (B.append Sp)) := by
    rw [hB₂,←compAt_eq_pullback hn q Hz hDz]
    exact hOwn
  have hLater : IsGeoTestTower
      (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong Mz B) q → (split T rp).1)
        (companionOf n (geoTransformAlong Mz B) q))
      (restrict (ordMask (geoTransformAlong Mz B) q) Sp) := by
    rw [hModel,←compAt_eq_pullback hn q Hp hDp]
    exact hFixedTest
  have hzOld : (B.append Sp).proj z.val∈Wz := by rw [hB₂];exact hOwnMask
  have hzNew : Sp.proj z.val∈ordMask (geoTransformAlong Mz B) q := by
    rw [hModel]
    exact z.property
  have hzEarlier : (⟨z.val,hzOld⟩ : openPreimage (B.append Sp) Wz)∈
      (geoTransformAlong
        (MarkedIdeal.pullback (Subtype.val : Wz → (split T rz).1) (companionOf n Mz q))
        (restrict Wz (B.append Sp))).cosupp := by
    apply (actual_cosupp_history_eq Wz _ (B.append Sp) Sz hB₂ z.val hzOld hOwnMask).mpr
    rw [←compAt_eq_pullback hn q Hz hDz]
    exact hOwnCos
  have hv := (avoided_middle_two_mask_step_one hn k Mz hDz q hq B hB hAvoid Sp
    hCut hLater z.val hzOld hzNew hzEarlier).2
  refine ⟨hOwnMask,?_⟩
  intro t
  have hOldVal := actual_value_history_eq hn t Wz
    (MarkedIdeal.pullback (Subtype.val : Wz → (split T rz).1) (companionOf n Mz q))
    (B.append Sp) Sz hB₂ z.val hzOld hOwnMask
  conv_rhs at hOldVal => rw [←compAt_eq_pullback hn q Hz hDz]
  have hNewVal := actual_companion_value_eq hn t q (geoTransformAlong Mz B)
    (geoTransformAlong M Hp) hModel Sp z.val hzNew z.property
  rw [←compAt_eq_pullback hn q Hp hDp] at hNewVal
  exact hNewVal.symm.trans ((hv t).symm.trans hOldVal)

end
end Hironaka.HironakaOriginalFixedCompanionStepOneComparison
