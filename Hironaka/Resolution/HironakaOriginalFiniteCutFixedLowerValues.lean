/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteCutPositiveLowerValues
import Hironaka.Resolution.HironakaOriginalZeroCurveLowerComparison
import Hironaka.Resolution.HironakaOriginalFiniteStepOneCutMiddleHistory
/-! Actual zero-level and all-level fixed-reference lower values from literal original
finite cuts. No lower TEST, canonicity or numerical certificate is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteCutFixedLowerValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong HomogenizedIdealAlongTower CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneMaskTower StepOneNearby StepOneLowerDomain
  StepOneCompare StepOneCanonicalTail HironakaOriginalFrozenRecursiveLower HironakaOriginalFiniteLevelCutLowerTests
  HironakaOriginalFiniteStepOneCutMaskAvoidance HironakaOriginalFiniteStepOneCutMiddleHistory
  HironakaOriginalFiniteCutPositiveLowerValues HironakaOriginalZeroCurveLowerComparison
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem domain_at_depth (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J) (d : ℕ) :
    IsInvDomain (d+2) J := by
  refine ⟨hJ.isWellFormed,?_,hJ.one_le_d,hJ.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hJ.dimLE x hx
  exact ⟨j,by omega,hreg⟩

/-- All ordinary lower domains, TESTs, actual points and earlier-mask avoidance
are constructed from the genuine finite cut history before numeric comparison. -/
theorem finite_cut_zero_stepone_eq_fixed_lower (hn : 0<n) (d : ℕ)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn (d+1) J T)
    (z : Y) (hz : z∈(geoTransformAlong J T).cosupp) (hns : ¬IsSpecial J T z)
    (hs : level J T z=0) :
    let r := regimeRun (stepRegime J 0) T z
    let H := head T r
    let S := tail T r
    let W := lowerMask J 0 H (S.proj z)
    let K := lowerMarkedM J 0 H (S.proj z)
    ∀ p : openPreimage S W,p∈(geoTransformAlong K (restrict W S)).cosupp →
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J T p.val=
        toLex (0,(((invFamily hn (d+1)).inv K (restrict W S) p : ValTy (d+1)) : WithTop (ValTy (d+1)))) := by
  let r := regimeRun (stepRegime J 0) T z
  let H := head T r
  let S := tail T r
  let W := lowerMask J 0 H (S.proj z)
  let K := lowerMarkedM J 0 H (S.proj z)
  change ∀ p : openPreimage S W,p∈(geoTransformAlong K (restrict W S)).cosupp →
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J T p.val=
      toLex (0,(((invFamily hn (d+1)).inv K (restrict W S) p : ValTy (d+1)) : WithTop (ValTy (d+1))))
  intro p hp
  have hLevel := stepOneCutTower_levelCut hn J T hT
  have hUpper := levelCutTower_geoTest J T hLevel
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar : IsGeoTestTower (barMarked J) T := (he.2 T).1.mpr hUpper
  have hzBar : z∈(geoTransformAlong (barMarked J) T).cosupp := by
    rw [(he.2 T).2 hBar];exact hz
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hBar hzBar hns
  rw [hs] at hReg hHead
  obtain ⟨hDomZ,hTestZ,_hzMask,_hzPoint,hDict⟩ :=
    finite_cut_lower_data_at_level hn J hJ hmax T hLevel z hz hns 0 hs
  obtain ⟨hpOriginal,hpLevel⟩ := (hDict p).mp hp
  have hApp : H.append S=T := head_append_tail T r
  have hBarHS : IsGeoTestTower (barMarked J) (H.append S) := by rw [hApp];exact hBar
  obtain ⟨hpReg,hpRun⟩ := stepRegime_and_le_regimeRun_of_mem_lowerMask J hJ.isWellFormed
    hJ.one_le_d hmax H S hBarHS hReg.1 p.property (by rw [hApp];exact hpLevel)
  rw [hApp] at hpReg hpRun
  have hSlen : S.length=r := by
    dsimp only [S]
    rw [length_tail]
    have hh := regimeRun_le_length (stepRegime J 0) T z
    change r≤T.length at hh
    omega
  let rp := regimeRun (stepRegime J 0) T p.val
  have hle : r≤rp := hSlen.symm.trans_le hpRun
  obtain ⟨hDomP,hTestP,hpMask,hpPoint,_hpDict⟩ :=
    finite_cut_lower_data_at_level hn J hJ hmax T hLevel p.val hpOriginal hpReg.2 0 hpLevel
  have hpBar : p.val∈(geoTransformAlong (barMarked J) T).cosupp := by
    rw [(he.2 T).2 hBar];exact hpOriginal
  obtain ⟨hpHead,_hpHeadPoint⟩ :=
    stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hBar hpBar hpReg.2
  rw [hpLevel] at hpHead
  obtain ⟨B,e₁,e₂,hAvoid⟩ := exists_actual_middle_of_stepone_cut hn J
    (domain_at_depth J hJ d) hmax T hT z p.val hz 0 hs r rp rfl rfl hle hpHead.1
  have hUpperB : IsGeoTestTower (barMarked J) (((head T rp).append B).append S) := by
    rw [e₁,hApp];exact hBar
  have hDom₀ : IsInvDomain 1 (lowerMarkedM J 0 ((head T rp).append B) (S.proj z)) := by
    rw [e₁];exact hDomZ
  have hTest₀ : IsGeoTestTower (lowerMarkedM J 0 ((head T rp).append B) (S.proj z))
      (restrict (lowerMask J 0 ((head T rp).append B) (S.proj z)) S) := by
    rw [e₁];exact hTestZ
  have hmem : S.proj p.val∈lowerMask J 0 ((head T rp).append B) (S.proj z) := by
    rw [e₁];exact p.property
  have hmem₁ : (B.append S).proj p.val∈lowerMask J 0 (head T rp) ((B.append S).proj p.val) := by
    rw [e₂];exact hpMask
  have hDom₁ : IsInvDomain 1 (lowerMarkedM J 0 (head T rp) ((B.append S).proj p.val)) := by
    rw [e₂];exact hDomP
  have hTest₁ : IsGeoTestTower (lowerMarkedM J 0 (head T rp) ((B.append S).proj p.val))
      (restrict (lowerMask J 0 (head T rp) ((B.append S).proj p.val)) (B.append S)) := by
    rw [e₂];exact hTestP
  have hCos₁ : (⟨p.val,hmem₁⟩ : openPreimage (B.append S)
      (lowerMask J 0 (head T rp) ((B.append S).proj p.val)))∈
      (geoTransformAlong (lowerMarkedM J 0 (head T rp) ((B.append S).proj p.val))
        (restrict (lowerMask J 0 (head T rp) ((B.append S).proj p.val)) (B.append S))).cosupp := by
    revert hmem₁
    rw [e₂]
    intro hmem₁
    exact hpPoint
  have hAvoid' : RestrictEmptyTower.CentresAvoid
      (lowerMask J 0 (head T rp) ((B.append S).proj p.val)) B := by
    rw [e₂];exact hAvoid
  have hHead₀ : S.proj z∈(geoTransformAlong (barMarked J) ((head T rp).append B)).cosupp := by
    rw [e₁];exact hHead
  have hpBarB : p.val∈(geoTransformAlong (barMarked J) (((head T rp).append B).append S)).cosupp := by
    rw [e₁,hApp];exact hpBar
  have hv := zero_curve_lower_value_rebase hn d J hJ.isWellFormed hJ.one_le_d hmax
    (head T rp) B S hUpperB (S.proj z) hHead₀ hDom₀ hTest₀ p.val hmem
    hpBarB hmem₁ hDom₁ hTest₁ hCos₁ hAvoid'
  have hv' : Seq.StepOneValueMasked.lowerValueL (invFamily hn (d+1)) J (lowerMarkedM J)
      0 (head T rp) (tail T rp) p.val=
      (((invFamily hn (d+1)).inv K (restrict W S) p : ValTy (d+1)) : WithTop (ValTy (d+1))) := by
    have hvAll : ∀ (hq : S.proj p.val∈lowerMask J 0 ((head T rp).append B) (S.proj z)),
        Seq.StepOneValueMasked.lowerValueL (invFamily hn (d+1)) J (lowerMarkedM J)
          0 (head T rp) (B.append S) p.val=
        (((invFamily hn (d+1)).inv (lowerMarkedM J 0 ((head T rp).append B) (S.proj z))
          (restrict (lowerMask J 0 ((head T rp).append B) (S.proj z)) S) ⟨p.val,hq⟩ :
          ValTy (d+1)) : WithTop (ValTy (d+1))) := fun _ => hv
    rw [e₁,e₂] at hvAll
    exact hvAll p.property
  change Seq.StepOneValueMasked.stepOneInvL (invFamily hn (d+1)) J (lowerMarkedM J) T p.val=_
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial (invFamily hn (d+1)) J
    (lowerMarkedM J) T hpReg.2,hpLevel]
  exact congrArg (fun v => toLex (0,v)) hv'

/-- The unchanged original StepOne function is the FULL value on the SAME
computed fixed reference at EVERY level, with all lower data internally built. -/
theorem finite_cut_stepone_eq_fixed_lower (hn : 0<n) (d : ℕ)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn (d+1) J T)
    (z : Y) (hz : z∈(geoTransformAlong J T).cosupp) (hns : ¬IsSpecial J T z) :
    ∀ p : patchAt J T z,p∈(geoTransformAlong (lowerAt J T z) (lowerTailAt J T z)).cosupp →
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J T p.val=
        toLex (level J T z,(((invFamily hn (d+1)).inv (lowerAt J T z) (lowerTailAt J T z) p :
          ValTy (d+1)) : WithTop (ValTy (d+1)))) := by
  let F : ℕ → Prop := fun s =>
    let r := regimeRun (stepRegime J s) T z
    let H := head T r
    let S := tail T r
    let W := lowerMask J s H (S.proj z)
    let K := lowerMarkedM J s H (S.proj z)
    ∀ p : openPreimage S W,p∈(geoTransformAlong K (restrict W S)).cosupp →
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J T p.val=
        toLex (s,(((invFamily hn (d+1)).inv K (restrict W S) p : ValTy (d+1)) : WithTop (ValTy (d+1))))
  change F (level J T z)
  by_cases hZero : level J T z=0
  · have hF : F 0 := finite_cut_zero_stepone_eq_fixed_lower hn d J hJ hmax T hT z hz hns hZero
    exact (congrArg F hZero).mpr hF
  · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hZero
    have hF : F (s+1) := finite_cut_positive_stepone_eq_fixed_lower hn d J hJ hmax T hT z hz hns s hs
    exact (congrArg F hs).mpr hF

end
end Hironaka.HironakaOriginalFiniteCutFixedLowerValues
