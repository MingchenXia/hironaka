/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalEmptyPrefixLevelCutTransport
import Hironaka.Resolution.HironakaOriginalZeroEmptyPrefixHeadValues
import Hironaka.Resolution.HironakaOriginalZeroCurveLowerComparison
/-! Actual original zero-contact geometry precedes run-crossing FULL values.
No lower CAN or independent tangent-function equality is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroEmptyPrefixBaseValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  HomogenizedIdealAlong HomogenizedIdealAlongTower InvDomainMemberRestriction InvDomainRebase
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRegime StepOneMaskTower StepOneEmptyPrefix
  StepOneCompare CanonicalCentres HironakaOriginalFrozenRecursiveLower HironakaOriginalFiniteLevelCutLowerTests
  HironakaOriginalEmptyPrefixLevelCutTransport HironakaOriginalZeroEmptyPrefixHeadValues
  HironakaOriginalZeroCurveLowerComparison
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionInvariantSpec (IsInvDomain DimLE)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

/-- Only ordinary genuine DOMAIN/TEST/cosupport, never lower CAN. -/
private def ActualLower (M : MarkedIdeal n X) (s : ℕ) (H : BlowupTower X B)
    (T : BlowupTower B Y) (z : Y) : Prop :=
  IsInvDomain 1 (lowerMarkedM M s H (T.proj z)) ∧
    IsGeoTestTower (lowerMarkedM M s H (T.proj z)) (restrict (lowerMask M s H (T.proj z)) T) ∧
    ∃ hp : T.proj z∈lowerMask M s H (T.proj z),
      (⟨z,hp⟩ : openPreimage T (lowerMask M s H (T.proj z)))∈
        (geoTransformAlong (lowerMarkedM M s H (T.proj z)) (restrict (lowerMask M s H (T.proj z)) T)).cosupp

private theorem actual_current_lower (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 2 M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T) (z : Y)
    (hz : z∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T z) :
    ActualLower M (level M T z) (head T (runAt M T z)) (tail T (runAt M T z)) z := by
  obtain ⟨hd,ht,_hc,hp,hcos,_dict⟩ := levelCutTower_current_lower_data hn M hM hmax T hT z hz hns
  exact ⟨hd,ht,hp,hcos⟩

/-- The entire original run includes EVERY genuine empty prefix slot. -/
theorem run_crossing_empty_prefix (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsGeoTestTower (barMarked J) (P.append T)) (s : ℕ) (z : Y)
    (hreg : stepRegime (geoTransformAlong J P) s T z)
    (heq : regimeRun (stepRegime (geoTransformAlong J P) s) T z=T.length) :
    regimeRun (stepRegime J s) (P.append T) z=(P.append T).length := by
  have hG : ∀ {V Z : CMfd.{u} n} (H : BlowupTower A V) (C : Set V) (π : Z → V)
      (hπ : IsBlowupAlong n C π),IsGeoTestTower (barMarked J) (P.append (.step H C π hπ)) →
        IsGeoTestTower (barMarked J) (P.append H) := fun _ _ _ _ h => h.1
  have hQ : ∀ {V : CMfd.{u} n} (H : BlowupTower A V) (v : V),
      IsGeoTestTower (barMarked J) (P.append H) →
        (stepRegime J s (P.append H) v ↔ stepRegime (geoTransformAlong J P) s H v) :=
    fun H v hH => (stepRegime_emptyPrefix_iff J hJ hd P hP H hH s v).symm
  have hBase := regime_base_of_regimeRun_eq _ T z hreg heq
  have hPt := ((isGeoTestTower_append_iff _ P T).mp hT).1
  have hBaseP : stepRegime J s P (T.proj z) := (hQ .refl _ hPt).mpr hBase
  have hStep : ∀ {V Z : CMfd.{u} n} (H : BlowupTower X V) (π : Z → V)
      (hπ : IsBlowupAlong n (∅ : Set V) π),IsEmptyTower H → ∀ w : Z,
        stepRegime J s (.step H ∅ π hπ) w → stepRegime J s H (π w) := by
    intro V Z H π hπ hH w hw
    have hHt := isGeoTestTower_of_isEmptyTower (barMarked J) H hH
    have hE := fun E hE => hJ.isSNCDivisor.1 E hE
    have hl := level_step_of_notMem J hE H ∅ π hπ (notMem_empty (π w))
    have hs := isSpecial_step_iff_of_notMem J hJ.isClosedSubmanifold_N hJ.isCoherent hE H hHt ∅ π hπ
      (notMem_empty (π w))
    exact ⟨hl.symm.trans hw.1,fun h => hw.2 (hs.mpr h)⟩
  have hRunP := regimeRun_eq_length_of_isEmptyTower (stepRegime J s) hStep P hP _ hBaseP
  rw [regimeRun_append_of_eq _ _ P (fun H => IsGeoTestTower (barMarked J) (P.append H)) hG hQ T z hT heq,
    hRunP,BlowupTower.length_append]
  omega

private theorem actual_zero_base (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 2 M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T) (z : Y)
    (hz : z∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T z)
    (hs : level M T z=0) (hr : regimeRun (stepRegime M 0) T z=T.length) :
    ActualLower M 0 .refl T z := by
  have hData := actual_current_lower hn M hM hmax T hT z hz hns
  change ActualLower M (level M T z)
    (head T (regimeRun (stepRegime M (level M T z)) T z))
    (tail T (regimeRun (stepRegime M (level M T z)) T z)) z at hData
  rw [hs,hr] at hData
  simp only [head,tail] at hData
  rw [split_of_length_le T _ le_rfl] at hData
  exact hData

/-- Actual DOMAIN2/current geometry supplies BOTH independent zero-contact
references before every requested positive lower FULL depth comparison. -/
theorem zero_base_values_of_level_cut_empty_prefix (hn : 0<n) (k : ℕ)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsLevelCutTower J (P.append T)) (z : Y)
    (hz : z∈(geoTransformAlong J (P.append T)).cosupp)
    (hns : ¬IsSpecial J (P.append T) z) (hs : level J (P.append T) z=0)
    (hr : regimeRun (stepRegime (geoTransformAlong J P) 0) T z=T.length) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) 0 .refl (P.append T) z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) (geoTransformAlong J P)
        (lowerMarkedM (geoTransformAlong J P)) 0 .refl T z := by
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar := (he.2 (P.append T)).1.mpr (levelCutTower_geoTest J (P.append T) hT)
  have hzBar : z∈(geoTransformAlong (barMarked J) (P.append T)).cosupp := by
    rw [(he.2 (P.append T)).2 hBar];exact hz
  obtain ⟨hJP,hMaxP,hLevelP,_hOther⟩ := empty_prefix_current_lower_data hn 1 J hJ hmax P hP T hT z hz hns
  have hzP : z∈(geoTransformAlong (geoTransformAlong J P) T).cosupp := by
    simpa only [geoTransformAlong_append] using hz
  have hnsP : ¬IsSpecial (geoTransformAlong J P) T z :=
    fun h => hns ((isSpecial_emptyPrefix_iff J hJ.isWellFormed hJ.one_le_d P hP T hBar z).mp h)
  have hl := level_emptyPrefix J P hP T z
  have hReg : stepRegime (geoTransformAlong J P) 0 T z := ⟨hl.trans hs,hnsP⟩
  have hRun := run_crossing_empty_prefix J hJ.isWellFormed hJ.one_le_d P hP T hBar 0 z hReg hr
  have hOld := actual_zero_base hn J hJ hmax (P.append T) hT z hz hns hs hRun
  have hNew := actual_zero_base hn _ hJP hMaxP T hLevelP z hzP hnsP (hl.trans hs) hr
  obtain ⟨hDold,hTestOld,hpOld,hCosOld⟩ := hOld
  obtain ⟨hDnew,hTestNew,hpNew,_hCosNew⟩ := hNew
  obtain ⟨hPt,hTail⟩ := (isGeoTestTower_append_iff _ P T).mp hBar
  have hBarP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked J hJ.isWellFormed) P hPt
  have hyP : T.proj z∈(geoTransformAlong (barMarked J) P).cosupp :=
    proj_mem_cosupp_of_mem_cosupp hBarP.isClosedSubmanifold_N hBarP.isCoherent T hTail
      (by simpa only [geoTransformAlong_append] using hzBar)
  have hBase := regime_base_of_regimeRun_eq _ T z hReg hr
  have hRegP : stepRegime J 0 P (T.proj z) :=
    (stepRegime_emptyPrefix_iff J hJ.isWellFormed hJ.one_le_d P hP .refl hPt 0 (T.proj z)).mp hBase
  obtain ⟨hpMid,hDmid⟩ := mem_lowerMask_and_isInvDomain_M J hJ.isWellFormed hJ.one_le_d
    hn hmax hJ.dimLE P hPt hyP hRegP
  obtain ⟨hTestMid,hDictMid⟩ := isGeoTestTower_cosupp_lowerMarkedB J hJ.isWellFormed
    hJ.one_le_d hmax P T hBar hyP
  have hMid : ActualLower J 0 P T z := by
    refine ⟨hDmid,hTestMid,hpMid,?_⟩
    change (⟨z,hpMid⟩ : openPreimage T (maskB J P (T.proj z)))∈
      (geoTransformAlong (lowerMarkedB J P (T.proj z)) (restrict (maskB J P (T.proj z)) T)).cosupp
    rw [hDictMid]
    exact hzBar
  have hRP := BlowupTower.refl_append P
  have hMid' : ActualLower J 0 (BlowupTower.refl.append P) T z :=
    (congrArg (fun H : BlowupTower X A => ActualLower J 0 H T z) hRP).mpr hMid
  obtain ⟨hDmid',hTestMid',hpMid',_hCosMid'⟩ := hMid'
  have hyP' : T.proj z∈(geoTransformAlong (barMarked J) (BlowupTower.refl.append P)).cosupp :=
    (congrArg (fun H : BlowupTower X A => T.proj z∈(geoTransformAlong (barMarked J) H).cosupp) hRP).mpr hyP
  have hUpper : IsGeoTestTower (barMarked J) ((BlowupTower.refl.append P).append T) := by
    rw [hRP];exact hBar
  have hzUpper : z∈(geoTransformAlong (barMarked J) ((BlowupTower.refl.append P).append T)).cosupp := by
    rw [hRP];exact hzBar
  have hRebase := zero_curve_lower_value_rebase hn k J hJ.isWellFormed hJ.one_le_d hmax
    .refl P T hUpper (T.proj z) hyP' hDmid' hTestMid' z hpMid' hzUpper
    hpOld hDold hTestOld hCosOld (ContactLowerValue.centresAvoid_of_isEmptyTower _ P hP)
  have hRebaseValue := hRebase.trans
    (Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) J (lowerMarkedM J)
      (s := 0) (T₀ := BlowupTower.refl.append P) (T₁ := T) (y := z) hpMid').symm
  have hHead := zero_lower_value_empty_prefix_head hn k J hJ.isWellFormed hJ.one_le_d P hP .refl T
    hBar z hzBar hDmid hTestMid hDnew hTestNew hpMid hpNew
  have hValRP := congrArg (fun H : BlowupTower X A =>
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) 0 H T z) hRP
  exact hRebaseValue.trans (hValRP.trans hHead)

end
end Hironaka.HironakaOriginalZeroEmptyPrefixBaseValues
