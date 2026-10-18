/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalEmptyPrefixLevelCutTransport
import Hironaka.Resolution.HironakaOriginalPositiveEmptyPrefixHeadValues
import Hironaka.Resolution.HironakaOriginalPositiveCurveLowerComparison
/-! Actual original lower geometry is constructed BEFORE the positive
run-crossing numeric comparison; lower CAN is never an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveEmptyPrefixBaseValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactRepresentative ContactEmptyPrefix
  InvDomainMemberRestriction InvDomainRebase StepOneValue StepOneValueMasked StepOneLowerDomain
  StepOneRegime StepOneMaskTower StepOneEmptyPrefix CanonicalCentres
  HironakaOriginalFrozenRecursiveLower HironakaOriginalFiniteLevelCutLowerTests
  HironakaOriginalEmptyPrefixLevelCutTransport HironakaOriginalPositiveEmptyPrefixHeadValues
  HironakaOriginalPositiveCurveLowerComparison
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionInvariantSpec (IsInvDomain)
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

/-- The entire real open pullbacks transport ordinary lower geometry. -/
theorem masked_curve_geometry_of_restrictEquiv
    (M N : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : N.IsWellFormed)
    (hEq : RestrictEquiv M N) {U V : Opens B} (hUV : U=V)
    (hDom : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : U → B) M))
    (T : BlowupTower B Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → B) M) (restrict U T))
    (z : Y) (hz : T.proj z∈U)
    (hCos : (⟨z,hz⟩ : openPreimage T U)∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → B) M) (restrict U T)).cosupp) :
    IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : V → B) N) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → B) N) (restrict V T) ∧
      ∃ hv : T.proj z∈V,(⟨z,hv⟩ : openPreimage T V)∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → B) N) (restrict V T)).cosupp := by
  subst V
  have he := restrictEquiv_pullback_val U hEq hM.isCoherent hN.isCoherent
  have hNU := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN U
  have hd := isInvDomain_of_restrictEquiv hDom he hNU.isCoherent
  have hw := RestrictEquiv.wEquiv (X := CMfd.of (n := n) U) he
    hDom.isWellFormed.isClosedSubmanifold_N.1 hDom.isWellFormed.isCoherent hNU.isCoherent
  refine ⟨hd,((hw.2 (restrict U T)).1).mp hTest,hz,?_⟩
  rwa [←(hw.2 (restrict U T)).2 hTest]

private theorem actual_crossing_run (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
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

private theorem positive_base_values (hn : 0<n) (k s : ℕ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsGeoTestTower (barMarked J) (P.append T)) (z : Y)
    (hOld : ActualLower J (s+1) .refl (P.append T) z)
    (hNew : ActualLower (geoTransformAlong J P) (s+1) .refl T z) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) (s+1) .refl (P.append T) z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) (geoTransformAlong J P)
        (lowerMarkedM (geoTransformAlong J P)) (s+1) .refl T z := by
  obtain ⟨hDold,hTestOld,hpOld,hCosOld⟩ := hOld
  obtain ⟨hDnew,hTestNew,hpNew,hCosNew⟩ := hNew
  have hPt := ((isGeoTestTower_append_iff _ P T).mp hT).1
  have hJP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ P
    (isGeoTestTower_of_isEmptyTower J P hP)
  have hBarNew := isWellFormed_barMarked _ hJP
  have hBarOld := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked J hJ) P hPt
  have hEqJ := restrictEquiv_barMarked_append J hJ hd P hP .refl hPt
  obtain ⟨L,hL,hE⟩ := origMembers_emptyPrefix J P hP .refl
  have hEqM : RestrictEquiv
      (memberRestrict (barMarked (geoTransformAlong J P))
        (membersThrough (barMarked (geoTransformAlong J P)).E
          (origMembers (geoTransformAlong J P) .refl) (T.proj z)))
      (memberRestrict (geoTransformAlong (barMarked J) P)
        (membersThrough (geoTransformAlong (barMarked J) P).E (origMembers J P) (T.proj z))) := by
    rw [hE,membersThrough_append_of_forall_eq_empty _ _ _ hL]
    exact restrictEquiv_memberRestrict_membersThrough hEqJ hBarNew.isCoherent hBarOld.isCoherent _ _
  have hW := maskA_emptyPrefix J hJ hd P hP .refl hPt (T.proj z)
  simp only [BlowupTower.append_refl] at hW
  obtain ⟨hDmid,hTestMid,hpMid,hCosMid⟩ := masked_curve_geometry_of_restrictEquiv (B := A) _ _
    (isWellFormed_memberRestrict hn hBarNew _) (isWellFormed_memberRestrict hn hBarOld _)
      hEqM hW hDnew T hTestNew z hpNew hCosNew
  change IsInvDomain 1 (lowerMarkedM J (s+1) P (T.proj z)) at hDmid
  change IsGeoTestTower (lowerMarkedM J (s+1) P (T.proj z))
    (restrict (lowerMask J (s+1) P (T.proj z)) T) at hTestMid
  change T.proj z∈lowerMask J (s+1) P (T.proj z) at hpMid
  have hMid : ActualLower J (s+1) P T z := ⟨hDmid,hTestMid,hpMid,hCosMid⟩
  have hRP := BlowupTower.refl_append P
  have hMid' : ActualLower J (s+1) (BlowupTower.refl.append P) T z :=
    (congrArg (fun H : BlowupTower X A => ActualLower J (s+1) H T z) hRP).mpr hMid
  obtain ⟨hDmid',hTestMid',hpMid',hCosMid'⟩ := hMid'
  have hRebase := positive_curve_lower_value_rebase hn k J hJ s .refl P T
    (by simpa only [BlowupTower.refl_append] using hT) (T.proj z)
    hDmid' hTestMid' z hpMid' rfl hCosMid' hpOld hDold hTestOld hCosOld
      (ContactLowerValue.centresAvoid_of_isEmptyTower _ P hP)
  have hRebaseValue := hRebase.trans
    (Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) J (lowerMarkedM J)
      (s := s+1) (T₀ := BlowupTower.refl.append P) (T₁ := T) (y := z) hpMid').symm
  have hHead := positive_lower_value_empty_prefix_head hn (k+1) J hJ hd P hP .refl hPt T s z
  have hValRP := congrArg (fun H : BlowupTower X A =>
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) (s+1) H T z) hRP
  exact hRebaseValue.trans (hValRP.trans hHead)

/-- All lower geometry is constructed from ONLY original positive run data. -/
theorem positive_base_values_of_level_cut_empty_prefix (hn : 0<n) (k s : ℕ)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsLevelCutTower J (P.append T)) (z : Y)
    (hz : z∈(geoTransformAlong J (P.append T)).cosupp)
    (hns : ¬IsSpecial J (P.append T) z) (hs : level J (P.append T) z=s+1)
    (hr : regimeRun (stepRegime (geoTransformAlong J P) (s+1)) T z=T.length) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) (s+1) .refl (P.append T) z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) (geoTransformAlong J P)
        (lowerMarkedM (geoTransformAlong J P)) (s+1) .refl T z := by
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar := (he.2 (P.append T)).1.mpr (levelCutTower_geoTest J (P.append T) hT)
  have hSource := empty_prefix_current_lower_data hn 1 J hJ hmax P hP T hT z hz hns
  obtain ⟨hJP,hMaxP,hLevelP,_hOther⟩ := hSource
  have hzP : z∈(geoTransformAlong (geoTransformAlong J P) T).cosupp := by
    simpa only [geoTransformAlong_append] using hz
  have hnsP : ¬IsSpecial (geoTransformAlong J P) T z :=
    fun h => hns ((isSpecial_emptyPrefix_iff J hJ.isWellFormed hJ.one_le_d P hP T hBar z).mp h)
  have hl := level_emptyPrefix J P hP T z
  have hReg : stepRegime (geoTransformAlong J P) (s+1) T z := ⟨hl.trans hs,hnsP⟩
  have hRun := actual_crossing_run J hJ.isWellFormed hJ.one_le_d P hP T hBar (s+1) z hReg hr
  have hOld := actual_current_lower hn J hJ hmax (P.append T) hT z hz hns
  have hNew := actual_current_lower hn _ hJP hMaxP T hLevelP z hzP hnsP
  change ActualLower J (level J (P.append T) z)
    (head (P.append T) (regimeRun (stepRegime J (level J (P.append T) z)) (P.append T) z))
    (tail (P.append T) (regimeRun (stepRegime J (level J (P.append T) z)) (P.append T) z)) z at hOld
  rw [hs,hRun] at hOld
  change ActualLower (geoTransformAlong J P) (level (geoTransformAlong J P) T z)
    (head T (regimeRun (stepRegime (geoTransformAlong J P) (level (geoTransformAlong J P) T z)) T z))
    (tail T (regimeRun (stepRegime (geoTransformAlong J P) (level (geoTransformAlong J P) T z)) T z)) z at hNew
  rw [hl,hs,hr] at hNew
  simp only [head,tail] at hOld hNew
  rw [split_of_length_le (P.append T) _ le_rfl] at hOld
  rw [split_of_length_le T _ le_rfl] at hNew
  exact positive_base_values hn k s J hJ.isWellFormed hJ.one_le_d P hP T hBar z hOld hNew

end
end Hironaka.HironakaOriginalPositiveEmptyPrefixBaseValues
