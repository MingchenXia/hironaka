/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPositiveEmptyPrefixBaseValues
import Hironaka.Resolution.HironakaOriginalZeroEmptyPrefixBaseValues
import Hironaka.Resolution.HironakaOriginalZeroEmptyPrefixHeadValues
import Hironaka.Resolution.HironakaOriginalFiniteStepOneCutMaskAvoidance
/-! Entire original DOMAIN2 StepOne values and real whole-cut recipes
across actual empty prefixes, without canonicality on either history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoStepOneEmptyPrefix
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong HomogenizedIdealAlongTower InvDomainTowerAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRegime StepOneEmptyPrefix
  CanonicalCentres HironakaOriginalFrozenRecursiveLower HironakaOriginalFiniteLevelCutLowerTests
  HironakaOriginalEmptyPrefixLevelCutTransport HironakaOriginalPositiveEmptyPrefixHeadValues
  HironakaOriginalZeroEmptyPrefixHeadValues HironakaOriginalPositiveEmptyPrefixBaseValues
  HironakaOriginalZeroEmptyPrefixBaseValues HironakaOriginalFiniteStepOneCutMaskAvoidance
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A B Y Z : CMfd.{u} n}

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

/-- Actual lower geometry precedes both genuine run cases of the unchanged
original StepOne value, at every positive lower FULL depth. -/
theorem step_one_values_empty_prefix (hn : 0<n) (k : ℕ)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsLevelCutTower J (P.append T)) (z : Y)
    (hz : z∈(geoTransformAlong J (P.append T)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J (P.append T) z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (geoTransformAlong J P) T z := by
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar := (he.2 (P.append T)).1.mpr (levelCutTower_geoTest J (P.append T) hT)
  have hzBar : z∈(geoTransformAlong (barMarked J) (P.append T)).cosupp := by
    rw [(he.2 (P.append T)).2 hBar];exact hz
  have hPt := isGeoTestTower_of_isEmptyTower J P hP
  have hJP := isInvDomain_geoTransformAlong hJ P hPt
  have hMaxP := isMaximalOrderAlong_geoTransformAlong hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hmax P hPt
  have hLevelP := level_cut_tail_of_empty_prefix J hJ.isWellFormed hJ.one_le_d P hP T hT
  have hzP : z∈(geoTransformAlong (geoTransformAlong J P) T).cosupp := by
    simpa only [geoTransformAlong_append] using hz
  have hG : ∀ {V Q : CMfd.{u} n} (H : BlowupTower A V) (C : Set V) (π : Q → V)
      (hπ : IsBlowupAlong n C π),IsGeoTestTower (barMarked J) (P.append (.step H C π hπ)) →
        IsGeoTestTower (barMarked J) (P.append H) := fun _ _ _ _ h => h.1
  have hQ : ∀ (s : ℕ) {V : CMfd.{u} n} (H : BlowupTower A V) (v : V),
      IsGeoTestTower (barMarked J) (P.append H) →
        (stepRegime J s (P.append H) v ↔ stepRegime (geoTransformAlong J P) s H v) :=
    fun s _ H v hH => (stepRegime_emptyPrefix_iff J hJ.isWellFormed hJ.one_le_d P hP H hH s v).symm
  have hl := level_emptyPrefix J P hP T z
  by_cases hs : IsSpecial J (P.append T) z
  · have hsP := (isSpecial_emptyPrefix_iff J hJ.isWellFormed hJ.one_le_d P hP T hBar z).mpr hs
    show Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) _ z=
      Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) _ (lowerMarkedM _) _ z
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ _ _ _ hs,
      Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ _ _ _ hsP,hl]
  · have hsP : ¬IsSpecial (geoTransformAlong J P) T z :=
      fun h => hs ((isSpecial_emptyPrefix_iff J hJ.isWellFormed hJ.one_le_d P hP T hBar z).mp h)
    have hD : ActualLower J (level J (P.append T) z)
        (head (P.append T) (regimeRun (stepRegime J (level J (P.append T) z)) (P.append T) z))
        (tail (P.append T) (regimeRun (stepRegime J (level J (P.append T) z)) (P.append T) z)) z :=
      actual_current_lower hn J hJ hmax (P.append T) hT z hz hs
    have hDP : ActualLower (geoTransformAlong J P) (level (geoTransformAlong J P) T z)
        (head T (regimeRun (stepRegime (geoTransformAlong J P) (level (geoTransformAlong J P) T z)) T z))
        (tail T (regimeRun (stepRegime (geoTransformAlong J P) (level (geoTransformAlong J P) T z)) T z)) z :=
      actual_current_lower hn _ hJP hMaxP T hLevelP z hzP hsP
    show Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) _ z=
      Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) _ (lowerMarkedM _) _ z
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ _ _ _ hs,
      Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ _ _ _ hsP]
    rw [hl] at hDP ⊢
    obtain ⟨s,hsdef⟩ : ∃ s,level J (P.append T) z=s := ⟨_,rfl⟩
    have hRegP : stepRegime (geoTransformAlong J P) s T z := ⟨hl.trans hsdef,hsP⟩
    rw [hsdef] at hD hDP ⊢
    rcases (regimeRun_le_length (stepRegime (geoTransformAlong J P) s) T z).lt_or_eq with hlt | heq
    · have hr := regimeRun_append_of_lt _ _ P
        (fun H => IsGeoTestTower (barMarked J) (P.append H)) hG (hQ s) T z hBar hlt
      rw [hr] at hD ⊢
      simp only [head,tail] at hD hDP ⊢
      rw [split_append_of_le P T _ hlt.le] at hD ⊢
      dsimp only at hD ⊢
      have hActual : IsGeoTestTower (barMarked J)
          ((P.append (head T (regimeRun (stepRegime (geoTransformAlong J P) s) T z))).append
            (tail T (regimeRun (stepRegime (geoTransformAlong J P) s) T z))) := by
        rw [BlowupTower.append_assoc,head_append_tail];exact hBar
      have hzActual : z∈(geoTransformAlong (barMarked J)
          ((P.append (head T (regimeRun (stepRegime (geoTransformAlong J P) s) T z))).append
            (tail T (regimeRun (stepRegime (geoTransformAlong J P) s) T z)))).cosupp := by
        rw [BlowupTower.append_assoc,head_append_tail];exact hzBar
      congr 2
      rcases s with _ | s
      · obtain ⟨hDom,hTest,hp,_hCos⟩ := hD
        obtain ⟨hDomP,hTestP,hpP,_hCosP⟩ := hDP
        exact zero_lower_value_empty_prefix_head hn k J hJ.isWellFormed hJ.one_le_d P hP _ _
          hActual z hzActual hDom hTest hDomP hTestP hp hpP
      · exact positive_lower_value_empty_prefix_head hn (k+1) J hJ.isWellFormed hJ.one_le_d P hP _
          ((isGeoTestTower_append_iff _ _ _).mp hActual).1 _ s z
    · have hr := run_crossing_empty_prefix J hJ.isWellFormed hJ.one_le_d P hP T hBar s z hRegP heq
      rw [hr,heq]
      simp only [head,tail]
      rw [split_of_length_le (P.append T) _ le_rfl,split_of_length_le T _ le_rfl]
      dsimp only
      congr 2
      rcases s with _ | s
      · exact zero_base_values_of_level_cut_empty_prefix hn k J hJ hmax P hP T hT z hz hs hsdef heq
      · exact positive_base_values_of_level_cut_empty_prefix hn k s J hJ hmax P hP T hT z hz hs hsdef heq

/-- Actual append admissibility and ENTIRE-value equality construct every
source whole-centre cut; source cut or CAN is not an input. -/
theorem step_one_cut_tail_empty_prefix (hn : 0<n) (k : ℕ)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsStepOneCutTower hn (k+1) J (P.append T)) :
    IsStepOneCutTower hn (k+1) (geoTransformAlong J P) T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hPrev : IsStepOneCutTower hn (k+1) J (P.append T) := hT.1
    have hLevel := stepOneCutTower_levelCut hn J (P.append T) hPrev
    refine ⟨ih hPrev,?_,?_⟩
    · simpa only [geoTransformAlong_append] using hT.2.1
    · intro y hy c hc
      have hyOld : y∈(geoTransformAlong J (P.append T)).cosupp := by
        simpa only [geoTransformAlong_append] using hy
      have hcOld : c∈(geoTransformAlong J (P.append T)).cosupp := hT.2.1.2.1 hc
      rw [←step_one_values_empty_prefix hn k J hJ hmax P hP T hLevel y hyOld,
        ←step_one_values_empty_prefix hn k J hJ hmax P hP T hLevel c hcOld]
      exact hT.2.2 y hyOld c hc

end
end Hironaka.HironakaOriginalBoundTwoStepOneEmptyPrefix
