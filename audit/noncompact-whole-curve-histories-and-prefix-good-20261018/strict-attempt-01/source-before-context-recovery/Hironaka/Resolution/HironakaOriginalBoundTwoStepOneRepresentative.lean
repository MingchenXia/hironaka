/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalRelativeIdealLevelCut
import Hironaka.Resolution.HironakaOriginalZeroContactRepresentative
import Hironaka.Resolution.HironakaOriginalFiniteStepOneCutMaskAvoidance
/-! Genuine source relative-ideal geometry internally supplies DOMAIN/maximal
order and all lower TESTs before whole original StepOne values and cuts. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoStepOneRepresentative
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal InvDomainRebase
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneValueMasked StepOneLowerDomain
  StepOneRegime StepOneRepresentative CanonicalCentres HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
  HironakaOriginalRelativeIdealLevelCut HironakaOriginalZeroContactRepresentative
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X B Y Z : CMfd.{u} n}

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

/-- Only original relative-ideal geometry supplies all second-reference
lower domains/tests before the unchanged ENTIRE original StepOne value. -/
theorem step_one_values_of_restrictEquiv (hn : 0<n) (k : ℕ)
    (J N : MarkedIdeal n X) (hJ : IsInvDomain 2 J) (hN : N.ideal.IsCoherent)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d) (hEq : RestrictEquiv J N)
    (T : BlowupTower X Y) (hT : IsLevelCutTower J T) (z : Y)
    (hz : z∈(geoTransformAlong J T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) N T z := by
  have hDomN := isInvDomain_of_restrictEquiv hJ hEq hN
  have hMaxN := actual_maximal_order J N hEq hmax
  have hLevelN := level_cut_of_restrictEquiv J N hJ.isWellFormed hN hEq T hT
  have hWhole := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
    hEq hJ.isWellFormed.isClosedSubmanifold_N.1 hJ.isWellFormed.isCoherent hN T
  have hzN : z∈(geoTransformAlong N T).cosupp := by rw [←hWhole.1];exact hz
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar := (he.2 T).1.mpr (levelCutTower_geoTest J T hT)
  have hzBar : z∈(geoTransformAlong (barMarked J) T).cosupp := by rw [(he.2 T).2 hBar];exact hz
  have hFacts := restrictEquiv_facts hJ.isWellFormed hN hEq T
  obtain ⟨hl,hs,_hr⟩ := hFacts.2.2.2 z
  by_cases hsp : IsSpecial J T z
  · show Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) T z=
      Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) N (lowerMarkedM N) T z
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ _ _ _ hsp,
      Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ _ _ _ (hs.mp hsp),hl]
  · have hspN : ¬IsSpecial N T z := fun h => hsp (hs.mpr h)
    have hD : ActualLower J (level J T z)
        (head T (regimeRun (stepRegime J (level J T z)) T z))
        (tail T (regimeRun (stepRegime J (level J T z)) T z)) z :=
      actual_current_lower hn J hJ hmax T hT z hz hsp
    have hDN : ActualLower N (level N T z)
        (head T (regimeRun (stepRegime N (level N T z)) T z))
        (tail T (regimeRun (stepRegime N (level N T z)) T z)) z :=
      actual_current_lower hn N hDomN hMaxN T hLevelN z hzN hspN
    show Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) T z=
      Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) N (lowerMarkedM N) T z
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ _ _ _ hsp,
      Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ _ _ _ hspN]
    rw [←hl] at hDN ⊢
    obtain ⟨s,hsdef⟩ : ∃ s,level J T z=s := ⟨_,rfl⟩
    rw [hsdef] at hD hDN ⊢
    have hRun := regimeRun_congr (stepRegime J s) (stepRegime N s)
      (fun H y => ((restrictEquiv_facts hJ.isWellFormed hN hEq H).2.2.2 y).2.2 s) T z
    rw [hRun] at hD ⊢
    have hActual : IsGeoTestTower (barMarked J)
        ((head T (regimeRun (stepRegime N s) T z)).append (tail T (regimeRun (stepRegime N s) T z))) := by
      rw [head_append_tail];exact hBar
    have hzActual : z∈(geoTransformAlong (barMarked J)
        ((head T (regimeRun (stepRegime N s) T z)).append (tail T (regimeRun (stepRegime N s) T z)))).cosupp := by
      rw [head_append_tail];exact hzBar
    congr 2
    rcases s with _ | s
    · obtain ⟨hDom,hTest,hp,_hCos⟩ := hD
      obtain ⟨hDom',hTest',hp',_hCos'⟩ := hDN
      exact zero_lower_values_of_restrictEquiv hn k J N hJ.isWellFormed hN hJ.one_le_d hEq _ _
        hActual z hzActual hDom hTest hDom' hTest' hp hp'
    · exact positive_lower_values_of_restrictEquiv hn (k+1) s J N hJ.isWellFormed hN hEq _
        ((isGeoTestTower_append_iff _ _ _).mp hActual).1 _ z

/-- Genuine actual admissibility transfers separately from the ENTIRE
numeric equality used on both points of every original whole-centre cut. -/
theorem step_one_cut_of_restrictEquiv (hn : 0<n) (k : ℕ)
    (J N : MarkedIdeal n X) (hJ : IsInvDomain 2 J) (hN : N.ideal.IsCoherent)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d) (hEq : RestrictEquiv J N)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn (k+1) J T) :
    IsStepOneCutTower hn (k+1) N T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hPrev : IsStepOneCutTower hn (k+1) J T := hT.1
    have hLevel := stepOneCutTower_levelCut hn J T hPrev
    have hWhole := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
      hEq hJ.isWellFormed.isClosedSubmanifold_N.1 hJ.isWellFormed.isCoherent hN T
    refine ⟨ih hPrev,(hWhole.2 C).mp hT.2.1,?_⟩
    intro y hy c hc
    have hyOld : y∈(geoTransformAlong J T).cosupp := by rw [hWhole.1];exact hy
    have hcOld : c∈(geoTransformAlong J T).cosupp := hT.2.1.2.1 hc
    rw [←step_one_values_of_restrictEquiv hn k J N hJ hN hmax hEq T hLevel y hyOld,
      ←step_one_values_of_restrictEquiv hn k J N hJ hN hmax hEq T hLevel c hcOld]
    exact hT.2.2 y hyOld c hc

end
end Hironaka.HironakaOriginalBoundTwoStepOneRepresentative
