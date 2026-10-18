/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.MemberLowerMarkedAdmissibleExact
import Hironaka.Resolution.HironakaOriginalFrozenRecursiveLower
import Hironaka.Invariant.MemberRestrictAdmissible

/-! Actual positive Step One cut admissibility for the SAME old selected lower
record, with lower TEST constructed from original canonical inputs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveStepOneCutLowerTest
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  StepOneCompare MemberRestrictAdmissible HironakaOriginalFrozenRecursiveLower InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

private theorem actual_lower_data_at_level (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬ IsSpecial M T y)
    (ℓ : ℕ) (hℓ : level M T y=ℓ) :
    let r := regimeRun (stepRegime M ℓ) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M ℓ H (S.proj y)
    let J := lowerMarkedM M ℓ H (S.proj y)
    stepRegime M ℓ H (S.proj y) ∧ S.proj y ∈ (geoTransformAlong (barMarked M) H).cosupp ∧
    y ∈ openPreimage S W ∧ IsInvDomain k J ∧
      IsCanonical J ((invFamily hn k).inv J) (restrict W S) ∧
      ∀ p : openPreimage S W,
        p ∈ (geoTransformAlong J (restrict W S)).cosupp ↔
          p.val ∈ (geoTransformAlong M T).cosupp ∧ level M T p.val=ℓ := by
  let P : ℕ → Prop := fun a =>
    let r := regimeRun (stepRegime M a) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M a H (S.proj y)
    let J := lowerMarkedM M a H (S.proj y)
    stepRegime M a H (S.proj y) ∧ S.proj y ∈ (geoTransformAlong (barMarked M) H).cosupp ∧
    y ∈ openPreimage S W ∧ IsInvDomain k J ∧
      IsCanonical J ((invFamily hn k).inv J) (restrict W S) ∧
      ∀ p : openPreimage S W,
        p ∈ (geoTransformAlong J (restrict W S)).cosupp ↔
          p.val ∈ (geoTransformAlong M T).cosupp ∧ level M T p.val=a
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by rwa [hb.2.2]
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed T hb.1 hyBar hns
  have hData : P (level M T y) :=
    ⟨hReg,hHead,actual_lower_domain_and_cosupport_dictionary hn M hM hmax T hcan y hy hns⟩
  exact (congrArg P hℓ).mp hData

theorem original_positive_stepone_cut_lower_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬ IsSpecial M T y)
    (s : ℕ) (hlevel : level M T y=s+1)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ c ∈ C,Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    let r := regimeRun (stepRegime M (s+1)) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M (s+1) H (S.proj y)
    let J := lowerMarked M (s+1) H (S.proj y)
    IsInvDomain k J ∧ IsGeoTestTower J (restrict W (.step S C π hπ)) ∧
      IsInvDomain k (geoTransformAlong J (restrict W (.step S C π hπ))) := by
  let r := regimeRun (stepRegime M (s+1)) T y
  let H := head T r
  let S := tail T r
  let W := lowerMask M (s+1) H (S.proj y)
  let J := lowerMarked M (s+1) H (S.proj y)
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have hData := actual_lower_data_at_level hn M hM hmax T hcan y hy hns (s+1) hlevel
  obtain ⟨hReg,hHead,hp,hJ,hJCan,hCos⟩ := hData
  have hJT : IsGeoTestTower J (restrict W S) :=
    (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hJ _ hJCan
  have hApp : H.append S=T := head_append_tail T r
  have hBarStep : IsGeoTestTower (barMarked M) (.step T C π hπ) := by
    apply ((coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d).2 (.step T C π hπ)).1.mpr
    exact ⟨hb.2.1,hC⟩
  have hH := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hb.1).1
  have hHS : IsGeoTestTower (barMarked M) (H.append (.step S C π hπ)) := by
    simpa only [BlowupTower.append_step,hApp] using hBarStep
  have hTailStep := (isGeoTestTower_append_iff (barMarked M) H (.step S C π hπ)).mp hHS
  have hHeadWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM.isWellFormed) H hH
  have hRestricted := isGeoTestTower_restrict W hHeadWF.isClosedSubmanifold_N
    hHeadWF.isCoherent (.step S C π hπ) hTailStep.2
  have hS := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hb.1).2
  have hAdm := hRestricted.2
  rw [geoTransformAlong_restrict W hHeadWF.isClosedSubmanifold_N hHeadWF.isCoherent S hS,
    ←geoTransformAlong_append,hApp] at hAdm
  have hTrace : (geoTransformAlong J (restrict W S)).IsAdmissibleCentre
      ((Subtype.val : openPreimage S W → Y) ⁻¹' C) := by
    apply (isAdmissibleCentre_lowerMarked_succ_iff M hM.isWellFormed hn H S
      (by rw [hApp];exact hb.1) hp hJT _).mpr
    refine ⟨by rwa [hApp],?_⟩
    intro q hq
    have hGe : s+1≤level M T q := by
      have hv := Prod.Lex.le_iff.mp (hCut q hq)
      rw [Seq.StepOneValueMasked.stepOneInvL_fst,
        Seq.StepOneValueMasked.stepOneInvL_fst] at hv
      rw [hlevel] at hv
      exact hv.elim (fun h => h.le) (fun h => h.1.le)
    have hLe : level M T q≤s+1 := by
      have hh := level_le_of_mem_lowerMask M (fun A hA => hM.isWellFormed.isSNCDivisor.1 A hA)
        H S hReg.1 q.property
      rwa [hApp] at hh
    have hqCos : q ∈ (geoTransformAlong J (restrict W S)).cosupp :=
      (hCos q).mpr ⟨hC.2.1 hq,le_antisymm hLe hGe⟩
    exact ((mem_cosupp_lowerMarked_succ_iff M hM.isWellFormed hn H S
      (by rw [hApp];exact hb.1) hp hJT q).mp hqCos).2
  have hNext : IsGeoTestTower J (restrict W (.step S C π hπ)) := ⟨hJT,hTrace⟩
  exact ⟨hJ,hNext,isInvDomain_geoTransformAlong hJ _ hNext⟩

theorem original_positive_stepone_cut_next_cosupport (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬ IsSpecial M T y)
    (s : ℕ) (hlevel : level M T y=s+1)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ c ∈ C,Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    let r := regimeRun (stepRegime M (s+1)) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M (s+1) H (S.proj y)
    let J := lowerMarked M (s+1) H (S.proj y)
    ∀ z : openPreimage (.step S C π hπ) W,
      z ∈ (geoTransformAlong J (restrict W (.step S C π hπ))).cosupp ↔
        z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp ∧
          level M (.step T C π hπ) z.val=s+1 := by
  let r := regimeRun (stepRegime M (s+1)) T y
  let H := head T r
  let S := tail T r
  let W := lowerMask M (s+1) H (S.proj y)
  have hData := actual_lower_data_at_level hn M hM hmax T hcan y hy hns (s+1) hlevel
  obtain ⟨hReg,hHead,hp,_,_,_⟩ := hData
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have hStep : IsGeoTestTower M (.step T C π hπ) := ⟨hb.2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBarStep := (he.2 (.step T C π hπ)).1.mpr hStep
  have hApp : H.append S=T := head_append_tail T r
  have hWhole : H.append (.step S C π hπ)=.step T C π hπ := by
    rw [BlowupTower.append_step,hApp]
  have hTest := (original_positive_stepone_cut_lower_test hn M hM hmax T hcan y hy hns
    s hlevel C hC π hπ hCut).2.1
  dsimp only
  intro z
  have hDict := mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d hn hmax H
    (.step S C π hπ) (by rw [hWhole];exact hBarStep) hHead hReg.1 hp hTest z
  rw [hWhole,(he.2 (.step T C π hπ)).2 hBarStep] at hDict
  exact hDict
end
end Hironaka.HironakaOriginalPositiveStepOneCutLowerTest
