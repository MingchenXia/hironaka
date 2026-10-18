/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPositiveStepOneCutLowerTest

/-! Real positive-regime increment/reset constructs the newly computed lower
TEST before its actual current domain, mask and cosupport point are used. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedCurrentPositiveLower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  HironakaOriginalPositiveStepOneCutLowerTest InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

theorem current_positive_lower_test_after_cut (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp, ¬IsSpecial M T y →
      0<level M T y → ∀ c ∈ C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) (s : ℕ) :
    let P := .step T C π hπ
    let r := regimeRun (stepRegime M (s+1)) P z
    let H := head P r
    let S := tail P r
    let W := lowerMask M (s+1) H (S.proj z)
    let J := lowerMarked M (s+1) H (S.proj z)
    IsGeoTestTower J (restrict W S) := by
  dsimp only
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    hM.isWellFormed T hb.2.1
  have hOldPoint : π z ∈ (geoTransformAlong M T).cosupp :=
    proj_mem_cosupp_of_mem_cosupp hWF.isClosedSubmanifold_N hWF.isCoherent
      (.step .refl C π hπ) ⟨trivial,hC⟩ hz
  by_cases hOld : stepRegime M (s+1) T (π z)
  · have hPos : 0<level M T (π z) := by rw [hOld.1]; omega
    have hTest := (original_positive_stepone_cut_lower_test hn M hM hmax T hcan
      (π z) hOldPoint hOld.2 s hOld.1 C hC π hπ
        (hCuts (π z) hOldPoint hOld.2 hPos)).2.1
    rw [regimeRun_step_of (stepRegime M (s+1)) T C π hπ hOld]
    exact hTest
  · rw [regimeRun_step_of_not (stepRegime M (s+1)) T C π hπ hOld]
    trivial

theorem current_positive_lower_data_after_cut (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp, ¬IsSpecial M T y →
      0<level M T y → ∀ c ∈ C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) z) (s : ℕ)
    (hlevel : level M (.step T C π hπ) z=s+1) :
    let P := .step T C π hπ
    let r := regimeRun (stepRegime M (s+1)) P z
    let H := head P r
    let S := tail P r
    let W := lowerMask M (s+1) H (S.proj z)
    let J := lowerMarked M (s+1) H (S.proj z)
    IsInvDomain k J ∧ IsGeoTestTower J (restrict W S) ∧
      IsInvDomain k (geoTransformAlong J (restrict W S)) ∧
      ∃ hp : S.proj z ∈ W,
        (⟨z,hp⟩ : openPreimage S W) ∈ (geoTransformAlong J (restrict W S)).cosupp ∧
        ∀ p : openPreimage S W,
          p ∈ (geoTransformAlong J (restrict W S)).cosupp ↔
            p.val ∈ (geoTransformAlong M P).cosupp ∧ level M P p.val=s+1 := by
  let P : BlowupTower X Z := .step T C π hπ
  let r := regimeRun (stepRegime M (s+1)) P z
  let H := head P r
  let S := tail P r
  let W := lowerMask M (s+1) H (S.proj z)
  let J := lowerMarked M (s+1) H (S.proj z)
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have hP : IsGeoTestTower M P := ⟨hb.2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hzBar : z ∈ (geoTransformAlong (barMarked M) P).cosupp := by
    rw [(he.2 P).2 hBar]
    exact hz
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed P hBar hzBar hns
  change level M P z=s+1 at hlevel
  rw [hlevel] at hReg hHead
  have hH := ((isGeoTestTower_iff_head_tail (barMarked M) P r).mp hBar).1
  obtain ⟨hp,hDom⟩ := mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d
    hn hmax hM.dimLE H hH hHead hReg
  have hJ : IsInvDomain k J := hDom
  have hTest := current_positive_lower_test_after_cut hn M hM hmax T hcan C hC π hπ hCuts z hz s
  have hWhole : H.append S=P := head_append_tail P r
  have hDict : ∀ p : openPreimage S W,
      p ∈ (geoTransformAlong J (restrict W S)).cosupp ↔
        p.val ∈ (geoTransformAlong M P).cosupp ∧ level M P p.val=s+1 := by
    intro p
    have hd := mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d hn hmax H S
      (by rw [hWhole]; exact hBar) hHead hReg.1 hp hTest p
    rw [hWhole,(he.2 P).2 hBar] at hd
    exact hd
  exact ⟨hJ,hTest,isInvDomain_geoTransformAlong hJ _ hTest,hp,(hDict ⟨z,hp⟩).mpr
    ⟨hz,hlevel⟩,hDict⟩

end
end Hironaka.HironakaOriginalPreparedCurrentPositiveLower
