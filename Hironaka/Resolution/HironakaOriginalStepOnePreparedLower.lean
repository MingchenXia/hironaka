/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStepOneInheritedLowerCut

/-! The original member/contact lower CAN history receives an ACTUAL next
TEST and entire lower cut before recursive preparation is invoked. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOnePreparedLower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  HironakaOriginalFrozenRecursiveLower HironakaOriginalPositiveStepOneCutLowerTest
  HironakaOriginalStepOneInheritedLowerCut InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

theorem original_stepone_cut_frozen_lower_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ c ∈ C,Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    IsGeoTestTower (lowerAt M T y)
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) := by
  let F : ℕ → Prop := fun ℓ =>
    let r := regimeRun (stepRegime M ℓ) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M ℓ H (S.proj y)
    IsGeoTestTower (lowerMarkedM M ℓ H (S.proj y)) (restrict W (.step S C π hπ))
  change F (level M T y)
  by_cases hZero : level M T y=0
  · have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
      (k := k+1) (invFamily hn k) M hM hmax hn T hcan
    have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by rwa [hb.2.2]
    have hHead := (stepRegime_and_mem_cosupp_head M hM.isWellFormed T hb.1 hyBar hns).2
    rw [hZero] at hHead
    have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBarNext : IsGeoTestTower (barMarked M) (.step T C π hπ) :=
      (he.2 (.step T C π hπ)).1.mpr ⟨hb.2.1,hC⟩
    let r := regimeRun (stepRegime M 0) T y
    have hWhole : (head T r).append (.step (tail T r) C π hπ)=.step T C π hπ := by
      rw [BlowupTower.append_step,head_append_tail]
    have hLower := StepOneCompare.isGeoTestTower_cosupp_lowerMarkedB M hM.isWellFormed
      hM.one_le_d hmax (head T r) (.step (tail T r) C π hπ)
      (by rw [hWhole];exact hBarNext) hHead
    have hF : F 0 := hLower.1
    exact (congrArg F hZero).mpr hF
  · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hZero
    have hF : F (s+1) := (original_positive_stepone_cut_lower_test hn M hM hmax T hcan
      y hy hns s hs C hC π hπ hCut).2.1
    exact (congrArg F hs).mpr hF

theorem original_stepone_cut_prepared_lower_data (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    let J := lowerAt M T y
    let R := lowerTailAt M T y
    let RNext := restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)
    IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) R ∧
      IsGeoTestTower J RNext ∧ IsInvDomain k (geoTransformAlong J RNext) ∧
        (Subtype.val : patchAt M T y → Y) ⁻¹' C ⊆
          maxLocus ((invFamily hn k).inv J R) (geoTransformAlong J R).cosupp := by
  have hOld := actual_lower_domain_and_cosupport_dictionary hn M hM hmax T hcan y hy hns
  have hNext := original_stepone_cut_frozen_lower_test hn M hM hmax T hcan y hy hns C hC π hπ
    (hCuts y hy)
  have hLowerCut := original_stepone_cut_inherited_lower_values hn M hM hmax T hcan y hy hns
    C hC hCuts
  exact ⟨hOld.2.1,hOld.2.2.1,hNext,isInvDomain_geoTransformAlong hOld.2.1 _ hNext,hLowerCut⟩

end
end Hironaka.HironakaOriginalStepOnePreparedLower
