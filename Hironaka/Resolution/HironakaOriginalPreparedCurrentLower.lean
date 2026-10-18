/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentPositiveLower

/-! Actual original member/contact lower TESTs and current points after
genuine preparation, without next canonicality or lower output certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedCurrentLower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  HironakaOriginalFrozenRecursiveLower HironakaOriginalPreparedCurrentPositiveLower
  InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

theorem current_lower_test_after_cut (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) z) :
    let P := .step T C π hπ
    IsGeoTestTower (lowerAt M P z) (lowerTailAt M P z) := by
  let P : BlowupTower X Z := .step T C π hπ
  let F : ℕ → Prop := fun ℓ =>
    let r := regimeRun (stepRegime M ℓ) P z
    let H := head P r
    let S := tail P r
    let W := lowerMask M ℓ H (S.proj z)
    IsGeoTestTower (lowerMarkedM M ℓ H (S.proj z)) (restrict W S)
  change F (level M P z)
  by_cases hZero : level M P z=0
  · have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
      (k := k+1) (invFamily hn k) M hM hmax hn T hcan
    have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr ⟨hb.2.1,hC⟩
    have hzBar : z ∈ (geoTransformAlong (barMarked M) P).cosupp := by
      rw [(he.2 P).2 hBar]
      exact hz
    have hHead := (stepRegime_and_mem_cosupp_head M hM.isWellFormed P hBar hzBar hns).2
    rw [hZero] at hHead
    let r := regimeRun (stepRegime M 0) P z
    have hAppend : IsGeoTestTower (barMarked M) ((head P r).append (tail P r)) := by
      rw [head_append_tail]
      exact hBar
    have hLower := StepOneCompare.isGeoTestTower_cosupp_lowerMarkedB M hM.isWellFormed
      hM.one_le_d hmax (head P r) (tail P r) hAppend hHead
    have hF : F 0 := hLower.1
    exact (congrArg F hZero).mpr hF
  · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hZero
    have hF : F (s+1) := current_positive_lower_test_after_cut hn M hM hmax T hcan C hC π hπ
      (fun y hy _ _ => hCuts y hy) z hz s
    exact (congrArg F hs).mpr hF

theorem current_lower_data_after_cut (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) z) :
    let P := .step T C π hπ
    let J := lowerAt M P z
    let R := lowerTailAt M P z
    IsInvDomain k J ∧ IsGeoTestTower J R ∧ IsInvDomain k (geoTransformAlong J R) ∧
      ∃ hp : z ∈ patchAt M P z,
        (⟨z,hp⟩ : patchAt M P z) ∈ (geoTransformAlong J R).cosupp ∧
        ∀ p : patchAt M P z,
          p ∈ (geoTransformAlong J R).cosupp ↔
            p.val ∈ (geoTransformAlong M P).cosupp ∧ level M P p.val=level M P z := by
  let P : BlowupTower X Z := .step T C π hπ
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr ⟨hb.2.1,hC⟩
  have hzBar : z ∈ (geoTransformAlong (barMarked M) P).cosupp := by
    rw [(he.2 P).2 hBar]
    exact hz
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed P hBar hzBar hns
  let r := runAt M P z
  have hH := ((isGeoTestTower_iff_head_tail (barMarked M) P r).mp hBar).1
  obtain ⟨hp,hDom⟩ := mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d
    hn hmax hM.dimLE (head P r) hH hHead hReg
  have hJ : IsInvDomain k (lowerAt M P z) := hDom
  have hTest := current_lower_test_after_cut hn M hM hmax T hcan C hC π hπ hCuts z hz hns
  have hDict : ∀ p : patchAt M P z,
      p ∈ (geoTransformAlong (lowerAt M P z) (lowerTailAt M P z)).cosupp ↔
        p.val ∈ (geoTransformAlong M P).cosupp ∧ level M P p.val=level M P z := by
    intro p
    have hd := mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d hn hmax
      (head P r) (tail P r) (by rw [head_append_tail];exact hBar) hHead hReg.1 hp hTest p
    rw [head_append_tail,(he.2 P).2 hBar] at hd
    exact hd
  exact ⟨hJ,hTest,isInvDomain_geoTransformAlong hJ _ hTest,hp,(hDict ⟨z,hp⟩).mpr
    ⟨hz,rfl⟩,hDict⟩

end
end Hironaka.HironakaOriginalPreparedCurrentLower
