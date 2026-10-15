/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalActualSmoothZeroMaskHistories
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalCurveFamily
/-! Genuine original dimension-one Step One values on EVERY ORIGINAL TEST.
Actual masked geometry proves the special leaf without lower canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAnyTestCurveStepOneValue
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain StepOneRegime
  StepOneValueMasked HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

/-- The ACTUAL current lower domain is zero-dimensional and its REFLEXIVE
cosupport gives a contradiction to any nonspecial original cosupport point. -/
theorem original_curve_step_one_special_of_test (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    (y : D) (hy : y ∈ (geoTransformAlong M T).cosupp) : IsSpecial M T y := by
  by_contra hns
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar]; exact hy
  have hReg : stepRegime M (level M T y) T y := ⟨rfl,hns⟩
  obtain ⟨hp,hJ⟩ := StepOneValueMasked.mem_lowerMask_and_isInvDomain_M M hM.isWellFormed
    hM.one_le_d hn hmax hM.dimLE T hBar hyBar hReg
  let U := lowerMask M (level M T y) T y
  let J := lowerMarkedM M (level M T y) T y
  change IsInvDomain 0 J at hJ
  have hCos := StepOneCanonicalTail.mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d
    hn hmax T .refl hBar hyBar rfl hp trivial (⟨y,hp⟩ : openPreimage .refl U)
  have hPoint : (⟨y,hp⟩ : U) ∈ J.cosupp := hCos.mpr ⟨hyBar,rfl⟩
  have hEmpty : J.cosupp=∅ := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero
    (X := CMfd.of (n := n) U) hJ (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) trivial
  rw [hEmpty] at hPoint
  exact hPoint

/-- The unchanged ACTUAL original Step One definition evaluates in its
proved special branch on every original dimension-one maximal-order TEST. -/
theorem original_curve_step_one_value_of_test (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    (y : D) (hy : y ∈ (geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) M T y=toLex (level M T y,⊤) := by
  have hs := original_curve_step_one_special_of_test hn M hM hmax T hT y hy
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hs]

/-- Real smooth special/level dictionaries precede actual value evaluation.
No canonicality or lower invariant comparison is assumed. -/
theorem actual_smooth_curve_step_one_value_of_test (hn : 0<n) (hm : 0<m)
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hT : IsGeoTestTower M T) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm (m-n)) (markedPullback (m := m) f M) Q z=
      stepDimensionMap (familyDimensionMap (m-n) 0)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) M T (g z)) := by
  have hs := original_curve_step_one_special_of_test hn M hM hmax T hT (g z) hy
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hsSource := (IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mpr hs
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hsSource,if_pos hs,IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_top]

/-- ONLY original smooth inputs internally produce the actual source original
TEST before every actual point's genuine original Step One value comparison. -/
theorem exists_original_smooth_curve_step_one_value_of_test
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm (m-n)) (markedPullback (m := m) f M) Q z=
          stepDimensionMap (familyDimensionMap (m-n) 0)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) M T (g z)) := by
  obtain ⟨D',Q,g,hCart,_hg,_hLen,_hSquare,hQ,_hCurrent,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  exact ⟨D',Q,g,hCart,hQ,fun z hz => actual_smooth_curve_step_one_value_of_test hn hm hCart M hM hmax hT z hz⟩

end
end Hironaka.HironakaOriginalAnyTestCurveStepOneValue
