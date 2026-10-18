/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStepOnePreparedLower
import Hironaka.Resolution.HironakaOriginalPreparedGeneralSmoothValues
/-! Genuine upper StepOne cuts internally supply the precise actual lower
preparation before the first higher lower-carrier FULL-value comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOnePreparedLowerFullValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  HironakaOriginalFrozenRecursiveLower HironakaOriginalStepOnePreparedLower
  HironakaOriginalPreparedGeneralSmoothValues BlowupRestrictOpen
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X Y Z : CMfd.{u} n} {A B : CMfd.{u} m}

/-- Actual lower step admissibility and its ENTIRE FULL cut are outputs of
the genuine original upper StepOne preparation, for every selected level. -/
theorem original_stepone_cut_actual_lower_preparation (hn : 0<n)
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
    let C' := (Subtype.val : patchAt M T y → Y) ⁻¹' C
    IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) R ∧
      (geoTransformAlong J R).IsAdmissibleCentre C' ∧
      ∀ p ∈ (geoTransformAlong J R).cosupp,∀ c ∈ C',
        (invFamily hn k).inv J R p≤(invFamily hn k).inv J R c := by
  have hData := original_stepone_cut_prepared_lower_data hn M hM hmax T hcan
    y hy hns C hC π hπ hCuts
  refine ⟨hData.1,hData.2.1,hData.2.2.1.2,?_⟩
  intro p hp c hc
  exact (hData.2.2.2.2 hc).2 p hp

/-- Upper DOMAIN3 inputs construct lower DOMAIN2, OLD CAN, the actual
restricted centre and its full cut BEFORE the SAME lower Cartesian history
is used in the genuine prepared FULL-value comparison. -/
theorem original_stepone_bound_three_prepared_lower_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    {f : A → maskAt M T y}
    {g : B → openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)}
    {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) g)
    (z : B) (hz : g z ∈ (geoTransformAlong (lowerAt M T y)
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ))).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f (lowerAt M T y)) Q z=
      familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv (lowerAt M T y)
        (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) (g z)) := by
  have hData := original_stepone_cut_actual_lower_preparation (k := 2) hn M hM hmax T hcan
    y hy hns C hC π hπ hCuts
  let J := lowerAt M T y
  let R := lowerTailAt M T y
  let V := patchAt M T y
  let C' : Set V := (Subtype.val : V → Y) ⁻¹' C
  let W := openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)
  let π' : W → V := fun w => ⟨π w.val,w.property⟩
  have hπ' : IsBlowupAlong n C' π' :=
    isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
  exact prepared_original_general_smooth_values
    (X := CMfd.of (n := n) (maskAt M T y)) (D := CMfd.of (n := n) V)
    (Z := CMfd.of (n := n) W) hn hm J hData.1 R hData.2.1 C' hData.2.2.1
    π' hπ' (fun p hp _ => hData.2.2.2 p hp) h z hz d

end
end Hironaka.HironakaOriginalStepOnePreparedLowerFullValues
