/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutSmoothCompanions
import Hironaka.Resolution.HironakaOriginalGivenSmoothStepOneValues
import Hironaka.Resolution.HironakaSmoothSubmersionActualFamilyMonomialLeaf
/-! Whole original FULL values on finite literal noncanonical order cuts
in target DOMAIN two, retaining ANY given smooth Cartesian history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteOrderCutBoundTwoSmoothValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue StepOneRegime NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalFiniteOrderCutSmoothCompanions
  HironakaOriginalGivenSmoothStepOneValues HironakaSmoothSubmersionActualFamilyMonomialLeaf
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X Z : CMfd.{u} n} {A B : CMfd.{u} m}

private theorem domain_at_depth (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (d : ℕ) :
    IsInvDomain (d+2) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

/-- Real current companion TESTs and genuine ANY-TEST StepOne values precede
literal substitution into the unchanged entire original FULL definition. -/
theorem orderCutTower_bound_two_full_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (P : BlowupTower X Z) (hRecipe : IsOrderCutTower M P)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q P g)
    (z : B) (hz : g z∈(geoTransformAlong M P).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+(d+2))).inv (markedPullback (m := m) f M) Q z=
      familyDimensionMap (m-n) (d+2)
        ((invFamily hn (d+2)).inv M P (g z)) := by
  have hP := orderCutTower_geoTest M P hRecipe
  by_cases hZero : nmOrd (geoTransformAlong M P) (g z)=0
  · exact (IsActualTowerPullback.actual_family_monomial_leaf hn hm h M
      (domain_at_depth M hM d) hP z hZero).2
  have hPos : 0<nmOrd (geoTransformAlong M P) (g z) := Nat.pos_of_ne_zero hZero
  obtain ⟨hOrd,hRun,hp,hp',p,q,hRecord,hCart,_hCoord,hPoint,hDom,hMax,hTest,
    _hCurrent,hTargetPoint,_hSourceDom,_hSourceTest,_hSourceCurrent,_hSourcePoint,_hWhole,_hCos,_hHeads⟩ :=
    orderCutTower_current_companion_smooth_diagram hn M hM P hRecipe h z hz hPos
  let o := nmOrd (geoTransformAlong M P) (g z)
  have ho : 0<o := hPos
  let r := regimeRun (OrdRegime M o) P (g z)
  let U := ordMask (geoTransformAlong M (head P r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let J := compAt M o (head P r)
  let J' := compAt (markedPullback (m := m) f M) o (head Q r)
  let R := restrict U (tail P r)
  let R' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  change markedPullback (m := m) p J=J' at hRecord
  change IsActualTowerPullback p R' R q at hCart
  have hTarget : q z'∈(geoTransformAlong J R).cosupp := by
    rw [hPoint]
    exact hTargetPoint
  have hv := (original_given_all_step_one_smooth_values hn hm J hDom hMax R hTest hCart).2 z' hTarget d
  rw [hRecord,hPoint] at hv
  change genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hm ((m-n)+(d+1))) K (Y := B) S w) (markedPullback (m := m) f M) Q z=
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) (d+1)))
      (genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
        (invFamily hn (d+1)) K (Y := B) S w) M P (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hOrd,show nmOrd (geoTransformAlong M P) (g z)=o from rfl,
    if_neg (ne_of_gt ho),hRun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+(d+1))) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+(d+1)))))))) hv

/-- ONLY original input constructs ONE source history before ALL points and depths. -/
theorem exists_orderCutTower_bound_two_smooth_history (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (P : BlowupTower X Z)
    (hRecipe : IsOrderCutTower M P) {f : A → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
    ∃ (B : CMfd.{u} m) (Q : BlowupTower A B) (g : B → Z),
      IsActualTowerPullback f Q P g ∧ IsOrderCutTower (markedPullback (m := m) f M) Q ∧
      IsInvDomain (2+(m-n)) (markedPullback (m := m) f M) ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp=g ⁻¹' (geoTransformAlong M P).cosupp ∧
      ∀ z : B,g z∈(geoTransformAlong M P).cosupp → ∀ d : ℕ,
        (invFamily hm ((m-n)+(d+2))).inv (markedPullback (m := m) f M) Q z=
          familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv M P (g z)) := by
  obtain ⟨B,Q,g,h⟩ := exists_actual_tower hf P
  have hP := orderCutTower_geoTest M P hRecipe
  exact ⟨B,Q,g,h,IsActualTowerPullback.orderCutTower_pullback hn M hM h hRecipe,
    isInvDomain_markedPullback_submersion hf M hM,
    (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hP).1,
    IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hP,
    fun z hz d => orderCutTower_bound_two_full_smooth_values hn hm M hM P hRecipe h z hz d⟩

end
end Hironaka.HironakaOriginalFiniteOrderCutBoundTwoSmoothValues
