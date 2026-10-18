/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutBoundTwoSmoothValues
/-! Literal original whole-value cut histories and their actual smooth
pullbacks, without source cuts or canonicality as output certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteFullCutSmoothHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalFiniteOrderCutBoundTwoSmoothValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

/-- Only genuine original admissibility and ordinary entire original FULL cuts. -/
def IsFullCutTower (hn : 0<n) (d : ℕ) (M : MarkedIdeal n X) :
    ∀ {D : CMfd.{u} n},BlowupTower X D → Prop
  | _,.refl => True
  | _,.step T C _ _ => IsFullCutTower hn d M T ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      ∀ y∈(geoTransformAlong M T).cosupp,∀ c∈C,
        (invFamily hn (d+2)).inv M T y≤(invFamily hn (d+2)).inv M T c

/-- Every ordinary entire FULL cut supplies its true first-coordinate cut. -/
theorem fullCutTower_orderCut (hn : 0<n) (d : ℕ) (M : MarkedIdeal n X)
    (T : BlowupTower X D) (hT : IsFullCutTower hn d M T) : IsOrderCutTower M T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    exact orderCutTower_step_of_full_cut hn M T (ih hT.1) C hT.2.1 π hπ hT.2.2

/-- Whole actual source values precede each genuine source full-value cut. -/
theorem IsActualTowerPullback.fullCutTower_pullback (hn : 0<n) (hm : 0<m)
    (d : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (hT : IsFullCutTower hn d M T) :
    IsFullCutTower hm ((m-n)+d) (markedPullback (m := m) f M) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    have hOrder := fullCutTower_orderCut hn d M (.step T C π hπ) hT
    have hTest := orderCutTower_geoTest M (.step T C π hπ) hOrder
    have hSource := (IsActualTowerPullback.relative_marked_dictionary
      (IsActualTowerPullback.step h hg hπ hρ) M hM.isWellFormed hTest).1
    refine ⟨ih hT.1,hSource.2,?_⟩
    intro z hz c hc
    rw [IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hTest.1] at hz
    have hvz := orderCutTower_bound_two_full_smooth_values hn hm M hM T hOrder.1 h z hz d
    have hvc := orderCutTower_bound_two_full_smooth_values hn hm M hM T hOrder.1 h c (hT.2.1.2.1 hc) d
    change (invFamily hm ((m-n)+(d+2))).inv (markedPullback (m := m) f M) Q z≤
      (invFamily hm ((m-n)+(d+2))).inv (markedPullback (m := m) f M) Q c
    rw [hvz,hvc]
    exact (strictMono_familyDimensionMap (m-n) (d+2)).monotone (hT.2.2 (g z) hz (g c) hc)

/-- ONLY original inputs choose ONE real source history before ALL full values. -/
theorem exists_fullCutTower_bound_two_smooth_history (hn : 0<n) (hm : 0<m)
    (d : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X D) (hT : IsFullCutTower hn d M T) {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsFullCutTower hm ((m-n)+d) (markedPullback (m := m) f M) Q ∧
      IsInvDomain (2+(m-n)) (markedPullback (m := m) f M) ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp=g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ z : D',g z∈(geoTransformAlong M T).cosupp → ∀ e : ℕ,
        (invFamily hm ((m-n)+(e+2))).inv (markedPullback (m := m) f M) Q z=
          familyDimensionMap (m-n) (e+2) ((invFamily hn (e+2)).inv M T (g z)) := by
  obtain ⟨D',Q,g,h,hOrder,hDom,hTest,hCos,hValues⟩ :=
    exists_orderCutTower_bound_two_smooth_history hn hm M hM T (fullCutTower_orderCut hn d M T hT) hf
  exact ⟨D',Q,g,h,IsActualTowerPullback.fullCutTower_pullback hn hm d M hM h hT,hDom,hTest,hCos,hValues⟩

end
end Hironaka.HironakaOriginalFiniteFullCutSmoothHistory
