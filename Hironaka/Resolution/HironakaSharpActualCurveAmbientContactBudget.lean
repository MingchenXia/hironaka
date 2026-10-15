/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMixedCurveContactEvolution

/-! Literal TRUE original ambient-contact orders give a genuine natural
budget drop at actual tau_D points. No selected-centre or driver certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveAmbientContactBudget
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualMixedCurveContactEvolution HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder RestrictedIdealExtension
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HomogenizedGlueingTower
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Sum of ACTUAL normalized AMBIENT strict trace orders over ORIGINAL positions. -/
def actualAmbientContactBudget (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (x : Y) : ℕ :=
  ∑ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
    (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
      (vanishingIdeal (n := n) (strictAlong T (E.get i)))) x

/-- True ORIGINAL member incidence positions, with no quotienting or reindexing. -/
def actualAmbientIncidentPositions (E : List (Set X)) (T : BlowupTower X Y) (x : Y) : Finset (Fin E.length) :=
  Finset.univ.filter fun i => x ∈ strictAlong T (E.get i)

/-- Genuine original-input member recurrence BEFORE exact whole-family sum. -/
theorem original_curve_actual_contact_budget_evolution (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {C : Set Y} (hC : (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : z ∈ (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N)
    (hzC : π z ∈ C) :
    actualAmbientContactBudget W E (.step T C π hπ) z+
      (actualAmbientIncidentPositions E T (π z)).card=actualAmbientContactBudget W E T (π z) := by
  have hi : ∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N
        (restrictOn n (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N
          (vanishingIdeal (n := n) (strictAlong (.step T C π hπ) (E.get i)))) z+
        (if π z ∈ strictAlong T (E.get i) then 1 else 0)=
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
            (vanishingIdeal (n := n) (strictAlong T (E.get i)))) (π z) := by
    intro i
    exact (original_curve_next_member_contact_and_exponent_evolution hn hW hE hdense hr T hT hC hπ i z hz hzC).1
  have hSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin E.length))) rfl (fun i _ => hi i)
  rw [Finset.sum_add_distrib] at hSum
  change actualAmbientContactBudget W E (.step T C π hπ) z+
    (∑ i : Fin E.length,if π z ∈ strictAlong T (E.get i) then 1 else 0)=
      actualAmbientContactBudget W E T (π z) at hSum
  simpa only [actualAmbientIncidentPositions,Finset.card_filter] using hSum

/-- Positive actual original-member incidence is internally proved from the
literal tau_D support before the genuine NATURAL budget drop is derived. -/
theorem original_curve_contact_budget_strict_drop_above_actual_difference (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {C : Set Y} (hC : (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : z ∈ (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N)
    (hzC : π z ∈ C) (hzD : π z ∈ actualAmbientExceptionalDifference W E T) :
    actualAmbientContactBudget W E (.step T C π hπ) z<actualAmbientContactBudget W E T (π z) := by
  have hEq := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT
  have hxD := hEq ▸ hzD
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxD.2
  have hPos : 0 < (actualAmbientIncidentPositions E T (π z)).card :=
    Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  have hBudget := original_curve_actual_contact_budget_evolution hn hW hE hdense hr T hT hC hπ hz hzC
  omega

end
end Hironaka.HironakaSharpActualCurveAmbientContactBudget
