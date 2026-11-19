import Hironaka.Resolution.HironakaG8CommonIdealControlledOrders
import Hironaka.Resolution.HironakaSharpActualMonomialDivisionResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8CommonIdealInheritedOrders
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers BlowupExceptionalDivisor NonmonomialOrderLocal
  NonmonomialTransformAlong CanonicalCentres DivisorExponentAlong RelativePrincipalizationSpan
  HironakaG8CommonIdealControlledOrders HironakaSharpActualMonomialDivisionResidual

set_option maxHeartbeats 1200000 in
/-- For one whole ideal at two admissible marks, both actual controlled
records have the same nonmonomial ideal and order at the next step. The
full ordered boundary, including all inherited slots, is used on both sides. -/
theorem common_ideal_next_nonmonomial_order_with_inherited_boundary
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : P.IsWellFormed)
    (hnz : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    {q : ℕ} {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hLow : P.IsAdmissibleCentre C) (hHigh : ({P with d := q}).IsAdmissibleCentre C) :
    let A := P.geoTransform C π
    let B := ({P with d := q}).geoTransform C π
    A.N = B.N ∧ A.E = B.E ∧ nmPart A = nmPart B ∧
      (∀ z : Y, nmOrd A z = nmOrd B z) := by
  intro A B
  let Q : MarkedIdeal n X := {P with d := q}
  have hQ : Q.IsWellFormed := ⟨hP.1, hP.2, hP.3, hP.4⟩
  have ha := actual_geoTransform_nonmonomial_eq_total hn P hP hnz hLow hπ
  have hb := actual_geoTransform_nonmonomial_eq_total hn Q hQ hnz hHigh hπ
  have he : nmPart A = nmPart B := ha.trans hb.symm
  refine ⟨rfl, rfl, he, fun z => nmOrd_congr fun j => ?_⟩
  change z ∈ cosupport n A.N (nmPart A) j ↔ z ∈ cosupport n A.N (nmPart B) j
  rw [he]

set_option maxHeartbeats 1200000 in
/-- For ordered marks on an ambient whole record, the higher raw
cosupport survives inside the lower one, with equal nonmonomial order. -/
theorem common_ideal_next_high_cosupport_order_with_inherited_boundary
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : P.IsWellFormed) (hN : P.N = univ)
    (hnz : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    {q : ℕ} (hq : P.d ≤ q) {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hLow : P.IsAdmissibleCentre C) (hHigh : ({P with d := q}).IsAdmissibleCentre C) :
    let A := P.geoTransform C π
    let B := ({P with d := q}).geoTransform C π
    A.ideal = (idealPow (exceptionalDivisor hπ).ideal (q - P.d)).mul B.ideal ∧
    B.cosupp ⊆ A.cosupp ∧ (∀ z ∈ B.cosupp, nmOrd A z = nmOrd B z) := by
  intro A B
  let Q : MarkedIdeal n X := {P with d := q}
  have hQ : Q.IsWellFormed := ⟨hP.1, hP.2, hP.3, hP.4⟩
  have hFAC : A.ideal = (idealPow (exceptionalDivisor hπ).ideal (q - P.d)).mul B.ideal :=
    common_ideal_controlled_marks P hN hP.isCoherent hq hπ hHigh
  have hBW := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hQ hHigh hπ
  have hFactor := GermIdealPullbackCalculus.isCoherent_idealPow
    (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) (q - P.d)
  have hAB : A.ideal.Le B.ideal := by
    rw [hFAC]
    exact GermIdealPullbackCalculus.mul_le_right
      (fun {_ _} hf => GermIdeal.IsCoherent.holomorphicAt_mem hFactor hf) hBW.isCoherent
  refine ⟨hFAC, ?_, fun z _ => ?_⟩
  · intro z hz
    exact DerivativeIdealTower.cosupport_subset_of_le hAB P.d (cosupport_anti hq hz)
  exact (common_ideal_next_nonmonomial_order_with_inherited_boundary hn P hP hnz hπ hLow hHigh).2.2.2 z

end
end Hironaka.HironakaG8CommonIdealInheritedOrders
