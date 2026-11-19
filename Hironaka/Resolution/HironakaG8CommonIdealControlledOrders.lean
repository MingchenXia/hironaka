import Hironaka.Resolution.HironakaSharpActualControlledAccumulatedResidual
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.NonmonomialOrderLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8CommonIdealControlledOrders
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder RelativePrincipalizationSpan IdealWeightPowers
  BlowupControlledTransform BlowupExceptionalDivisor RestrictLeCalculus
  NonmonomialOrderLocal NonmonomialTransformAlong
  HironakaSharpActualControlledAccumulatedResidual HironakaSharpActualChronologicalStrictStep
  CanonicalCentres DivisorExponentAlong

set_option maxHeartbeats 950000 in
/-- With the same coherent whole ideal and a common test center, the
difference between two controlled marks is exactly the corresponding
power of the actual exceptional ideal. -/
theorem common_ideal_controlled_marks {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hN : P.N = univ) (hP : P.ideal.IsCoherent)
    {q : ℕ} (hq : P.d ≤ q) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π)
    (hHigh : ({P with d := q}).IsAdmissibleCentre C) :
    let L := (exceptionalDivisor hπ).ideal
    let Q := {P with d := q}
    (P.geoTransform C π).ideal = (idealPow L (q - P.d)).mul (Q.geoTransform C π).ideal := by
  intro L Q
  have hUpper : P.ideal.Le (idealPow (vanishingIdeal (n := n) C) q) :=
    HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hP hHigh.1 (by simpa [MarkedIdeal.cosupp, hN] using hHigh.2.1)
  have hCoL : L.IsCoherent := DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible
  have hCoQ := isCoherent_controlledTransform hπ hP hUpper
  have hCo := IdealWeightPowers.isCoherent_mul
    (GermIdealPullbackCalculus.isCoherent_idealPow hCoL (q - P.d)) hCoQ
  rw [geoTransform_ideal_eq_controlledTransform (𝔪 := P) hN hP hπ,
    geoTransform_ideal_eq_controlledTransform (𝔪 := Q) hN hP hπ]
  symm
  apply eq_controlledTransform_of_eq_mul hπ hCo
  rw [pullback_eq_mul_controlledTransform hπ hP hUpper]
  have hSum : P.d + (q - P.d) = q := Nat.add_sub_of_le hq
  rw [← GermIdealTotalTransform.mul_assoc (GermIdealPullbackCalculus.isCoherent_idealPow hCoL _)
    (GermIdealPullbackCalculus.isCoherent_idealPow hCoL _) hCoQ, ← idealPow_add hCoL, hSum]

set_option maxHeartbeats 1700000 in
/-- At a genuine common next step of two actual marks on the same
whole relatively principal record, removal of the full stage boundary
recovers the same strict residual. This applies at an advancing prefix
with inherited boundary provided no old slot divides the common current
ideal. In particular both first orders agree on every surviving high
cosupport point of that step. -/
theorem common_principal_ideal_next_nonmonomial_order {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : P.IsWellFormed)
    (hN : P.N = univ)
    (hnz : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    (hPrincipal : ∀ x ∈ P.N, ∃ f : X → ℂ, HolomorphicAt n f x ∧
      ∀ g, P.ideal.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) P.N (· = f) x g)
    (hNoOld : ∀ x ∈ P.N, ∀ i : Fin P.E.length, x ∈ P.E.get i →
      ∃ g, P.ideal.mem x g ∧
        ¬ IsInSpanOnAt (n := n) P.N ((vanishingIdeal (n := n) (P.E.get i)).mem x) x g)
    {q : ℕ} (hq : P.d ≤ q) {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hLow : P.IsAdmissibleCentre C) (hHigh : ({P with d := q}).IsAdmissibleCentre C) :
    let Q := {P with d := q}
    let A := P.geoTransform C π
    let B := Q.geoTransform C π
    A.N = B.N ∧ A.E = B.E ∧
    A.ideal = (idealPow (exceptionalDivisor hπ).ideal (q - P.d)).mul B.ideal ∧
    A.cosupp ⊇ B.cosupp ∧ nmPart A = nmPart B ∧
    (∀ z : Y, nmOrd A z = nmOrd B z) := by
  intro Q A B
  have hQ : Q.IsWellFormed := ⟨hP.1, hP.2, hP.3, hP.4⟩
  have hResA : nmPart A = nextRelativeStrict P.N P.ideal C π :=
    controlled_all_accumulated_nonmonomial_eq_nextStrict hn P hP hnz hPrincipal hLow hπ hNoOld
  have hResB : nmPart B = nextRelativeStrict P.N P.ideal C π :=
    controlled_all_accumulated_nonmonomial_eq_nextStrict hn Q hQ hnz hPrincipal hHigh hπ hNoOld
  have hFAC : A.ideal = (idealPow (exceptionalDivisor hπ).ideal (q - P.d)).mul B.ideal :=
    common_ideal_controlled_marks P hN hP.isCoherent hq hπ hHigh
  have hBW := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hQ hHigh hπ
  have hHolL : ∀ x f, (idealPow (exceptionalDivisor hπ).ideal (q - P.d)).mem x f → HolomorphicAt n f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem
      (GermIdealPullbackCalculus.isCoherent_idealPow
        (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) _) hf
  have hAB : A.ideal.Le B.ideal := by
    rw [hFAC]
    exact GermIdealPullbackCalculus.mul_le_right (fun {x g} => hHolL x g) hBW.isCoherent
  have hCos : B.cosupp ⊆ A.cosupp := by
    intro z hz
    have hz' := cosupport_anti hq hz
    exact DerivativeIdealTower.cosupport_subset_of_le hAB P.d hz'
  have hNM := hResA.trans hResB.symm
  refine ⟨rfl, rfl, hFAC, hCos, hNM, fun z => nmOrd_congr fun j => ?_⟩
  change z ∈ cosupport n A.N (nmPart A) j ↔ z ∈ cosupport n A.N (nmPart B) j
  rw [hNM]

end
end Hironaka.HironakaG8CommonIdealControlledOrders
