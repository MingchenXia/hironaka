import Hironaka.Resolution.HironakaG8CaseNTwoSided

/-!
# Case N: equality of every original cosupport threshold

This is the non-tangent input used in the order case split. No claim is made
here about the tangent case or the general residual successor.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseN
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  DivisorExponentAlong GermIdealOrder HironakaG8LocalHistory
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)

/-- Case N: on the two natural order-two non-tangency hypotheses, the
original cosupport thresholds agree for every integer. -/
theorem cosupport_iff_of_notTangent
    {n : ℕ} {X : CMfd.{u} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x)
    (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hNot : ∀ H ∈ P.E, x ∈ H →
      x ∉ cosupport n P.N (vanishingIdeal (n := n) H) 2 ∧
      x ∉ cosupport n Q.N (vanishingIdeal (n := n) H) 2) :
    ∀ e, x ∈ cosupport n P.N P.ideal e ↔ x ∈ cosupport n Q.N Q.ideal e := by
  have hxQc : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  have hNotP : ∀ H ∈ P.E, x ∈ H →
      x ∉ cosupport n P.N (vanishingIdeal (n := n) H) 2 :=
    fun H hH hxH => (hNot H hH hxH).1
  have hNotQ : ∀ H ∈ Q.E, x ∈ H →
      x ∉ cosupport n Q.N (vanishingIdeal (n := n) H) 2 := by
    intro H hH hxH
    exact (hNot H (h.E_eq ▸ hH) hxH).2
  have hOrder := HironakaG8CaseNTwoSided.ordinaryTraceOrder_eq_of_original_local_equiv_notTangent
    P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hNotP hNotQ
  intro e
  rw [HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
      hNP hIP (P.cosupp_subset_N hx) hxP e,
    HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
      hNQ hIQ (Q.cosupp_subset_N hxQc) hxQ e, hOrder]

end
end Hironaka.HironakaG8CaseN
