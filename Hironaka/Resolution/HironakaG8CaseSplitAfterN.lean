import Hironaka.Resolution.HironakaG8CaseN
import Hironaka.Resolution.HironakaG8P1ArcDirectrix
import Hironaka.Resolution.HironakaG8ClassStepTangent

/-!
# Pointwise order comparison reduced to the tangent case

The mark case, tangent equivalence and non-tangent case are constructed
from the original hypotheses. The tangent case remains an explicit input.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseSplitAfterN
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  DivisorExponentAlong GermIdealOrder HironakaG8LocalHistory
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaG8ClassStepHistory (OrdAgreeBelowAt)

/-- Under the ordinary source hypotheses, only the explicitly stated tangent
case remains to obtain pointwise order agreement below twice the mark. -/
theorem ordAgreeBelowAt_of_tangent_case
    {n : ℕ} {X : CMfd.{u} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x)
    (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hT : ∀ H ∈ P.E, x ∈ H → x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2 →
      x ∈ cosupport n Q.N (vanishingIdeal (n := n) H) 2 → OrdAgreeBelowAt P Q x) :
    OrdAgreeBelowAt P Q x := by
  have hxQc : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  have hM := HironakaG8P1ArcPair.cosupport_succ_iff P Q h hNP hNQ hIP hIQ hE
    hd1 hd hdim hx hxP hxQ
  apply HironakaG8ClassStepTangent.ordAgreeBelowAt_of_cases hd hx hxQc hM ?_ ?_ hT
  · intro hs H _hH _hxH
    exact HironakaG8P1ArcDirectrix.tangent_member_iff_of_locWPEquiv_order_gt
      P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hs H
  · intro hNot
    exact HironakaG8CaseN.cosupport_iff_of_notTangent
      P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hNot

end
end Hironaka.HironakaG8CaseSplitAfterN
