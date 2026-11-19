import Hironaka.Resolution.HironakaG8CaseTAmbientComparison
import Hironaka.Resolution.HironakaG8CaseSplitAfterN

/-!
# Pointwise order agreement for transverse ambient carriers

The proved non-tangent case, directrix comparison and tangent-frame argument
combine under the actual codimension-one ambient-carrier hypotheses.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTAmbientOrder
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  DivisorExponentAlong GermIdealOrder HironakaG8LocalHistory
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaG8ClassStepHistory (OrdAgreeBelowAt)

/-- The original order comparison holds at the point when both carriers are
hypersurfaces inside ambient carriers transverse to the common boundary. -/
theorem ordAgreeBelowAt_of_transverse_ambient_carriers
    {n m : ℕ} {X : CMfd.{u} n} (hn : 0 < n) (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x)
    (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hP : RegularAtDim (n := n) P.N x m) (hQ : RegularAtDim (n := n) Q.N x m)
    (NP NQ : Set X) (hNPdim : RegularAtDim (n := n) NP x (m+1))
    (hNQdim : RegularAtDim (n := n) NQ x (m+1))
    (hPsub : P.N ⊆ NP) (hQsub : Q.N ⊆ NQ)
    (hTransP : IsTransverse n NP P.E) (hTransQ : IsTransverse n NQ P.E) :
    OrdAgreeBelowAt P Q x := by
  apply HironakaG8CaseSplitAfterN.ordAgreeBelowAt_of_tangent_case
    P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ
  intro H hH hxH hTP hTQ
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hH
  subst H
  exact HironakaG8CaseTAmbientComparison.ordAgreeBelowAt_of_transverse_ambient_carriers
    P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hP hQ NP NQ hNPdim hNQdim
    hPsub hQsub hTransP hTransQ i (MonomialPart.isClosedSubmanifold_get hn hE i) hxH hTP hTQ

end
end Hironaka.HironakaG8CaseTAmbientOrder
