import Hironaka.Resolution.HironakaG8P1ArcDirectrix

set_option autoImplicit false

/-!
# Intrinsic tangent containment from the source order-two comparison

For a regular carrier at a point on an arbitrary set, order-two cosupport
of the set's vanishing ideal is exactly inclusion of the carrier tangent
in the set's intrinsic tangent. Thus the source pointwise order-two
comparison transfers literal tangent containment and noncontainment
between the two locally weakly equivalent carriers.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11IntrinsicTangentTransfer

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupSpaceTangent NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder DivisorExponentAlong HironakaG8P1ArcOrderTwo HironakaG8P1ArcDirectrix
  HironakaG8LocalHistory HironakaG11InvBMClass

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- On a regular carrier at a point of `H`, order two of the vanishing
ideal of `H` is exactly intrinsic tangent-space containment. -/
theorem cosupport_vanishing_two_iff_tangent_le {N H : Set X} {x : X} {k : ℕ}
    (hN : RegularAtDim (n := n) N x k) (hxH : x ∈ H) :
    x ∈ cosupport n N (vanishingIdeal (n := n) H) 2 ↔
      tangentSpace n N x ≤ tangentSpace n H x := by
  constructor
  · intro h ξ hξ
    apply mem_tangentSpace.mpr
    intro f hf
    exact germDiff_eq_zero_of_order_two hf.1 (h.2 f hf) hξ
  · intro h
    refine ⟨hN.2.1, fun f hf => ?_⟩
    apply order_two_of_germDiff_eq_zero hN hf.1 (hf.2.self_of_nhds hxH)
    intro ξ hξ
    exact germDiff_eq_zero_of_mem_tangentSpace (h hξ) hf

/-- The source order-greater-than-mark comparison transfers literal tangent
containment in an arbitrary incident set, without a chosen defining equation. -/
theorem tangent_le_iff_of_locWPEquiv_order_gt
    (P Q : MarkedIdeal n X) (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent)
    (hE : IsSNCDivisor n P.E) (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x) (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hsucc : x ∈ cosupport n P.N P.ideal (P.d + 1)) {H : Set X} (hxH : x ∈ H) :
    tangentSpace n P.N x ≤ tangentSpace n H x ↔ tangentSpace n Q.N x ≤ tangentSpace n H x := by
  have hxQc : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  obtain ⟨kP, hkP⟩ := hNP.2 x (P.cosupp_subset_N hx)
  obtain ⟨kQ, hkQ⟩ := hNQ.2 x (Q.cosupp_subset_N hxQc)
  calc
    tangentSpace n P.N x ≤ tangentSpace n H x ↔
        x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2 :=
      (cosupport_vanishing_two_iff_tangent_le hkP hxH).symm
    _ ↔ x ∈ cosupport n Q.N (vanishingIdeal (n := n) H) 2 :=
      tangent_member_iff_of_locWPEquiv_order_gt P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hsucc H
    _ ↔ tangentSpace n Q.N x ≤ tangentSpace n H x :=
      cosupport_vanishing_two_iff_tangent_le hkQ hxH

end

end Hironaka.HironakaG11IntrinsicTangentTransfer
