import Hironaka.Resolution.HironakaG8CaseNOriginalComparison
import Hironaka.Resolution.HironakaG8CaseNPointwiseOrder

/-!
# Case N: original two-sided ordinary order equality

The two natural non-tangency conditions are retained explicitly. Lemma M(i)
handles the common-mark branch and synchronizes the strict-order branch.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNTwoSided
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  DivisorExponentAlong GermIdealOrder HironakaG8LocalHistory
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)

/-- When both carriers satisfy the natural order-two condition for each
original boundary member, the actual original ordinary orders agree. -/
theorem ordinaryTraceOrder_eq_of_original_local_equiv_notTangent
    {n : ℕ} {X : CMfd.{u} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x)
    (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hNotP : ∀ H ∈ P.E, x ∈ H →
      x ∉ cosupport n P.N (vanishingIdeal (n := n) H) 2)
    (hNotQ : ∀ H ∈ Q.E, x ∈ H →
      x ∉ cosupport n Q.N (vanishingIdeal (n := n) H) 2) :
    ordinaryTraceOrder P.N P.ideal x = ordinaryTraceOrder Q.N Q.ideal x := by
  have hxQcos : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  have hDimQ : SameCarrierDim Q P :=
    HironakaG8SpecialLoci.SameCarrierDim.symm_of_cosupp_eq h.cosupp_eq_base hdim
  have hEQ : Q.E = P.E := h.E_eq
  have hQE : IsSNCDivisor n Q.E := by rw [hEQ]; exact hE
  have hdQ : 1 ≤ Q.d := hd ▸ hd1
  have hM := HironakaG8P1ArcPair.cosupport_succ_iff P Q h hNP hNQ hIP hIQ hE
    hd1 hd hdim hx hxP hxQ
  have hPcut := HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
    hNP hIP (P.cosupp_subset_N hx) hxP (P.d+1)
  have hQcut := HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
    hNQ hIQ (Q.cosupp_subset_N hxQcos) hxQ (Q.d+1)
  have hPbase := (HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
    hNP hIP (P.cosupp_subset_N hx) hxP P.d).mp hx
  have hQbase := (HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
    hNQ hIQ (Q.cosupp_subset_N hxQcos) hxQ Q.d).mp hxQcos
  by_cases hPgt : P.d < ordinaryTraceOrder P.N P.ideal x
  · have hxPnext : x ∈ cosupport n P.N P.ideal (P.d+1) := hPcut.mpr (by omega)
    have hxQnext : x ∈ cosupport n Q.N Q.ideal (Q.d+1) := by
      rw [hd]
      exact hM.mp hxPnext
    have hQgt : Q.d < ordinaryTraceOrder Q.N Q.ideal x := by
      have := hQcut.mp hxQnext
      omega
    have hQP := HironakaG8CaseNOriginalComparison.order_le_of_original_local_equiv_and_notTangent
      P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hNotP hPgt
    have hPQ := HironakaG8CaseNOriginalComparison.order_le_of_original_local_equiv_and_notTangent
      Q P h.symm hNQ hNP hIQ hIP hQE hdQ hd.symm hDimQ hxQcos hxQ hxP hNotQ hQgt
    exact Nat.le_antisymm hPQ hQP
  · have hxPnot : x ∉ cosupport n P.N P.ideal (P.d+1) := by
      intro hxNext
      have := hPcut.mp hxNext
      omega
    have hxQnot : x ∉ cosupport n Q.N Q.ideal (Q.d+1) := by
      rw [hd]
      exact fun hq => hxPnot (hM.mpr hq)
    have hQnot : ¬ Q.d+1 ≤ ordinaryTraceOrder Q.N Q.ideal x :=
      fun hq => hxQnot (hQcut.mpr hq)
    omega

end
end Hironaka.HironakaG8CaseNTwoSided
