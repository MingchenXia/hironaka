import Hironaka.Resolution.HironakaG8CaseTSingleCutDomain

/-!
# Case T: the singleton cut gives the tangent order comparison

The actual one-member cut is locally equivalent, nonzero at the original
point, and compared by native P1 on the constructed common domain open.
The normal-crossing remainder is still an explicit input.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTSingleCutOrder
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen NormalCrossings DivisorExponentAlong GermIdealOrder
  IdealWeightPowers HironakaG8LocalHistory HironakaG8CaseTSingleCut
  HironakaG8CaseTSingleCutDomain HironakaG8CaseTSingleCutCosupport
open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaG8ClassStepHistory (OrdAgreeBelowAt)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)

/-- The tangent order comparison holds when the selected first boundary
member has a well-formed ordered remainder for both original carriers. -/
theorem ordAgreeBelowAt_of_single_tangent_cut
    {n : ℕ} {X : CMfd.{u} n} (A B : MarkedIdeal n X)
    (G : List (Set X)) (H : Set X)
    (h : LocWPEquiv A B) (hE : A.E = [H] ++ G)
    (hSNC : IsSNCDivisor n A.E) (hH : IsClosedSubmanifold n H)
    (hWA : ({ A with E := G } : MarkedIdeal n X).IsWellFormed)
    (hWB : ({ B with E := G } : MarkedIdeal n X).IsWellFormed)
    (hd : B.d = A.d) (hd1 : 1 ≤ A.d) (hdim : SameCarrierDim A B)
    {x : X} (hx : x ∈ A.cosupp)
    (hxA : IsNonzeroAlongAt A.N A.ideal x)
    (hxB : IsNonzeroAlongAt B.N B.ideal x)
    (hTA : x ∈ cosupport n A.N (vanishingIdeal (n := n) H) 2)
    (hTB : x ∈ cosupport n B.N (vanishingIdeal (n := n) H) 2) :
    OrdAgreeBelowAt A B x := by
  let JA := singleCut A G H
  let JB := singleCut B G H
  have hHolA : ∀ y f, A.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hWA.isCoherent hf
  have hHolB : ∀ y f, B.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hWB.isCoherent hf
  have hwJA : JA.IsWellFormed := isWellFormed_singleCut A G H hH hWA
  have hwJB : JB.IsWellFormed := isWellFormed_singleCut B G H hH hWB
  have hnzJA : IsNonzeroAlongAt JA.N JA.ideal x := isNonzeroAlongAt_singleCut A G H hWA.isCoherent hxA
  have hnzJB : IsNonzeroAlongAt JB.N JB.ideal x := isNonzeroAlongAt_singleCut B G H hWB.isCoherent hxB
  have hdB : 1 ≤ B.d := hd ▸ hd1
  have hLoc : LocWPEquiv JA JB := locWPEquiv_singleCut A B G H h hE hSNC hH hWA hWB hd1 hdB
  have hxJA : x ∈ JA.cosupp := by
    change x ∈ cosupport n A.N (singleCut A G H).ideal A.d
    rw [cosupport_singleCut_iff A G H hHolA]
    exact (HironakaG8ClassStepTangent.mem_cosupport_sumIdeal_idealPow_iff hHolA hTA (by omega)).mpr hx
  have hxJB : x ∈ JB.cosupp := hLoc.cosupp_eq_base ▸ hxJA
  have hJDim : SameCarrierDim JA JB := by
    intro y hy j
    have hyA : y ∈ A.cosupp := by
      change y ∈ cosupport n A.N (singleCut A G H).ideal A.d at hy
      rw [cosupport_singleCut_iff A G H hHolA,
        IdealOrderArithmetic.cosupport_sumIdeal hHolA
          (fun _ _ hf => GermIdealOrder.holomorphicAt_of_mem_idealPow hf) A.d] at hy
      exact hy.1
    exact hdim y hyA j
  let O : Opens X := HironakaG8DomainExponents.domOpen JA hwJA.isClosedSubmanifold_N ⊓
    HironakaG8DomainExponents.domOpen JB hwJB.isClosedSubmanifold_N
  have hxO : x ∈ O := ⟨(HironakaG8DomainExponents.mem_domOpen_iff hwJA.isClosedSubmanifold_N
    hwJA.isCoherent hd1 (JA.cosupp_subset_N hxJA)).mpr hnzJA,
    (HironakaG8DomainExponents.mem_domOpen_iff hwJB.isClosedSubmanifold_N
      hwJB.isCoherent hdB (JB.cosupp_subset_N hxJB)).mpr hnzJB⟩
  let p : O := ⟨x, hxO⟩
  let PA := MarkedIdeal.pullback (Subtype.val : O → X) JA
  let PB := MarkedIdeal.pullback (Subtype.val : O → X) JB
  have hPA : IsInvDomain n PA := HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen
    hwJA hd1 (G := O) inf_le_left
  have hPB : IsInvDomain n PB := HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen
    hwJB hdB (G := O) inf_le_right
  have hJAhol : ∀ y f, JA.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwJA.isCoherent hf
  have hPAcos : p ∈ PA.cosupp := by
    change p ∈ (MarkedIdeal.pullback (Subtype.val : O → X) JA).cosupp
    rw [cosupp_pullback_val JA hJAhol O]
    exact hxJA
  have hPdim : SameCarrierDim (X := CMfd.of (n := n) O) PA PB :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val hJAhol hJDim O
  have hOrders := HironakaG8P1NormalizedOrder.normalized_order_eq_of_locWPEquiv
    (LocEquiv.restrict hLoc O) hPA hPB hPdim hPAcos
  have hMarks : PB.d = PA.d := hd
  rw [hMarks] at hOrders
  have hOrd : ordinaryTraceOrder (X := CMfd.of (n := n) O) PA.N PA.ideal p =
      ordinaryTraceOrder (X := CMfd.of (n := n) O) PB.N PB.ideal p :=
    Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hPA.one_le_d) hOrders
  have hOrdA := HironakaG8CaseNOpenTransport.ordinaryTraceOrder_pullback_val_of_coherent JA hwJA.isCoherent O hPA p
  have hOrdB := HironakaG8CaseNOpenTransport.ordinaryTraceOrder_pullback_val_of_coherent JB hwJB.isCoherent O hPB p
  rw [hOrdA, hOrdB] at hOrd
  apply HironakaG8ClassStepTangent.ordAgreeBelowAt_of_tangent_sumIdeal hWA.isCoherent hWB.isCoherent hTA hTB
  intro e _he
  change x ∈ cosupport n A.N (RestrictedIdealExtension.sumIdeal A.ideal
    (idealPow (vanishingIdeal (n := n) H) A.d)) e ↔
    x ∈ cosupport n B.N (RestrictedIdealExtension.sumIdeal B.ideal
      (idealPow (vanishingIdeal (n := n) H) A.d)) e
  have hCutB : x ∈ cosupport n B.N (RestrictedIdealExtension.sumIdeal B.ideal
      (idealPow (vanishingIdeal (n := n) H) A.d)) e ↔
      x ∈ cosupport n B.N (singleCut B G H).ideal e := by
    simpa only [hd] using (cosupport_singleCut_iff B G H hHolB e x).symm
  rw [← cosupport_singleCut_iff A G H hHolA, hCutB]
  change x ∈ cosupport n JA.N JA.ideal e ↔ x ∈ cosupport n JB.N JB.ideal e
  rw [HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
      (X := X) hwJA.isClosedSubmanifold_N hwJA.isCoherent (JA.cosupp_subset_N hxJA) hnzJA e,
    HironakaG8CaseNPointwiseOrder.ordinaryTraceOrder_cosupport_iff_of_at
      (X := X) hwJB.isClosedSubmanifold_N hwJB.isCoherent (JB.cosupp_subset_N hxJB) hnzJB e, hOrd]

end
end Hironaka.HironakaG8CaseTSingleCutOrder
