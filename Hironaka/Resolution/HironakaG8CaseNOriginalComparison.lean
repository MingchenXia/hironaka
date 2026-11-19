import Hironaka.Resolution.HironakaG8CaseNOpenTransport

/-!
# Case N: original-record one-sided comparison

The empty-boundary native domains are obtained on the actual common open
where the original ideals are nonzero along their carriers. The original
local relation, SNC boundary, orders and order-two condition are transported
to that open without assuming transversality of the boundary to either carrier.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNOriginalComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen NormalCrossings DivisorExponentAlong GermIdealOrder
  HironakaG8LocalHistory
open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)

/-- The original local equivalence and natural one-sided non-tangency imply
the one-sided order inequality on the branch strictly above the common mark. -/
theorem order_le_of_original_local_equiv_and_notTangent
    {n : ℕ} {X : CMfd.{u} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x)
    (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hNotTangent : ∀ H ∈ P.E, x ∈ H →
      x ∉ cosupport n P.N (vanishingIdeal (n := n) H) 2)
    (hgreater : P.d < ordinaryTraceOrder P.N P.ideal x) :
    ordinaryTraceOrder Q.N Q.ideal x ≤ ordinaryTraceOrder P.N P.ideal x := by
  set P0 : MarkedIdeal n X := ⟨P.N, [], P.ideal, P.d⟩ with hP0
  set Q0 : MarkedIdeal n X := ⟨Q.N, [], Q.ideal, Q.d⟩ with hQ0
  have hwfP0 : P0.IsWellFormed := ⟨hNP, hIP, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hNP⟩
  have hwfQ0 : Q0.IsWellFormed := ⟨hNQ, hIQ, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hNQ⟩
  have hdQ1 : 1 ≤ Q.d := hd ▸ hd1
  have hxQc : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  let G : Opens X := HironakaG8DomainExponents.domOpen P0 hNP ⊓ HironakaG8DomainExponents.domOpen Q0 hNQ
  have hxG : x ∈ G := ⟨(HironakaG8DomainExponents.mem_domOpen_iff (P := P0) hNP hIP hd1 (P.cosupp_subset_N hx)).mpr hxP,
    (HironakaG8DomainExponents.mem_domOpen_iff (P := Q0) hNQ hIQ hdQ1 (Q.cosupp_subset_N hxQc)).mpr hxQ⟩
  have hholP : ∀ y g, P.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIP hg
  have hholQ : ∀ y g, Q.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIQ hg
  set A0 := MarkedIdeal.pullback (Subtype.val : G → X) P0 with hA0def
  set B0 := MarkedIdeal.pullback (Subtype.val : G → X) Q0 with hB0def
  have hA0 : IsInvDomain n A0 :=
    HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen hwfP0 hd1 (G := G) inf_le_left
  have hB0 : IsInvDomain n B0 :=
    HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen hwfQ0 hdQ1 (G := G) inf_le_right
  let x' : G := ⟨x, hxG⟩
  have hx'A : x' ∈ A0.cosupp := by
    change x' ∈ (MarkedIdeal.pullback (Subtype.val : G → X) P0).cosupp
    rw [cosupp_pullback_val P0 hholP G]
    exact hx
  let F : List (Set G) := P.E.map ((Subtype.val : G → X) ⁻¹' ·)
  have hEQ : Q.E = P.E := h.E_eq
  have hL := LocEquiv.restrict h G
  have hL0 : LocWPEquiv (X := CMfd.of (n := n) G)
      ({ A0 with E := F } : MarkedIdeal n (CMfd.of (n := n) G))
      ({ B0 with E := F } : MarkedIdeal n (CMfd.of (n := n) G)) := by
    simpa only [A0, B0, P0, Q0, F, MarkedIdeal.pullback, hEQ] using hL
  have hEG : IsSNCDivisor n F :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (NormalCrossingsInvariance.pullsBackCoordinates_val G)
      continuous_subtype_val hE
  have hdim0 : SameCarrierDim (X := CMfd.of (n := n) G) A0 B0 :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val (A := P0) (B := Q0) hholP hdim G
  have hOrdP : ordinaryTraceOrder (X := CMfd.of (n := n) G) A0.N A0.ideal x' =
      ordinaryTraceOrder P.N P.ideal x :=
    HironakaG8CaseNOpenTransport.ordinaryTraceOrder_pullback_val_of_coherent P0 hIP G hA0 x'
  have hOrdQ : ordinaryTraceOrder (X := CMfd.of (n := n) G) B0.N B0.ideal x' =
      ordinaryTraceOrder Q.N Q.ideal x :=
    HironakaG8CaseNOpenTransport.ordinaryTraceOrder_pullback_val_of_coherent Q0 hIQ G hB0 x'
  have hNot0 : ∀ H ∈ F, x' ∈ H →
      x' ∉ cosupport n A0.N (vanishingIdeal (n := n) H) 2 := by
    intro H hHF hxH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hHF
    intro hCos
    apply hNotTangent H₀ hH₀ hxH
    exact (HironakaG8CaseNOpenTransport.cosupport_vanishingIdeal_pullback_val P.N H₀ G x').mp hCos
  have hGreat0 : A0.d < ordinaryTraceOrder (X := CMfd.of (n := n) G) A0.N A0.ideal x' := by
    rw [hOrdP]
    exact hgreater
  have hCmp := HironakaG8CaseNNativeComparison.order_le_of_local_equiv_and_notTangent
    (X := CMfd.of (n := n) G) A0 B0 hA0 hB0 rfl rfl hdim0 hx'A hd F hEG.1 hNot0 hGreat0 hL0 hEG
  rw [hOrdP, hOrdQ] at hCmp
  exact hCmp

end
end Hironaka.HironakaG8CaseNOriginalComparison
