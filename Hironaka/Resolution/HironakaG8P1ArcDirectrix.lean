import Hironaka.Resolution.HironakaG8P1ArcOrderTwo

set_option autoImplicit false

/-!
# The source-facing order-two directrix comparison

Use the same genuine nonzero-domain restriction and empty-boundary native
records as Lemma M(i), apply the constructed native ideal comparison, and
transport the literal order-two cosupport back to the original carriers.
No tangent-space restriction transport or caller-supplied directrix result
is required.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcDirectrix

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen GermIdealOrder
  RestrictedIdealQuotient MarkedIdealBiholomorphism DivisorExponentAlong RelativePrincipalizationSpan
  HironakaActualProjectionTestRecord HironakaG8P1ArcPair HironakaG8P1ArcOrderTwo

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaG8LocalHistory (LocWPEquiv LocEquiv)
open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The source's ordinary locally weakly equivalent pair, with nonzero
original ideals at the point and order greater than the mark for P,
compares the order-two cosupport of every original holomorphic germ ideal.
The native frame/tangent comparison is constructed on the actual domOpen
intersection, then the cosupport is transported back by restriction. -/
theorem cosupport_two_iff_of_locWPEquiv_order_gt
    (P Q : MarkedIdeal n X) (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent)
    (hE : IsSNCDivisor n P.E) (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x) (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hsucc : x ∈ cosupport n P.N P.ideal (P.d + 1))
    (I : GermIdeal n X) (hI : ∀ y f, I.mem y f → HolomorphicAt n f y) :
    x ∈ cosupport n P.N I 2 ↔ x ∈ cosupport n Q.N I 2 := by
  let P0 : MarkedIdeal n X := ⟨P.N, [], P.ideal, P.d⟩
  let Q0 : MarkedIdeal n X := ⟨Q.N, [], Q.ideal, Q.d⟩
  have hwfP0 : P0.IsWellFormed := ⟨hNP, hIP, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hNP⟩
  have hwfQ0 : Q0.IsWellFormed := ⟨hNQ, hIQ, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hNQ⟩
  have hdQ1 : 1 ≤ Q.d := hd ▸ hd1
  have hxQc : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  let G : Opens X := HironakaG8DomainExponents.domOpen P0 hNP ⊓ HironakaG8DomainExponents.domOpen Q0 hNQ
  have hxG : x ∈ G := ⟨
    (HironakaG8DomainExponents.mem_domOpen_iff (P := P0) hNP hIP hd1 (P.cosupp_subset_N hx)).mpr hxP,
    (HironakaG8DomainExponents.mem_domOpen_iff (P := Q0) hNQ hIQ hdQ1 (Q.cosupp_subset_N hxQc)).mpr hxQ⟩
  have hholP : ∀ y g, P.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIP hg
  let A0 := MarkedIdeal.pullback (Subtype.val : G → X) P0
  let B0 := MarkedIdeal.pullback (Subtype.val : G → X) Q0
  have hA0 : IsInvDomain n A0 :=
    HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen hwfP0 hd1 (G := G) inf_le_left
  have hB0 : IsInvDomain n B0 :=
    HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen hwfQ0 hdQ1 (G := G) inf_le_right
  let x' : G := ⟨x, hxG⟩
  have hcosP : ∀ e, cosupport n ((Subtype.val : G → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) P.ideal) e =
      (Subtype.val : G → X) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n X) hholP G
  have hx'A : x' ∈ A0.cosupp := by
    change x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) P.ideal) P.d
    rw [hcosP]
    exact hx
  have hsuccA : x' ∈ cosupport n A0.N A0.ideal (A0.d + 1) := by
    change x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) P.ideal) (P.d + 1)
    rw [hcosP]
    exact hsucc
  have hgreater : A0.d < HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder
      (X := CMfd.of (n := n) G) A0.N A0.ideal x' := by
    have hge := (HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff
      (X := CMfd.of (n := n) G)
      hA0.isWellFormed.isClosedSubmanifold_N hA0.isWellFormed.isCoherent hA0.isNonzeroAlongAt
      (A0.cosupp_subset_N hx'A) (A0.d + 1)).mp hsuccA
    omega
  have hL : LocWPEquiv (X := CMfd.of (n := n) G) (MarkedIdeal.pullback (Subtype.val : G → X) P)
      (MarkedIdeal.pullback (Subtype.val : G → X) Q) := LocEquiv.restrict h G
  have hLp := locWPEquiv_projectionTest hL
  have hsA := sameNID_projectionTest (X := CMfd.of (n := n) G) (M := A0)
    (M' := MarkedIdeal.pullback (Subtype.val : G → X) P) ⟨rfl, rfl, rfl⟩
  have hsB := sameNID_projectionTest (X := CMfd.of (n := n) G) (M := B0)
    (M' := MarkedIdeal.pullback (Subtype.val : G → X) Q) ⟨rfl, rfl, rfl⟩
  have hEG : IsSNCDivisor n (MarkedIdeal.pullback (Subtype.val : G → X) P).E :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (NormalCrossingsInvariance.pullsBackCoordinates_val G)
      continuous_subtype_val hE
  have hE' := HironakaG8ClassStepCut.isSNCDivisor_projectionTest (Y := CMfd.of (n := n) G)
    (A := MarkedIdeal.pullback (Subtype.val : G → X) P) hEG
  have hdim0 : SameCarrierDim (X := CMfd.of (n := n) G) A0 B0 :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val (A := P0) (B := Q0) hholP hdim G
  have hNative := cosupport_two_iff_of_native_pair_order_gt
    A0 B0 hA0 hB0 rfl hdim0 hx'A _ _ hsA hsB hLp.wEquiv hE' hgreater
    (GermIdeal.pullback (m := n) (Subtype.val : G → X) I)
    (fun _ hf => (GermIdeal.mem_pullback_iff.mp hf).holomorphicAt)
  have hcosPI : cosupport n ((Subtype.val : G → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) I) 2 =
      (Subtype.val : G → X) ⁻¹' cosupport n P.N I 2 :=
    cosupp_pullback_val (⟨P.N, [], I, 2⟩ : MarkedIdeal n X) hI G
  have hcosQI : cosupport n ((Subtype.val : G → X) ⁻¹' Q.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) I) 2 =
      (Subtype.val : G → X) ⁻¹' cosupport n Q.N I 2 :=
    cosupp_pullback_val (⟨Q.N, [], I, 2⟩ : MarkedIdeal n X) hI G
  change x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) I) 2 ↔
    x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' Q.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) I) 2 at hNative
  rw [hcosPI, hcosQI] at hNative
  exact hNative

/-- The source's literal ideal-theoretic directrix clause (T') for an
original member H, with the native comparison produced internally. -/
theorem tangent_member_iff_of_locWPEquiv_order_gt
    (P Q : MarkedIdeal n X) (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent)
    (hE : IsSNCDivisor n P.E) (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x) (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hsucc : x ∈ cosupport n P.N P.ideal (P.d + 1)) (H : Set X) :
    x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2 ↔
      x ∈ cosupport n Q.N (vanishingIdeal (n := n) H) 2 :=
  cosupport_two_iff_of_locWPEquiv_order_gt
    P Q h hNP hNQ hIP hIQ hE hd1 hd hdim hx hxP hxQ hsucc
    (vanishingIdeal (n := n) H) (fun _ _ hf => hf.1)

end

end Hironaka.HironakaG8P1ArcDirectrix
