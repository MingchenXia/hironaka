import Hironaka.Resolution.HironakaG8P1NormalizedOrder
import Hironaka.Resolution.HironakaG8ClassStepLower

/-!
# Case N: dropping the actual empty old prefix and applying native P1

This module is the endpoint restriction/P1 consumer. It does not select the
generic point or assert the full ordinary-input Case N order equivalence.

This is the endpoint consumer of the point constructed in
`HironakaG8CaseNGenericPoint`. It does not select that point independently.
From the retained local class relation with a finite old prefix, it constructs
the actual open complement, drops the empty prefix, and derives native order
agreement by P1. No order-agreement or protection certificate is an input.
The exact tower prefix identity and the full ordinary-input Case N assembly
remain separate, as recorded in `G8N-CASE-N-ROUTE.md`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8CaseNRestriction

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen HironakaG8LocalHistory

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder ordinaryTraceOrder_cosupport_iff)

/-- Native ordinary order is unchanged by the actual open inclusion. This is
derived from all literal cosupport thresholds and domain nonzeroness. -/
theorem ordinaryTraceOrder_pullback_val_of_domain
    {n k : ℕ} {X : CMfd.{u} n} (A : MarkedIdeal n X) (hA : IsInvDomain k A)
    (O : Opens X) (p : O) (hp : p.val ∈ A.N) :
    ordinaryTraceOrder (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → X) A).N
      (MarkedIdeal.pullback (Subtype.val : O → X) A).ideal p =
      ordinaryTraceOrder A.N A.ideal p.val := by
  let AP := MarkedIdeal.pullback (Subtype.val : O → X) A
  have hAP : IsInvDomain k AP := InvDomainTowerAlong.isInvDomain_pullback_val O hA
  have hHol : ∀ x f, A.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hA.isWellFormed.isCoherent hf
  have hpAP : p ∈ AP.N := hp
  have hThreshold (q : ℕ) :
      q ≤ ordinaryTraceOrder (X := CMfd.of (n := n) O) AP.N AP.ideal p ↔
      q ≤ ordinaryTraceOrder A.N A.ideal p.val := by
    rw [← ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n) O)
      (W := AP.N) (I := AP.ideal) hAP.isWellFormed.isClosedSubmanifold_N
      hAP.isWellFormed.isCoherent hAP.isNonzeroAlongAt hpAP q,
      ← ordinaryTraceOrder_cosupport_iff (X := X) (W := A.N) (I := A.ideal)
        hA.isWellFormed.isClosedSubmanifold_N
        hA.isWellFormed.isCoherent hA.isNonzeroAlongAt hp q]
    have hCos := cosupp_pullback_val
      (⟨A.N, A.E, A.ideal, q⟩ : MarkedIdeal n X) hHol O
    change p ∈ (MarkedIdeal.pullback (Subtype.val : O → X)
      (⟨A.N, A.E, A.ideal, q⟩ : MarkedIdeal n X)).cosupp ↔ _
    rw [hCos]
    rfl
  exact Nat.le_antisymm
    ((hThreshold _).mp le_rfl) ((hThreshold _).mpr le_rfl)

/-- At a point off the literal finite original prefix, construct an actual
open where that prefix is empty, retain its native boundary tail, and derive
the normalized order equality from the local class relation by native P1.

In Case N, `A,B` are the actual native stage records, `F` is the actual list
of strict original members, and the point is constructed from the actual arc
counts. Original-boundary transversality is not assumed. -/
theorem normalized_order_eq_off_finite_original_prefix
    {n kA kB : ℕ} {X : CMfd.{u} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hE : B.E = A.E)
    (hdim : SameCarrierDim A B) (F : List (Set X))
    (hClosed : ∀ H ∈ F, IsClosed H)
    (h : LocWPEquiv ({ A with E := F ++ A.E } : MarkedIdeal n X)
      ({ B with E := F ++ B.E } : MarkedIdeal n X))
    {y : X} (hyA : y ∈ A.cosupp) (hyOff : ∀ H ∈ F, y ∉ H) :
    B.d * ordinaryTraceOrder A.N A.ideal y =
      A.d * ordinaryTraceOrder B.N B.ideal y := by
  classical
  let O : Opens X :=
    ⟨(⋃ i : Fin F.length, F.get i)ᶜ,
      (isClosed_iUnion_of_finite fun i => hClosed _ (List.get_mem F i)).isOpen_compl⟩
  have hyO : y ∈ O := by
    intro hyUnion
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyUnion
    exact hyOff _ (List.get_mem F i) hi
  let p : O := ⟨y, hyO⟩
  let AP := MarkedIdeal.pullback (Subtype.val : O → X) A
  let BP := MarkedIdeal.pullback (Subtype.val : O → X) B
  have hHolA : ∀ x f, A.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hA.isWellFormed.isCoherent hf
  have hDomA : IsInvDomain kA AP := InvDomainTowerAlong.isInvDomain_pullback_val O hA
  have hDomB : IsInvDomain kB BP := InvDomainTowerAlong.isInvDomain_pullback_val O hB
  have hRestricted := LocEquiv.restrict h O
  have hSplit :
      (MarkedIdeal.pullback (Subtype.val : O → X) { A with E := F ++ A.E }).E =
        F.map ((Subtype.val : O → X) ⁻¹' ·) ++ A.E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    simp only [MarkedIdeal.pullback, List.map_append]
  have hEmpty : ∀ H ∈ F.map ((Subtype.val : O → X) ⁻¹' ·), H = ∅ := by
    intro H hHF
    obtain ⟨H₀, hH₀F, rfl⟩ := List.mem_map.mp hHF
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH₀F
    exact q.property (mem_iUnion.mpr ⟨i, hq⟩)
  have hDropped := HironakaG8ClassStepLower.locEquiv_drop rfl hRestricted hSplit hEmpty
  have hNative : LocWPEquiv (X := CMfd.of (n := n) O) AP BP := by
    simpa only [AP, BP, MarkedIdeal.pullback, hE] using hDropped
  have hpA : p ∈ AP.cosupp := by
    change p ∈ (MarkedIdeal.pullback (Subtype.val : O → X) A).cosupp
    rw [cosupp_pullback_val A hHolA O]
    exact hyA
  have hDim : SameCarrierDim (X := CMfd.of (n := n) O) AP BP :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val hHolA hdim O
  have hpB : p ∈ BP.cosupp := hNative.cosupp_eq_base ▸ hpA
  have hOrders := HironakaG8P1NormalizedOrder.normalized_order_eq_of_locWPEquiv
    hNative hDomA hDomB hDim hpA
  change B.d * ordinaryTraceOrder (X := CMfd.of (n := n) O) AP.N AP.ideal p =
    A.d * ordinaryTraceOrder (X := CMfd.of (n := n) O) BP.N BP.ideal p at hOrders
  rw [ordinaryTraceOrder_pullback_val_of_domain A hA O p (A.cosupp_subset_N hyA),
    ordinaryTraceOrder_pullback_val_of_domain B hB O p (BP.cosupp_subset_N hpB)] at hOrders
  exact hOrders

end

end Hironaka.HironakaG8CaseNRestriction
