import Hironaka.Resolution.HironakaG8CaseNNativeComparison
import Hironaka.Invariant.SmoothCentreHomogeneity

/-!
# Case N: the original order and boundary condition on an open

These identities retain the actual carrier and the actual vanishing ideal
under an open inclusion, at a specified nonzero point.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNOpenTransport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  DivisorExponentAlong GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder ordinaryTraceOrder_cosupport_iff)

/-- Ordinary order is local under an open inclusion when both ideals are
coherent. Equality is proved at all thresholds, including the zero ideal. -/
theorem ordinaryTraceOrder_pullback_val_of_coherent
    {n k : ℕ} {X : CMfd.{u} n} (A : MarkedIdeal n X)
    (hI : A.ideal.IsCoherent)
    (O : Opens X) (hAO : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → X) A))
    (p : O) :
    ordinaryTraceOrder (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → X) A).N
      (MarkedIdeal.pullback (Subtype.val : O → X) A).ideal p =
      ordinaryTraceOrder A.N A.ideal p.val := by
  let AP := MarkedIdeal.pullback (Subtype.val : O → X) A
  have hHol : ∀ x f, A.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  change NonmonomialOrderLocal.nmOrd (M := CMfd.of (n := n) O)
    (HironakaSharpOriginalProductTraceOrder.ordinaryTraceMarked (X := CMfd.of (n := n) O) AP.N AP.ideal) p =
      NonmonomialOrderLocal.nmOrd (M := X)
        (HironakaSharpOriginalProductTraceOrder.ordinaryTraceMarked (X := X) A.N A.ideal) p.val
  apply NonmonomialOrderLocal.nmOrd_congr
  intro q
  rw [HironakaSharpOriginalProductTraceOrder.ordGe_ordinaryTraceMarked_eq_cosupport
      (X := CMfd.of (n := n) O) AP.N AP.ideal hAO.isWellFormed.isCoherent,
    HironakaSharpOriginalProductTraceOrder.ordGe_ordinaryTraceMarked_eq_cosupport (X := X) A.N A.ideal hI]
  have hCos := cosupp_pullback_val
    (⟨A.N, A.E, A.ideal, q⟩ : MarkedIdeal n X) hHol O
  change p ∈ (MarkedIdeal.pullback (Subtype.val : O → X)
    (⟨A.N, A.E, A.ideal, q⟩ : MarkedIdeal n X)).cosupp ↔ _
  rw [hCos]
  rfl

/-- Every order-two vanishing-ideal cosupport threshold is literally
preserved by restriction to an actual open. -/
theorem cosupport_vanishingIdeal_pullback_val
    {n : ℕ} {X : CMfd.{u} n} (N H : Set X) (O : Opens X) (p : O) :
    p ∈ cosupport n ((Subtype.val : O → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : O → X) ⁻¹' H)) 2 ↔
    p.val ∈ cosupport n N (vanishingIdeal (n := n) H) 2 := by
  have hHol : ∀ x f, (vanishingIdeal (n := n) H).mem x f → HolomorphicAt n f x :=
    fun _ _ hf => hf.1
  have hCos := cosupp_pullback_val
    (⟨N, [], vanishingIdeal (n := n) H, 2⟩ : MarkedIdeal n X) hHol O
  change cosupport n ((Subtype.val : O → X) ⁻¹' N)
    (GermIdeal.pullback (m := n) (Subtype.val : O → X) (vanishingIdeal (n := n) H)) 2 =
    (Subtype.val : O → X) ⁻¹' cosupport n N (vanishingIdeal (n := n) H) 2 at hCos
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal O H] at hCos
  exact Set.ext_iff.mp hCos p

end
end Hironaka.HironakaG8CaseNOpenTransport
