import Hironaka.Resolution.HironakaG8CaseNNativeComparison

/-! Pointwise finite ordinary order along a carrier, using only nonzeroness
at the point in question. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNPointwiseOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan MonomialPartAlong RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers GermIdealOrder
  NonmonomialOrderLocal DivisorExponentAlong IdealWeightPowers OrderTaylor GermOrderProduct
  MonomialCase MemberPullback BlowupFlatCoordinates SimultaneousNormalCrossings
open HironakaSharpOriginalProductTraceOrder

/-- The ordinary carrier-order cosupport dictionary needs nonzeroness only
at the given point, not at every point of the carrier. -/
theorem ordinaryTraceOrder_cosupport_iff_of_at
    {n : ℕ} {X : CMfd.{u} n} {W : Set X} {I : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent)
    {x : X} (hx : x ∈ W) (hne : IsNonzeroAlongAt W I x) (q : ℕ) :
    x ∈ cosupport n W I q ↔ q ≤ ordinaryTraceOrder W I x := by
  have hfin : ∃ q, x ∉ ordGe (ordinaryTraceMarked W I) (q + 1) := by
    obtain ⟨g, hg, hfreq⟩ := hne
    obtain ⟨k, hk⟩ := hW.2 x hx
    obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
    have hghol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hI x g hg
    obtain ⟨j, hj⟩ := hr.exists_not_vanishesToOrderOn hghol hfreq
    refine ⟨j, fun hmem => hj ?_⟩
    have hg' : (nmPart (ordinaryTraceMarked W I)).mem x g :=
      NonmonomialTransformAlong.le_nonmonomialPartAlong_self hI x g hg
    exact (ordGe_anti (ordinaryTraceMarked W I) (Nat.le_succ j) hmem).2 g hg'
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport W I hI q]
  change x ∈ ordGe (ordinaryTraceMarked W I) q ↔ q ≤ nmOrd (ordinaryTraceMarked W I) x
  cases q with
  | zero =>
    refine ⟨fun _ => Nat.zero_le _, fun _ => ?_⟩
    change x ∈ cosupport n W (nmPart (ordinaryTraceMarked W I)) 0
    rw [cosupport_zero (𝔞 := nmPart (ordinaryTraceMarked W I)) (fun _ _ hg => hg.1)]
    exact hx
  | succ q => exact ⟨succ_le_nmOrd_of_mem hfin, mem_ordGe_of_succ_le⟩

end
end Hironaka.HironakaG8CaseNPointwiseOrder
