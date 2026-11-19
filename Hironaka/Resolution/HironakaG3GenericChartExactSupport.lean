import Hironaka.Resolution.HironakaG3VisibleListSupport
import Hironaka.Resolution.HironakaG3GenericChartBoundaryReadout
import Hironaka.Resolution.HironakaG3RPureEmbedded
import Hironaka.Resolution.HironakaG3RBoundaryEmbedded
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GenericChartExactSupport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaDisjointFiniteControlledHistory HironakaG3RTowerClass
  HironakaG3GenericChartBoundaryReadout HironakaG3VisibleListSupport HironakaG3RPureEmbedded
  HironakaG3RBoundaryEmbedded HironakaPrincipalization

/-- A window-independent bound on the actual tower exceptional divisor makes
any complete chart-boundary readout have exactly inherited-plus-exceptional support. -/
theorem chart_boundary_exact_support_of_exceptional_divisor_bound
    {n : ℕ} {X Z : CMfd.{0} n} {𝒞 : LocalTowerClass X} {κ : Type*}
    (D : κ → Set X) (hD : ∀ j, IsClosed (D j)) {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart 𝒞 Z P) (E : List (Set X))
    (hMembers : ∀ H ∈ E, ∃ j, H = D j)
    (hVis : ∀ j, (D j ∩ (c.U : Set X)).Nonempty → D j ∈ E)
    (hBound : (exceptionalDivisor c.T).support ⊆
      c.T.proj ⁻¹' ((Subtype.val : c.U → X) ⁻¹' (⋃ j, D j)) ∪ exceptionalLocus n c.T.proj) :
    (⋃ H ∈ chartBoundaryOfList c E, H) =
      (P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P) ∩ c.V := by
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  have hlocal := visible_list_transformed_support D hD c.U E hMembers hVis J c.T
  have hExc : exceptionalLocus n c.T.proj ⊆ (exceptionalDivisor c.T).support :=
    HironakaPrincipalization.exceptionalLocus_subset_support c.T
  have heq : c.T.proj ⁻¹' ((Subtype.val : c.U → X) ⁻¹' (⋃ j, D j)) ∪ (exceptionalDivisor c.T).support =
      c.T.proj ⁻¹' ((Subtype.val : c.U → X) ⁻¹' (⋃ j, D j)) ∪ exceptionalLocus n c.T.proj := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact Or.inl hy
      · exact hBound hy
    · rintro (hy | hy)
      · exact Or.inl hy
      · exact Or.inr (hExc hy)
  unfold chartBoundaryOfList
  rw [HironakaG3RPureEmbedded.iUnion_map_image,hlocal,heq,Set.image_union,
    HironakaG3RBoundaryEmbedded.image_chartIncl_preimage]
  have hChartExc : chartIncl c '' exceptionalLocus n c.T.proj = exceptionalLocus n P ∩ c.V := by
    rw [exceptionalLocus_chart c hP, Set.image_preimage_eq_inter_range, range_chartIncl]
  rw [hChartExc]
  ext z
  simp only [mem_union,mem_inter_iff]
  tauto
end
end Hironaka.HironakaG3GenericChartExactSupport
