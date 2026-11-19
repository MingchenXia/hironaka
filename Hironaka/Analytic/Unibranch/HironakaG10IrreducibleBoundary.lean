import Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
import Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata

/-! # Irreducible strata meet the Hironaka boundary -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka

namespace Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata

noncomputable section

/-- Intersections of native analytic subsets are native analytic. -/
theorem isAnalyticSubset_inter {X : SourceReducedComplexSpace}
    {A B : Set X.obj.left} (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) :
    X.IsAnalyticSubset (A ∩ B) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val '' (e.toPoint ⁻¹' A)) ∩ (Subtype.val '' (e.toPoint ⁻¹' B)),
    (analytic_image_trace hA e).inter (analytic_image_trace hB e), ?_⟩
  rw [Set.preimage_inter, Set.preimage_inter,
    Set.preimage_image_eq _ Subtype.val_injective,
    Set.preimage_image_eq _ Subtype.val_injective]

/-- Removing a proper analytic subset from an irreducible analytic set leaves
  a dense subset of it. -/
theorem subset_closure_diff_of_irreducible {X : SourceReducedComplexSpace}
    {C Z : Set X.obj.left} (hC : X.IsIrreducibleAnalyticSubset C)
    (hZ : X.IsAnalyticSubset Z) (hnot : ¬ C ⊆ Z) : C ⊆ closure (C \ Z) := by
  have hCZ : X.IsAnalyticSubset (C ∩ Z) := isAnalyticSubset_inter hC.1 hZ
  have hK : X.IsAnalyticSubset (closure (C \ Z)) := isAnalyticSubset_closure_diff hC.1 hZ
  have hKC : closure (C \ Z) ⊆ C := closure_minimal sdiff_subset hC.1.isClosed
  have heq : C = (C ∩ Z) ∪ closure (C \ Z) := by
    refine Subset.antisymm (fun x hx => ?_) (union_subset inter_subset_left hKC)
    by_cases hxZ : x ∈ Z
    · exact Or.inl ⟨hx, hxZ⟩
    · exact Or.inr (subset_closure ⟨hx, hxZ⟩)
  rcases hC.2.2 (C ∩ Z) (closure (C \ Z)) hCZ hK inter_subset_left hKC heq with h | h
  · exact False.elim (hnot (h ▸ inter_subset_right))
  · exact h.subset

/-- An irreducible analytic subset of a positive stratum which is not
  contained in `Z` meets `Z` only inside Hironaka's boundary. -/
theorem stratum_component_inter_subset_boundary
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (B W Z C : Set X.obj.left)
    (i : ℕ) (hC : X.IsIrreducibleAnalyticSubset C) (hZ : X.IsAnalyticSubset Z)
    (hCS : C ⊆ strata f B (i + 1)) (hCW : C ⊆ W) (hnot : ¬ C ⊆ Z) :
    C ∩ Z ⊆ closure ((strata f B (i + 1) ∩ W) \ Z) ∩ Z := by
  intro x hx
  refine ⟨?_, hx.2⟩
  apply closure_mono (show C \ Z ⊆ (strata f B (i + 1) ∩ W) \ Z from ?_)
    (subset_closure_diff_of_irreducible hC hZ hnot hx.1)
  intro y hy
  exact ⟨⟨hCS hy.1, hCW hy.1⟩, hy.2⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary
