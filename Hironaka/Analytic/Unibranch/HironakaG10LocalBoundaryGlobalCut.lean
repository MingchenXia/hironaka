import Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticBoundary

/-! # Global cut of a boundary defined by local analytic data -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka

namespace Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticBoundary
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus

noncomputable section

/-- A locally analytic set is closed relative to its open domain. -/
theorem mem_of_mem_closure_inter_domain {X : SourceReducedComplexSpace}
    {V A : Set X.obj.left} (hV : IsOpen V) (hA : IsLocallyAnalyticOn X V A)
    {x : X.obj.left} (hxV : x ∈ V) (hx : x ∈ closure (A ∩ V)) : x ∈ A := by
  obtain ⟨e,⟨y,hy⟩,heV,_⟩ := LocalEmbedding.exists_domain x hV hxV
  have hclosed : IsClosed (e.toPoint ⁻¹' A) := by
    have h : IsClosed ((Subtype.val : e.carrier → e.ambient) ⁻¹'
        (Subtype.val '' (e.toPoint ⁻¹' A))) :=
      (analytic_image_local_trace hA e heV).isClosed.preimage continuous_subtype_val
    rwa [Set.preimage_image_eq _ Subtype.val_injective] at h
  have hycl : y ∈ closure (e.toPoint ⁻¹' (A ∩ V)) := by
    rw [← e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
      e.isOpenEmbedding_toPoint.continuous]
    change e.toPoint y ∈ closure (A ∩ V)
    rw [hy]
    exact hx
  have hyA : y ∈ e.toPoint ⁻¹' A := by
    rw [← hclosed.closure_eq]
    exact closure_mono (Set.preimage_mono inter_subset_left) hycl
  change e.toPoint y ∈ A at hyA
  rwa [hy] at hyA

/-- A closed set contained in the flattener domain cuts the local analytic
  boundary to a global analytic set; both source sets need only be locally
  analytic on that domain. -/
theorem analytic_global_cut_of_local_data {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B C : Set X.obj.left) (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1)))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V) :
    X.IsAnalyticSubset (C ∩ stratumBoundary f B Z.V Z.support i) := by
  intro x
  by_cases hxC : x ∈ C
  · obtain ⟨e,he,heV,A,hA,htrace⟩ := locallyAnalytic_stratumBoundary f B Z i hS x (hCV hxC)
    let AC : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' C)
    have hAC : IsComplexAnalyticSubset (n := e.dim) AC := analytic_image_local_trace hC e heV
    refine ⟨e,he,AC ∩ A,hAC.inter hA,?_⟩
    rw [Set.preimage_inter, htrace, Set.preimage_inter]
    dsimp [AC]
    rw [Set.preimage_image_eq _ Subtype.val_injective]
  · obtain ⟨e,he,heC,_⟩ := LocalEmbedding.exists_domain x hCclosed.isOpen_compl hxC
    refine ⟨e,he,∅,isComplexAnalyticSubset_empty,?_⟩
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => (heC ⟨y,rfl⟩) h.1

/-- On a compact base the global cut is compact and contained in the
  absolute non-flat image, with only local analytic data on the domain. -/
theorem compact_global_cut_of_local_data {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B C : Set X.obj.left) (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1)))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V) :
    IsCompact (C ∩ stratumBoundary f B Z.V Z.support i) ∧
      C ∩ stratumBoundary f B Z.V Z.support i ⊆ nonflatImage f := by
  refine ⟨(analytic_global_cut_of_local_data f B C Z i hS hC hCclosed hCV).isClosed.isCompact, ?_⟩
  intro x hx
  apply strata_succ_subset_nonflatImage f B i
  apply mem_of_mem_closure_inter_domain Z.isOpen hS (hCV hx.1)
  exact closure_mono (show (strata f B (i + 1) ∩ Z.V) \ Z.support ⊆
    strata f B (i + 1) ∩ Z.V from sdiff_subset) hx.2.1

end
end Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut
