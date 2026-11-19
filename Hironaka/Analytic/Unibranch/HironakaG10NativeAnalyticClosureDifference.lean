import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticSubsets
import Hironaka.Analytic.ClosureDifferenceAnalytic

/-! # Closure differences of native analytic subsets -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces

namespace Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

noncomputable section

/-- In any local embedding, the image of the trace of a native analytic
  subset is analytic in the ambient manifold. -/
theorem analytic_image_trace {X : SourceReducedComplexSpace} {A : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (e : LocalEmbedding X) :
    IsComplexAnalyticSubset (n := e.dim)
      (Subtype.val '' (e.toPoint ⁻¹' A) : Set e.ambient) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro u
  by_cases hu : u ∈ e.carrier
  · obtain ⟨O, huO, A', hA', hiff⟩ := hA.exists_local_trace e ⟨u, hu⟩
    refine ⟨O, huO, ?_⟩
    have hCO : IsComplexAnalyticSubset (n := e.dim) ((↑) ⁻¹' e.carrier : Set O) :=
      AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O
    have heq : ((↑) ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' A)) : Set O) =
        A' ∩ ((↑) ⁻¹' e.carrier : Set O) := by
      ext o
      constructor
      · rintro ⟨a, ha, hao⟩
        have hoC : (o : e.ambient) ∈ e.carrier := hao ▸ a.property
        refine ⟨?_, hoC⟩
        apply (hiff ⟨o.val, hoC⟩ o.property).mp
        have : (⟨o.val, hoC⟩ : e.carrier) = a := Subtype.ext hao.symm
        rw [this]
        exact ha
      · rintro ⟨ho, hoC⟩
        exact ⟨⟨o.val, hoC⟩, (hiff ⟨o.val, hoC⟩ o.property).mpr ho, rfl⟩
    rw [heq]
    exact hA'.inter hCO
  · refine ⟨⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩, hu, ?_⟩
    have he : ((↑) ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' A)) :
        Set (⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩ : Opens e.ambient)) = ∅ := by
      ext o
      simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro a _ hao
      exact o.property (hao ▸ a.property)
    rw [he]
    exact isComplexAnalyticSubset_empty

/-- The closure of the difference of two native analytic subsets is analytic. -/
theorem isAnalyticSubset_closure_diff {X : SourceReducedComplexSpace}
    {A B : Set X.obj.left} (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) :
    X.IsAnalyticSubset (closure (A \ B)) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  let SA : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' A)
  let SB : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' B)
  have hSA : IsComplexAnalyticSubset (n := e.dim) SA := analytic_image_trace hA e
  have hSB : IsComplexAnalyticSubset (n := e.dim) SB := analytic_image_trace hB e
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x, closure (SA \ SB),
    ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff hSA hSB, ?_⟩
  rw [e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
    e.isOpenEmbedding_toPoint.continuous]
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  congr 1
  dsimp [SA, SB]
  rw [Set.image_sdiff Subtype.val_injective]


/-- Identity principle for native irreducible analytic subsets: an analytic
  subset containing a nonempty relatively open part of an irreducible
  analytic set contains the whole set. -/
theorem eq_of_subset_of_inter_open_subset {X : SourceReducedComplexSpace}
    {V Z : Set X.obj.left} (hV : X.IsAnalyticSubset V)
    (hZ : X.IsIrreducibleAnalyticSubset Z) (hVZ : V ⊆ Z) {O : Set X.obj.left}
    (hO : IsOpen O) (hne : (Z ∩ O).Nonempty) (hsub : Z ∩ O ⊆ V) : V = Z := by
  have hC := isAnalyticSubset_closure_diff hZ.1 hV
  have hCZ : closure (Z \ V) ⊆ Z := closure_minimal sdiff_subset hZ.1.isClosed
  have hZVC : Z = V ∪ closure (Z \ V) := by
    refine Subset.antisymm (fun z hz => ?_) (union_subset hVZ hCZ)
    by_cases hzV : z ∈ V
    · exact Or.inl hzV
    · exact Or.inr (subset_closure ⟨hz, hzV⟩)
  rcases hZ.2.2 V (closure (Z \ V)) hV hC hVZ hCZ hZVC with h | h
  · exact h.symm
  · exfalso
    obtain ⟨y, hyZ, hyO⟩ := hne
    obtain ⟨z, hzO, hzZ, hzV⟩ := mem_closure_iff.mp (h.subset hyZ) O hO hyO
    exact hzV (hsub ⟨hzZ, hzO⟩)

end
end Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
