import Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticDecomposition
import Mathlib.Order.Preorder.Finite

/-! # Actual irreducible components of compact analytic subsets -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticComponents
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticDecomposition
  Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

noncomputable section

/-- An irreducible analytic subset contained in a union of two analytic
  sets is contained in one of them. -/
theorem irreducible_subset_union {X : SourceReducedComplexSpace}
    {D A B : Set X.obj.left} (hD : X.IsIrreducibleAnalyticSubset D)
    (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) (hsub : D ⊆ A ∪ B) :
    D ⊆ A ∨ D ⊆ B := by
  have heq : D = (D ∩ A) ∪ (D ∩ B) := by
    ext x
    constructor
    · intro hx
      rcases hsub hx with ha | hb
      · exact Or.inl ⟨hx,ha⟩
      · exact Or.inr ⟨hx,hb⟩
    · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx
  rcases hD.2.2 (D ∩ A) (D ∩ B) (isAnalyticSubset_inter hD.1 hA)
      (isAnalyticSubset_inter hD.1 hB) inter_subset_left inter_subset_left heq with h | h
  · exact Or.inl (h ▸ inter_subset_right)
  · exact Or.inr (h ▸ inter_subset_right)

/-- An irreducible analytic set in a finite analytic union is contained in
  one member of that union. -/
theorem irreducible_subset_finite_union {X : SourceReducedComplexSpace}
    {D : Set X.obj.left} (hD : X.IsIrreducibleAnalyticSubset D)
    (s : Finset (Set X.obj.left)) (hs : ∀ A ∈ s, X.IsAnalyticSubset A)
    (hsub : D ⊆ ⋃ A ∈ s, A) : ∃ A ∈ s, D ⊆ A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨x,hx⟩ := hD.2.1
    have := hsub hx
    simp at this
  | @insert A s hAs ih =>
    have hA : X.IsAnalyticSubset A := hs A (Finset.mem_insert_self A s)
    have hs' : ∀ B ∈ s, X.IsAnalyticSubset B := fun B hB => hs B (Finset.mem_insert_of_mem hB)
    have htail : X.IsAnalyticSubset (⋃ B ∈ s, B) := by
      exact analytic_finite_biUnion (s : Set (Set X.obj.left)) s.finite_toSet id hs'
    have hcover : D ⊆ A ∪ (⋃ B ∈ s, B) := by
      intro x hx
      obtain ⟨B,h⟩ := mem_iUnion.mp (hsub hx)
      obtain ⟨hB,hxB⟩ := mem_iUnion.mp h
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact Or.inl hxB
      · exact Or.inr (mem_iUnion.mpr ⟨B,mem_iUnion.mpr ⟨hB,hxB⟩⟩)
    rcases irreducible_subset_union hD hA htail hcover with hDA | hDs
    · exact ⟨A,Finset.mem_insert_self A s,hDA⟩
    · obtain ⟨B,hB,hDB⟩ := ih hs' hDs
      exact ⟨B,Finset.mem_insert_of_mem hB,hDB⟩

/-- The actual maximal irreducible components of an analytic set. -/
def components (X : SourceReducedComplexSpace) (A : Set X.obj.left) : Set (Set X.obj.left) :=
  {C | X.IsIrreducibleAnalyticSubset C ∧ C ⊆ A ∧
    ∀ D, X.IsIrreducibleAnalyticSubset D → C ⊆ D → D ⊆ A → D = C}

/-- On a compact reduced complex space, the actual irreducible components
  of every analytic set are finite and cover that set. -/
theorem finite_components_and_cover (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] (A : Set X.obj.left) (hA : X.IsAnalyticSubset A) :
    (components X A).Finite ∧ ∀ x ∈ A, ∃ C ∈ components X A, x ∈ C := by
  classical
  obtain ⟨s,hs,hAeq⟩ := finite_irreducible_decomposition X A hA
  have hsA : ∀ C ∈ s, X.IsAnalyticSubset C := fun C hC => (hs C hC).1.1
  have hcompSub : components X A ⊆ (s : Set (Set X.obj.left)) := by
    intro C hC
    have hsub : C ⊆ ⋃ D ∈ s, D := hAeq ▸ hC.2.1
    obtain ⟨D,hDs,hCD⟩ := irreducible_subset_finite_union hC.1 s hsA hsub
    have heq : D = C := hC.2.2 D (hs D hDs).1 hCD (hs D hDs).2
    change C ∈ s
    simpa only [heq] using hDs
  refine ⟨s.finite_toSet.subset hcompSub,?_⟩
  intro x hxA
  have hxU : x ∈ ⋃ C ∈ s, C := hAeq ▸ hxA
  obtain ⟨C,hxC⟩ := mem_iUnion.mp hxU
  obtain ⟨hCs,hxC⟩ := mem_iUnion.mp hxC
  obtain ⟨D,hCD,hDmax⟩ := Finset.exists_le_maximal s hCs
  have hDs : D ∈ s := hDmax.1
  refine ⟨D,⟨(hs D hDs).1,(hs D hDs).2,?_⟩,hCD hxC⟩
  intro E hE hDE hEA
  have hsub : E ⊆ ⋃ F ∈ s, F := hAeq ▸ hEA
  obtain ⟨F,hFs,hEF⟩ := irreducible_subset_finite_union hE s hsA hsub
  have hDF : D ⊆ F := hDE.trans hEF
  have hFD : F ⊆ D := hDmax.2 hFs hDF
  exact Subset.antisymm (hEF.trans hFD) hDE

end
end Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticComponents
