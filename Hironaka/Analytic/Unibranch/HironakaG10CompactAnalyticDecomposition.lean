import Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether
import Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary
import Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
import Mathlib.Order.WellFounded

/-! # Finite irreducible decomposition on a compact reduced complex space -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticDecomposition
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether
  Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

noncomputable section

/-- The proper-subset relation on the actual analytic subsets of a compact
  reduced complex space is well founded. -/
theorem wellFounded_analytic_ssubset (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] :
    WellFounded (fun A B : {A : Set X.obj.left // X.IsAnalyticSubset A} => A.val ⊂ B.val) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨F,hF⟩
  obtain ⟨N,hN⟩ := analytic_descending_stationary_on_compact X
    (fun n => (F n).val) (fun n => (F n).property) (fun n => (hF n).subset) univ isCompact_univ
  have heq : (F (N + 1)).val = (F N).val := by
    simpa only [univ_inter] using hN (N + 1) (Nat.le_succ N)
  exact (hF N).ne heq

/-- Every actual analytic subset of a compact reduced complex space is the
  union of finitely many actual irreducible analytic subsets. -/
theorem finite_irreducible_decomposition (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] (A : Set X.obj.left) (hA : X.IsAnalyticSubset A) :
    ∃ s : Finset (Set X.obj.left),
      (∀ C ∈ s, X.IsIrreducibleAnalyticSubset C ∧ C ⊆ A) ∧
      A = ⋃ C ∈ s, C := by
  classical
  let P (A : {A : Set X.obj.left // X.IsAnalyticSubset A}) : Prop :=
    ∃ s : Finset (Set X.obj.left),
      (∀ C ∈ s, X.IsIrreducibleAnalyticSubset C ∧ C ⊆ A.val) ∧
      A.val = ⋃ C ∈ s, C
  have hall : ∀ A, P A := by
    intro A
    apply (wellFounded_analytic_ssubset X).induction A
    intro A ih
    by_cases hempty : A.val = ∅
    · refine ⟨∅,by simp,?_⟩
      simp [hempty]
    · have hnon : A.val.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
      by_cases hirr : X.IsIrreducibleAnalyticSubset A.val
      · refine ⟨{A.val},?_,?_⟩
        · simp [hirr]
        · simp
      · have hsplit : ∃ B C : Set X.obj.left,
            X.IsAnalyticSubset B ∧ X.IsAnalyticSubset C ∧ B ⊆ A.val ∧ C ⊆ A.val ∧
            A.val = B ∪ C ∧ A.val ≠ B ∧ A.val ≠ C := by
          unfold IsIrreducibleAnalyticSubset at hirr
          simp only [A.property,hnon,true_and] at hirr
          push Not at hirr
          exact hirr
        obtain ⟨B,C,hB,hC,hBA,hCA,hunion,hneB,hneC⟩ := hsplit
        let B' : {A : Set X.obj.left // X.IsAnalyticSubset A} := ⟨B,hB⟩
        let C' : {A : Set X.obj.left // X.IsAnalyticSubset A} := ⟨C,hC⟩
        have hB' : B'.val ⊂ A.val := ⟨hBA,fun h => hneB (Subset.antisymm h hBA)⟩
        have hC' : C'.val ⊂ A.val := ⟨hCA,fun h => hneC (Subset.antisymm h hCA)⟩
        obtain ⟨s,hs,hseq⟩ := ih B' hB'
        obtain ⟨t,ht,hteq⟩ := ih C' hC'
        refine ⟨s ∪ t,?_,?_⟩
        · intro D hD
          rcases Finset.mem_union.mp hD with hD | hD
          · exact ⟨(hs D hD).1,(hs D hD).2.trans hBA⟩
          · exact ⟨(ht D hD).1,(ht D hD).2.trans hCA⟩
        · change B = ⋃ D ∈ s, D at hseq
          change C = ⋃ D ∈ t, D at hteq
          rw [hunion,hseq,hteq]
          ext x
          simp only [mem_union,mem_iUnion,Finset.mem_union]
          constructor
          · rintro (⟨D,hD,hx⟩ | ⟨D,hD,hx⟩)
            · exact ⟨D,Or.inl hD,hx⟩
            · exact ⟨D,Or.inr hD,hx⟩
          · rintro ⟨D,(hD | hD),hx⟩
            · exact Or.inl ⟨D,hD,hx⟩
            · exact Or.inr ⟨D,hD,hx⟩
  exact hall ⟨A,hA⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticDecomposition
