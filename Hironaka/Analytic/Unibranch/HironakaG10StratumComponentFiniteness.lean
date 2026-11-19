import Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticComponents

/-! # Finite and covering actual stratum components -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10StratumComponentFiniteness
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10CompactAnalyticComponents

noncomputable section

/-- Actual analytic strata on a compact base are covered by their genuine
  maximal irreducible analytic components. -/
theorem stratum_component_coverage {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j)) :
    ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C := by
  intro j x hx
  obtain ⟨_,hcover⟩ := finite_components_and_cover X (strata f B j) (hA j)
  obtain ⟨C,hC,hxC⟩ := hcover x hx
  exact ⟨C,hC,hxC⟩

/-- The full collection of indexed actual stratum components below an
  empty terminal stratum is finite. -/
theorem indexed_stratum_components_finite {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j)) (N : ℕ)
    (hN : strata f B N = ∅) :
    {jC : ℕ × Set X.obj.left | IsStratumComponent f B jC.1 jC.2}.Finite := by
  let S : Set (ℕ × Set X.obj.left) :=
    ⋃ j ∈ (Finset.range N : Set ℕ), (fun C : Set X.obj.left => (j,C)) ''
      components X (strata f B j)
  have hS : S.Finite := (Finset.range N).finite_toSet.biUnion fun j _ =>
    ((finite_components_and_cover X (strata f B j) (hA j)).1).image _
  apply hS.subset
  intro jC hjC
  have hanti : Antitone (strata f B) := antitone_nat_of_succ_le (strata_succ_subset f B)
  have hj : jC.1 < N := by
    by_contra hn
    have hsub : strata f B jC.1 ⊆ strata f B N := hanti (Nat.le_of_not_gt hn)
    obtain ⟨x,hx⟩ := hjC.1.2.1
    have hx' : x ∈ strata f B N := hsub (hjC.2.1 hx)
    rw [hN] at hx'
    exact hx'
  dsimp [S]
  refine mem_iUnion.mpr ⟨jC.1,mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,?_⟩⟩
  exact ⟨jC.2,hjC,Prod.mk.eta⟩

/-- Consequently the actual selected source components are finite; no
  independent component-finiteness assumption is needed. -/
theorem selectedHigherComponents_finite {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → Set X.obj.left) (i : ℕ)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j)) (N : ℕ)
    (hN : strata f B N = ∅) : (selectedHigherComponents f B Z i).Finite :=
  (indexed_stratum_components_finite f B hA N hN).subset (fun _ h => h.2.1)

/-- The actual bad component set is finite under the same hypotheses. -/
theorem badComponents_finite {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → Set X.obj.left)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j)) (N : ℕ)
    (hN : strata f B N = ∅) : (badComponents f B Z).Finite :=
  (indexed_stratum_components_finite f B hA N hN).subset (fun _ h => h.2.1)

/-- The actual bad-component indices have one finite upper bound. -/
theorem exists_badComponents_index_bound {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → Set X.obj.left)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j)) (N : ℕ)
    (hN : strata f B N = ∅) :
    ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i := by
  obtain ⟨i,hi⟩ := ((badComponents_finite f B Z hA N hN).image Prod.fst).bddAbove
  exact ⟨i,fun jC hjC => hi ⟨jC,hjC,rfl⟩⟩

/-- Analyticity and nonstationarity of nonempty actual strata yield all of
  the finite-depth and genuine-component inputs used by the source centre
  construction. -/
theorem exists_finite_depth_component_data {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → Set X.obj.left)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j))
    (hproper : ∀ n, (strata f B n).Nonempty → strata f B (n + 1) ≠ strata f B n) :
    ∃ N i, strata f B N = ∅ ∧
      (∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C) ∧
      (∀ k, (selectedHigherComponents f B Z k).Finite) ∧
      (badComponents f B Z).Finite ∧
      ∀ jC ∈ badComponents f B Z, jC.1 ≤ i := by
  obtain ⟨N,hN⟩ :=
    Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether.exists_empty_stratum_of_analytic_no_fixed
      f B hA hproper
  obtain ⟨i,hi⟩ := exists_badComponents_index_bound f B Z hA N hN
  exact ⟨N,i,hN,stratum_component_coverage f B hA,
    fun k => selectedHigherComponents_finite f B Z k hA N hN,
    badComponents_finite f B Z hA N hN,hi⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10StratumComponentFiniteness
