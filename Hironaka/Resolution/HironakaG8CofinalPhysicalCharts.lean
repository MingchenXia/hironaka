import Hironaka.Resolution.HironakaG8NoncompactInitialBoundaryAtlas

/-! # Cofinal compact-enclosed physical charts on the same glued projection -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CofinalPhysicalCharts

open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG8NoncompactInitialBoundaryAtlas HironakaEmbeddedAnalytic NormalCrossings

/-- A projection with physical charts on all compact-enclosed windows
has nested precompact charts cofinal among all compact base subsets. -/
theorem exists_cofinal_physical_charts {n : ℕ} {X Z : CMfd.{0} n}
    {K : LocalTowerClass X} {P : Z → X}
    (hChart : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ c : TowerChart K Z P, c.U = U) :
    ∃ c : ℕ → TowerChart K Z P,
      Monotone (fun i => (c i).U) ∧
      (∀ i, IsCompact (closure ((c i).U : Set X))) ∧
      (∀ i, closure ((c i).U : Set X) ⊆ ((c (i+1)).U : Set X)) ∧
      (∀ L : Set X, IsCompact L → ∃ i, L ⊆ ((c i).U : Set X)) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let L := CompactExhaustion.choice X
  let U (i : ℕ) : Opens X := ⟨interior (L i),isOpen_interior⟩
  choose c hc using fun i => hChart (U i) (L i) (L.isCompact i) interior_subset
  have hBound (i : ℕ) : closure ((c i).U : Set X) ⊆ L i := by
    rw [hc]
    exact closure_minimal interior_subset (L.isCompact i).isClosed
  refine ⟨c,?_,fun i => (L.isCompact i).of_isClosed_subset isClosed_closure (hBound i),?_,?_⟩
  · intro i j h
    change (c i).U ≤ (c j).U
    rw [hc i,hc j]
    exact interior_mono (L.subset h)
  · intro i
    rw [hc (i+1)]
    exact (hBound i).trans (L.subset_interior_succ i)
  · intro S hS
    obtain ⟨i,hi⟩ := L.exists_superset_of_isCompact hS
    refine ⟨i+1,?_⟩
    rw [hc]
    exact hi.trans (L.subset_interior_succ i)

/-- The certified arbitrary-initial-SNC positive-dimensional construction
gives the cofinal physical charts over one and the same resolution map. -/
theorem exists_ordered_initial_boundary_cofinal_physical_charts
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      ∃ c : ℕ → TowerChart (orderedInitialBoundaryClass W E) Z P,
        Monotone (fun i => (c i).U) ∧
        (∀ i, IsCompact (closure ((c i).U : Set X))) ∧
        (∀ i, closure ((c i).U : Set X) ⊆ ((c (i+1)).U : Set X)) ∧
        (∀ L : Set X, IsCompact L → ∃ i, L ⊆ ((c i).U : Set X)) := by
  obtain ⟨Z,P,hGlued,hWindows,-,-⟩ := exists_locally_finite_initial_boundary_atlas hW hE hDense
  exact ⟨Z,P,hGlued,exists_cofinal_physical_charts hWindows⟩

end Hironaka.HironakaG8CofinalPhysicalCharts
