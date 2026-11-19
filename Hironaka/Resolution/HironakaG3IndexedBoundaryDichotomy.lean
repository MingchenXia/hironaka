import Hironaka.Resolution.HironakaG3MixedComponentOpen
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedBoundaryDichotomy
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3MixedComponentOpen

/-- An analytically irreducible component not contained in any member of a
locally finite analytic family is dense away from the entire indexed union. -/
theorem irreducible_dense_off_locally_finite {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    {C : Set X} (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (D : ι → Set X) (hD : LocallyFinite D)
    (hDa : ∀ i, IsComplexAnalyticSubset (n := n) (D i))
    (hNot : ∀ i, ¬ C ⊆ D i) : C ⊆ closure (C \ ⋃ i, D i) := by
  intro x hx
  obtain ⟨A,hAx,hAfin⟩ := hD x
  obtain ⟨O,hOA,hOo,hxO⟩ := mem_nhds_iff.mp hAx
  let s := hAfin.toFinset
  let E : List (Set X) := s.toList.map D
  have hEa : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H := by
    intro H hH
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    exact hDa i
  have hENot : ∀ H ∈ E, ¬ C ⊆ H := by
    intro H hH
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    exact hNot i
  have hDense := irreducible_dense_off_list hC E hEa hENot
  have hClose : x ∈ closure ((C \ ⋃ H ∈ E, H) ∩ O) :=
    hOo.closure_inter ⟨hDense hx,hxO⟩
  apply closure_mono (show (C \ ⋃ H ∈ E, H) ∩ O ⊆ C \ ⋃ i, D i from ?_) hClose
  rintro y ⟨⟨hyC,hyNot⟩,hyO⟩
  refine ⟨hyC,?_⟩
  intro hyUnion
  obtain ⟨i,hyD⟩ := Set.mem_iUnion.mp hyUnion
  have hi : i ∈ s := hAfin.mem_toFinset.mpr ⟨y,hyD,hOA hyO⟩
  apply hyNot
  exact Set.mem_iUnion₂.mpr ⟨D i,List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩,hyD⟩

/-- Every irreducible component is either contained in one boundary member or
dense away from the entire locally finite boundary support. -/
theorem irreducible_locally_finite_boundary_dichotomy {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    {C : Set X} (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (D : ι → Set X) (hD : LocallyFinite D)
    (hDa : ∀ i, IsComplexAnalyticSubset (n := n) (D i)) :
    (∃ i, C ⊆ D i) ∨ C ⊆ closure (C \ ⋃ i, D i) := by
  by_cases h : ∃ i, C ⊆ D i
  · exact Or.inl h
  · exact Or.inr (irreducible_dense_off_locally_finite hC D hD hDa (by simpa using h))
end
end Hironaka.HironakaG3IndexedBoundaryDichotomy
