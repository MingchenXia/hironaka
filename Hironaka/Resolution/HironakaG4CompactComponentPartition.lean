import Hironaka.Resolution.HironakaG4CompactComponentTasks

/-! Closed separation of compact and noncompact sharp-bad components. -/
set_option autoImplicit false
open Set TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactComponentPartition
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers GlobalComponents
  HironakaG4CompactComponentTasks
variable {n : ℕ} {X : CMfd.{u} n}

/-- The union of all noncompact irreducible components of the original bad set. -/
def noncompactComponentUnion (B : Set X) : Set X :=
  ⋃ K : {K : globalComponents (n := n) B // ¬ IsCompact K.val}, K.val.val

theorem isClosed_noncompactComponentUnion {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B) :
    IsClosed (noncompactComponentUnion B) := by
  unfold noncompactComponentUnion
  have hLF : LocallyFinite (fun K : {K : globalComponents (n := n) B // ¬ IsCompact K.val} => K.val.val) :=
    (locallyFinite_globalComponents hB).comp_injective Subtype.val_injective
  exact hLF.isClosed_iUnion (fun K =>
    (isComplexAnalyticallyIrreducible_of_mem_globalComponents hB K.val.property).1.isClosed)

theorem compact_noncompact_union {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B) :
    compactComponentUnion B ∪ noncompactComponentUnion B = B := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact compactComponentUnion_subset hB hx
    · obtain ⟨K,hK⟩ := mem_iUnion.mp hx
      exact subset_of_mem_globalComponents hB K.val.property hK
  · intro hx
    have hcover : x ∈ ⋃₀ globalComponents (n := n) B := by
      rw [sUnion_globalComponents hB]
      exact hx
    obtain ⟨C,hC,hxC⟩ := mem_sUnion.mp hcover
    let K : globalComponents (n := n) B := ⟨C,hC⟩
    by_cases hK : IsCompact K.val
    · exact Or.inl (mem_iUnion.mpr ⟨⟨K,hK⟩,hxC⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨K,hK⟩,hxC⟩)

theorem compact_noncompact_disjoint {B : Set X}
    (hdisj : Pairwise (fun C D : globalComponents (n := n) B => Disjoint C.val D.val)) :
    Disjoint (compactComponentUnion B) (noncompactComponentUnion B) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨K,hK⟩ := mem_iUnion.mp hx
  obtain ⟨L,hL⟩ := mem_iUnion.mp hy
  have hne : K.val ≠ L.val := by
    intro h
    apply L.property
    rw [←h]
    exact K.property
  exact Set.disjoint_left.mp (hdisj hne) hK hL

/-- The complement of the noncompact components is an open region in which
all original bad points belong to the compact-component union. -/
theorem compact_only_bad_slice {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B)
    (hdisj : Pairwise (fun C D : globalComponents (n := n) B => Disjoint C.val D.val)) :
    IsOpen (noncompactComponentUnion B)ᶜ ∧
      B ∩ (noncompactComponentUnion B)ᶜ = compactComponentUnion B := by
  refine ⟨(isClosed_noncompactComponentUnion hB).isOpen_compl,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hnot⟩
    have : x ∈ compactComponentUnion B ∪ noncompactComponentUnion B := by
      rw [compact_noncompact_union hB]
      exact hx
    exact this.resolve_right hnot
  · intro hx
    refine ⟨compactComponentUnion_subset hB hx,?_⟩
    intro hy
    exact Set.disjoint_left.mp (compact_noncompact_disjoint hdisj) hx hy
end
end Hironaka.HironakaG4CompactComponentPartition
