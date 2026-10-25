import DeJongAlterations.Geometry.FiberDimensionComponentLowerBound

/-!
# Actual irreducible-closed chains and closed-cover dimension

Restriction of the original irreducible closed subsets preserves strict
chains when their original supports lie in the selected subspace. This
bounds heights and proves the dimension formulas needed for proper fibers.
-/

noncomputable section

open TopologicalSpace Topology Order

namespace DeJongAlterations.Geometry.FiberDimensionUpperSemicontinuityClosedCover

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type u} [TopologicalSpace T]

/-- An actual irreducible closed subset restricts to any subspace containing it. -/
def restrictIrreducibleClosed (Z : Set T) (C : IrreducibleCloseds T)
    (hCZ : (C : Set T) ⊆ Z) : IrreducibleCloseds Z where
  carrier := Subtype.val ⁻¹' (C : Set T)
  isClosed' := C.isClosed.preimage continuous_subtype_val
  isIrreducible' := by
    let e : (Subtype.val ⁻¹' (C : Set T) : Set Z) ≃ₜ C :=
      IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by
        intro x hx
        exact ⟨⟨x, hCZ hx⟩, rfl⟩)
    let : IrreducibleSpace C := Subtype.irreducibleSpace C.isIrreducible
    exact isIrreducible_iff_irreducibleSpace.mpr (e.irreducibleSpace_iff.mpr inferInstance)

/-- Original irreducible-closed height is bounded by any actual containing subspace. -/
theorem height_le_dimension_of_subset (Z : Set T) (C : IrreducibleCloseds T)
    (hCZ : (C : Set T) ⊆ Z) : (Order.height C : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  let r : Set.Iic C → IrreducibleCloseds Z := fun D ↦
    restrictIrreducibleClosed Z D.val (D.property.trans hCZ)
  have hr : StrictMono r := by
    intro D E hDE
    refine lt_of_le_not_ge (fun x hx ↦ hDE.le hx) ?_
    intro hED
    apply hDE.not_ge
    intro x hx
    have hx' : (⟨x, (E.property.trans hCZ) hx⟩ : Z) ∈ (r E : Set Z) := hx
    exact hED hx'
  rw [Order.height_eq_krullDim_Iic]
  exact Order.krullDim_le_of_strictMono r hr

/-- Native finite closed covers bound the full actual topological dimension. -/
theorem topologicalKrullDim_le_of_finite_closed_cover
    (Z : Finset (Set T)) (hclosed : ∀ C ∈ Z, IsClosed C)
    (hcover : (Set.univ : Set T) ⊆ ⋃₀ (Z : Set (Set T)))
    (d : WithBot ℕ∞) (hdim : ∀ C ∈ Z, topologicalKrullDim C ≤ d) :
    topologicalKrullDim T ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  apply iSup_le
  intro C
  obtain ⟨D, hD, hCD⟩ := isIrreducible_iff_sUnion_isClosed.mp C.isIrreducible Z hclosed
    ((Set.subset_univ _).trans hcover)
  exact (height_le_dimension_of_subset D C hCD).trans (hdim D hD)

/-- Actual irreducible-component dimensions compute the full dimension, with no supplied bound. -/
theorem topologicalKrullDim_eq_iSup_componentDimension :
    topologicalKrullDim T = ⨆ Z : irreducibleComponents T, topologicalKrullDim Z.val := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
    apply iSup_le
    intro C
    obtain ⟨Z, hZ, hCZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (C : Set T) C.isIrreducible
    exact (height_le_dimension_of_subset Z C hCZ).trans
      (le_iSup (fun Z : irreducibleComponents T ↦ topologicalKrullDim Z.val) ⟨Z, hZ⟩)
  · apply iSup_le
    intro Z
    exact topologicalKrullDim_subspace_le T Z.val

end DeJongAlterations.Geometry.FiberDimensionUpperSemicontinuityClosedCover
