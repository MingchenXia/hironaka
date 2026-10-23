import DeJongAlterations.Geometry.FiberDimensionCurveComponents

/-! # An actual isolated point from a zero-dimensional irreducible component -/

noncomputable section

open TopologicalSpace

namespace DeJongAlterations.Geometry.FiberComponentIsolation

universe u

/-- Every actual zero-dimensional component of a Noetherian `T₀` space contains an open point. -/
theorem exists_isOpen_singleton_of_component_dimension_le_zero
    (T : Type u) [TopologicalSpace T] [T0Space T] [NoetherianSpace T]
    (Z : Set T) (hZ : Z ∈ irreducibleComponents T)
    (hdim : topologicalKrullDim Z ≤ 0) : ∃ z ∈ Z, IsOpen ({z} : Set T) := by
  have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ.1
  have : Subsingleton Z :=
    FiberDimensionCurveComponents.subsingleton_of_irreducible_dimension_le_zero Z hdim
  obtain ⟨o, ho, ⟨z, hzo⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  have heq : o = {z} := by
    apply Set.Subset.antisymm
    · intro w hw
      exact Set.mem_singleton_iff.mpr
        (congrArg Subtype.val (Subsingleton.elim (⟨w, hoZ hw⟩ : Z) ⟨z, hoZ hzo⟩))
    · rintro w rfl
      exact hzo
  exact ⟨z, hoZ hzo, heq ▸ ho⟩

end DeJongAlterations.Geometry.FiberComponentIsolation
