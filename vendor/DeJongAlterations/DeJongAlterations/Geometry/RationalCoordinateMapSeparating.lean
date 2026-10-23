import DeJongAlterations.Geometry.RationalCoordinateMap
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Rational projections from actual separating transcendence bases

The source open, regular coordinates, coefficient map and dominant morphism
are those constructed by `RationalCoordinateMap`. A separating basis of the
canonical function field is enumerated internally; omitting its last member
gives an actual dominant rational projection and a remaining transcendental
field coordinate. No conclusion about scheme-theoretic fibres is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.RationalCoordinateMap

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- A finite separating basis of the actual function field can be enumerated by `Fin d`. -/
theorem exists_separating_family (p : X ⟶ Spec (.of k))
    (h : SeparableGenericSmoothness.FunctionFieldSeparablyGenerated p) :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    ∃ d : ℕ, ∃ r : Fin d → X.functionField, IsTranscendenceBasis k r ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range r)) X.functionField ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range r)) X.functionField := by
  classical
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  obtain ⟨s, hs, hsep⟩ := h
  let e := (Fintype.equivFin s).symm
  let r : Fin (Fintype.card s) → X.functionField := fun i ↦ (e i : X.functionField)
  have hb : IsTranscendenceBasis k r := hs.comp_equiv e
  have hrange : Set.range r = (s : Set X.functionField) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro ha
      obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨_, r, hb, ?_, hb.isAlgebraic_field⟩
  rw [hrange]
  exact hsep

/-- The full separating-coordinate map is an actual dominant morphism on a dense affine open. -/
theorem exists_separating_coordinate_map (p : X ⟶ Spec (.of k))
    (h : SeparableGenericSmoothness.FunctionFieldSeparablyGenerated p) :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    ∃ d : ℕ, ∃ r : Fin d → X.functionField, IsTranscendenceBasis k r ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range r)) X.functionField ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range r)) X.functionField ∧
      IsDominant (coordinateMap p r) := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  obtain ⟨d, r, hb, hs, ha⟩ := exists_separating_family p h
  exact ⟨d, r, hb, hs, ha, coordinateMap_isDominant p r hb.1⟩

/-- Omitting the last member of a separating basis gives the actual rational projection. -/
theorem exists_separating_projection (p : X ⟶ Spec (.of k))
    (h : SeparableGenericSmoothness.FunctionFieldSeparablyGenerated p)
    (htr : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      Algebra.Transcendental k X.functionField) :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    ∃ n : ℕ, ∃ r : Fin (n + 1) → X.functionField, IsTranscendenceBasis k r ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range r)) X.functionField ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range r)) X.functionField ∧
      IsDominant (coordinateMap p (fun i : Fin n ↦ r i.castSucc)) ∧
      Transcendental (IntermediateField.adjoin k (Set.range fun i : Fin n ↦ r i.castSucc))
        (r (Fin.last n)) := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  obtain ⟨d, r, hb, hs, ha⟩ := exists_separating_family p h
  have hd : d ≠ 0 := by
    intro hd
    subst d
    exact (Algebra.transcendental_iff_not_isAlgebraic.mp htr)
      (hb.isEmpty_iff_isAlgebraic.mp inferInstance)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  refine ⟨n, r, hb, hs, ha, coordinateMap_isDominant p _
    (hb.1.comp Fin.castSucc (Fin.castSucc_injective n)), ?_⟩
  apply IntermediateField.transcendental_adjoin_iff.mpr
  have hlast : Fin.last n ∉ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
    rintro ⟨i, hi⟩
    have heq := congrArg Fin.val hi
    simp only [Fin.val_castSucc, Fin.val_last] at heq
    exact (Nat.ne_of_lt i.isLt) heq
  have ht := hb.1.transcendental_adjoin hlast
  have hset : r '' Set.range (Fin.castSucc : Fin n → Fin (n + 1)) =
      Set.range (fun i : Fin n ↦ r i.castSucc) := by
    ext z
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, ⟨i, rfl⟩, rfl⟩
  rw [hset] at ht
  exact ht

end DeJongAlterations.Geometry.RationalCoordinateMap
