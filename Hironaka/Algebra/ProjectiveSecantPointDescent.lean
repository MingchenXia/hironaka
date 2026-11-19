import Hironaka.Algebra.ProjectiveSecantSeparablePoint
import Mathlib.RingTheory.FiniteType

/-!
# The entire original algebra point descends to its internally chosen finite separable coefficient field
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveSecant

universe u

/-- Internally adjoin the actual images of finitely many original algebra generators and restrict the whole original point, retaining its literal entire inclusion triangle. -/
theorem exists_finite_separable_point_descent
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (χ : A →ₐ[k] SeparableClosure k) :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ ∃ χL : A →ₐ[k] L, L.val.comp χL = χ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  let L := IntermediateField.adjoin k (χ '' (s : Set A))
  let := (s.finite_toSet.image χ).fintype
  have hfin : FiniteDimensional k L := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsSeparable.isIntegral k x)
  have hgen : (s : Set A) ⊆ L.toSubalgebra.comap χ := by
    intro x hx
    exact IntermediateField.subset_adjoin k _ ⟨x, hx, rfl⟩
  have htop : (⊤ : Subalgebra k A) ≤ L.toSubalgebra.comap χ := by
    rw [← hs]
    exact Algebra.adjoin_le hgen
  have hχ : ∀ x, χ x ∈ L.toSubalgebra := fun x => htop (by trivial : x ∈ (⊤ : Subalgebra k A))
  refine ⟨L, hfin, inferInstance, χ.codRestrict L.toSubalgebra hχ, ?_⟩
  exact AlgHom.val_comp_codRestrict χ L.toSubalgebra hχ

end Hironaka.Algebra.ProjectiveSecant
