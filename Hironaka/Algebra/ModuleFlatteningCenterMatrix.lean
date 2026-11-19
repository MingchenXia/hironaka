import Hironaka.Algebra.ModuleFlatteningMinorsCoordinates

/-!
# The same original maximal-minor ideal under coefficient maps and basis factorization

These algebraic identities keep the original column selector family and
the exact original whole ideal. A literal factorization through an actual
selected column block proves principality without radical replacement.
-/

noncomputable section

open Module

namespace Hironaka.Algebra.ModuleFlatteningCenter

open ModuleFlatteningMinors

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S] {n r : ℕ}

/-- Mapping the original coefficients maps each original selected minor exactly. -/
theorem columnMinor_map (f : R →+* S) (V : Matrix (Fin r) (Fin n) R)
    (s : Fin r → Fin n) : columnMinor (V.map f) s = f (columnMinor V s) := by
  exact (f.map_det (selectedMatrix V s)).symm

/-- The same original minor ideal commutes exactly with original coefficient extension. -/
theorem minorIdeal_map (f : R →+* S) (V : Matrix (Fin r) (Fin n) R) :
    minorIdeal (V.map f) = (minorIdeal V).map f := by
  rw [minorIdeal, minorIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext s
  exact columnMinor_map f V s

/-- An actual selected-column factorization makes the same original minor ideal principal. -/
theorem minorIdeal_eq_span_of_selected_factorization
    (V : Matrix (Fin r) (Fin n) R) (s : Fin r → Fin n)
    (C : Matrix (Fin r) (Fin n) R) (hV : V = selectedMatrix V s * C) :
    minorIdeal V = Ideal.span ({columnMinor V s} : Set R) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    have ht : selectedMatrix V t = selectedMatrix V s * selectedMatrix C t := by
      ext i j
      exact congrArg (fun W : Matrix (Fin r) (Fin n) R ↦ W i (t j)) hV
    change Matrix.det (selectedMatrix V t) ∈ _
    rw [ht, Matrix.det_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact columnMinor_mem_minorIdeal V s

end Hironaka.Algebra.ModuleFlatteningCenter
