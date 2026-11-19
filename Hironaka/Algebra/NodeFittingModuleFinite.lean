import Hironaka.Algebra.NodeFittingModuleInvariance

/-! # Finite generation of actual full intrinsic Fitting ideals over arbitrary rings -/

noncomputable section

namespace Hironaka.Algebra.NodeFittingMatrix

universe u v w
variable {R : Type u} [CommRing R] {m : Type v} {n : Type w}

/-- Every original minor is the image of a pair of actual finite index selections. -/
theorem minorSet_finite [Fintype m] [Fintype n] (k : ℕ) (A : Matrix m n R) :
    (minorSet k A).Finite := by
  classical
  let f : (Fin k → m) × (Fin k → n) → R := fun p => (A.submatrix p.1 p.2).det
  have h : minorSet k A = Set.range f := by
    ext x
    constructor
    · rintro ⟨r, c, he⟩
      exact ⟨(r, c), he⟩
    · rintro ⟨⟨r, c⟩, he⟩
      exact ⟨r, c, he⟩
  rw [h]
  exact Set.finite_range f

/-- The entire actual determinant ideal is finitely generated, with no Noetherian premise. -/
theorem determinantalIdeal_fg [Fintype m] [Fintype n] (k : ℕ) (A : Matrix m n R) :
    (determinantalIdeal k A).FG :=
  Submodule.fg_span (minorSet_finite k A)

end Hironaka.Algebra.NodeFittingMatrix

namespace Hironaka.Algebra.NodeFittingModule

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Finite generation of the ORIGINAL whole intrinsic ideal over EVERY original base ring. -/
theorem fittingIdeal_fg [Module.FinitePresentation R M] (i : ℕ) :
    (fittingIdeal (R := R) (M := M) i).FG := by
  let P := selectedPresentation (R := R) (M := M)
  rw [fittingIdeal_eq_presentationIdeal P i]
  exact NodeFittingMatrix.determinantalIdeal_fg _ _

end Hironaka.Algebra.NodeFittingModule
