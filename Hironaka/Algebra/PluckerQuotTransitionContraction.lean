import Hironaka.Algebra.PluckerQuotTransitionMatrix

/-!
# The original global-coordinate contraction has its actual local split factor

Every entry is the original replacement minor. Cramer's identity constructs
the factor from the actual adjugates. The original identity pivot rows give
a literal left inverse over the entire original coefficient ring.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι η : Type u} [Fintype ι] [DecidableEq ι]

/-- Every original replacement minor is the actual corresponding adjugate row applied to the same column. -/
theorem replacementMinor_eq_adjugate_mul (M : Matrix ι η R) (s : ι → η) (i : ι) (a : η) :
    columnMinor M (Function.update s i a) = ((selectedMatrix M s).adjugate * M) i a := by
  rw [columnMinor, ← updateCol_selectedMatrix, ← Matrix.cramer_apply,
    Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- The literal original-coordinate contraction matrix, retaining all selectors, rows, and free columns. -/
def originalContractionMatrix {σ : Type v} (β : σ → ι → η) (M : Matrix ι η R) :
    Matrix (σ × ι) η R :=
  fun row a ↦ columnMinor M (Function.update (β row.1) row.2 a)

/-- The actual factor built from the original selected-column adjugates. -/
def originalContractionFactor {σ : Type v} (β : σ → ι → η) (M : Matrix ι η R) :
    Matrix (σ × ι) ι R :=
  fun row i ↦ (selectedMatrix M (β row.1)).adjugate row.2 i

/-- The entire original contraction factors through the same actual original quotient matrix. -/
theorem originalContractionMatrix_eq_factor_mul {σ : Type v} (β : σ → ι → η) (M : Matrix ι η R) :
    originalContractionMatrix β M = originalContractionFactor β M * M := by
  ext row a
  exact replacementMinor_eq_adjugate_mul M (β row.1) row.2 a

/-- The actual original pivot rows of the same factor are the literal identity, providing its left inverse. -/
theorem originalContractionFactor_pivot_rows {σ : Type v} {κ : Type u}
    [Fintype κ] [DecidableEq κ] (β : σ ≃ (ι → η)) (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R) :
    (originalContractionFactor β (splitNormalizedMatrix e a)).submatrix
      (fun i ↦ (β.symm (e ∘ Sum.inl), i)) id = 1 := by
  ext i j
  change (selectedMatrix (splitNormalizedMatrix e a) (β (β.symm (e ∘ Sum.inl)))).adjugate i j =
    (1 : Matrix ι ι R) i j
  rw [β.apply_symm_apply, selectedMatrix_splitNormalized_pivot, Matrix.adjugate_one]

end Hironaka.Algebra.PluckerQuot
