import Hironaka.Algebra.PluckerQuotChart
import Hironaka.Algebra.PluckerQuotMinors

/-!
# Exact pivot and replacement minors of the original normalized quotient

The original free coordinates are preserved through an actual index splitting.
The same quotient matrix has identity pivot block and its replacement minors
are exactly the original entries, over arbitrary commutative rings.
-/

noncomputable section

open scoped Matrix

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι κ η : Type u}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The original normalized quotient matrix in its original free coordinates. -/
def normalizedMatrix (a : Matrix ι κ R) : Matrix ι (ι ⊕ κ) R :=
  fun i k ↦ matrixQuotient a (Pi.single k 1) i

omit [Fintype ι] in
@[simp]
theorem normalizedMatrix_inl (a : Matrix ι κ R) (i k : ι) :
    normalizedMatrix a i (Sum.inl k) = (1 : Matrix ι ι R) i k := by
  simp [normalizedMatrix, Matrix.one_apply, Pi.single_apply, eq_comm]

omit [Fintype ι] in
@[simp]
theorem normalizedMatrix_inr (a : Matrix ι κ R) (i : ι) (j : κ) :
    normalizedMatrix a i (Sum.inr j) = a i j := by
  exact congrFun (matrixQuotient_single_inr a j) i

/-- The exact same matrix in the original coordinates of an actual coordinate splitting. -/
def splitNormalizedMatrix (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R) : Matrix ι η R :=
  fun i k ↦ normalizedMatrix a i (e.symm k)

omit [Fintype ι] in
@[simp]
theorem splitNormalizedMatrix_apply (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R)
    (i : ι) (k : ι ⊕ κ) : splitNormalizedMatrix e a i (e k) = normalizedMatrix a i k := by
  simp [splitNormalizedMatrix]

omit [Fintype ι] in
/-- The original selected pivot block is literally the identity matrix. -/
theorem selectedMatrix_splitNormalized_pivot (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R) :
    selectedMatrix (splitNormalizedMatrix e a) (e ∘ Sum.inl) = 1 := by
  ext i k
  simp [selectedMatrix]

/-- The literal original pivot minor is exactly one. -/
theorem columnMinor_splitNormalized_pivot (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R) :
    columnMinor (splitNormalizedMatrix e a) (e ∘ Sum.inl) = 1 := by
  rw [columnMinor, selectedMatrix_splitNormalized_pivot, Matrix.det_one]

/-- The literal original replacement minor is exactly the original matrix entry. -/
theorem columnMinor_splitNormalized_replacement (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R)
    (i : ι) (j : κ) :
    columnMinor (splitNormalizedMatrix e a)
      (Function.update (e ∘ Sum.inl) i (e (Sum.inr j))) = a i j := by
  rw [columnMinor, ← updateCol_selectedMatrix]
  rw [← Matrix.cramer_apply, selectedMatrix_splitNormalized_pivot,
    Matrix.cramer_eq_adjugate_mulVec, Matrix.adjugate_one, Matrix.one_mulVec]
  simp

/-- Every original replacement minor, for any original free column, is its exact quotient entry. -/
theorem columnMinor_splitNormalized_replacement_any (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R)
    (i : ι) (k : η) :
    columnMinor (splitNormalizedMatrix e a)
      (Function.update (e ∘ Sum.inl) i k) = splitNormalizedMatrix e a i k := by
  rw [columnMinor, ← updateCol_selectedMatrix]
  rw [← Matrix.cramer_apply, selectedMatrix_splitNormalized_pivot,
    Matrix.cramer_eq_adjugate_mulVec, Matrix.adjugate_one, Matrix.one_mulVec]

end Hironaka.Algebra.PluckerQuot
