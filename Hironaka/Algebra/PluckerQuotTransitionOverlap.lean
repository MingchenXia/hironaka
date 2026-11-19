import Hironaka.Algebra.PluckerQuotTransitionMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Actual matrix normalization and overlap cocycles

These are algebraic identities for the original selected-column matrices.
The unit-determinant hypotheses will be supplied by restriction to the literal
projective pivot intersections; that geometric restriction is a separate gate.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι η κ : Type u}
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Selecting original columns commutes with multiplication on the quotient coordinates. -/
theorem selectedMatrix_mul (P : Matrix ι ι R) (M : Matrix ι η R) (s : ι → η) :
    selectedMatrix (P * M) s = P * selectedMatrix M s := by
  ext i j
  rfl

/-- Normalize the original matrix by the inverse of its actual selected pivot block. -/
def pivotNormalize (M : Matrix ι η R) (s : ι → η) : Matrix ι η R :=
  (selectedMatrix M s)⁻¹ * M

/-- An actual unit pivot gives exactly the identity selected block, over the whole ring. -/
theorem selectedMatrix_pivotNormalize (M : Matrix ι η R) (s : ι → η)
    (hs : IsUnit (columnMinor M s)) : selectedMatrix (pivotNormalize M s) s = 1 := by
  rw [pivotNormalize, selectedMatrix_mul]
  exact Matrix.nonsing_inv_mul _ hs

omit [Fintype ι] in
/-- Every matrix with the original identity block is the literal original normalized quotient. -/
theorem eq_splitNormalizedMatrix_of_selected_eq_one [Fintype κ] [DecidableEq κ]
    (e : (ι ⊕ κ) ≃ η) (M : Matrix ι η R)
    (hM : selectedMatrix M (e ∘ Sum.inl) = 1) :
    M = splitNormalizedMatrix e (fun i j ↦ M i (e (Sum.inr j))) := by
  ext i k
  obtain ⟨k, rfl⟩ := e.surjective k
  cases k with
  | inl k =>
    rw [splitNormalizedMatrix_apply, normalizedMatrix_inl]
    exact congrFun (congrFun hM i) k
  | inr j => simp

/-- The actual normalized matrix on the other pivot has its literal original matrix entries. -/
theorem pivotNormalize_eq_splitNormalizedMatrix [Fintype κ] [DecidableEq κ]
    (e : (ι ⊕ κ) ≃ η) (M : Matrix ι η R)
    (hs : IsUnit (columnMinor M (e ∘ Sum.inl))) :
    pivotNormalize M (e ∘ Sum.inl) =
      splitNormalizedMatrix e (fun i j ↦ pivotNormalize M (e ∘ Sum.inl) i (e (Sum.inr j))) :=
  eq_splitNormalizedMatrix_of_selected_eq_one e _ (selectedMatrix_pivotNormalize M _ hs)

/-- The actual change between two pivot quotient bases of the same original free module. -/
def pivotBasisChange (M : Matrix ι η R) (s t : ι → η) : Matrix ι ι R :=
  (selectedMatrix M t)⁻¹ * selectedMatrix M s

/-- The actual overlap change intertwines the two original normalized quotient matrices. -/
theorem pivotBasisChange_mul_normalize (M : Matrix ι η R) (s t : ι → η)
    (hs : IsUnit (columnMinor M s)) :
    pivotBasisChange M s t * pivotNormalize M s = pivotNormalize M t := by
  rw [pivotBasisChange, pivotNormalize, pivotNormalize]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (selectedMatrix M s), Matrix.mul_nonsing_inv _ hs,
    Matrix.one_mul]

/-- The exact triple-overlap cocycle for the actual same quotient-basis changes. -/
theorem pivotBasisChange_cocycle (M : Matrix ι η R) (s t v : ι → η)
    (ht : IsUnit (columnMinor M t)) :
    pivotBasisChange M t v * pivotBasisChange M s t = pivotBasisChange M s v := by
  rw [pivotBasisChange, pivotBasisChange, pivotBasisChange]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (selectedMatrix M t), Matrix.mul_nonsing_inv _ ht,
    Matrix.one_mul]

/-- An original actual unit pivot has the identity self-transition. -/
theorem pivotBasisChange_self (M : Matrix ι η R) (s : ι → η)
    (hs : IsUnit (columnMinor M s)) : pivotBasisChange M s s = 1 :=
  Matrix.nonsing_inv_mul _ hs

end Hironaka.Algebra.PluckerQuot
