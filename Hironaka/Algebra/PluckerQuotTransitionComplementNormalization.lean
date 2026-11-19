import Hironaka.Algebra.PluckerQuotTransitionLinear
import Mathlib.Logic.Equiv.Set

/-!
# The actual original selected columns and complement give the original normalized quotient

The source reindexing is constructed from the SAME original index embedding.
The WHOLE matrix map, rather than just its quotient kernel, is retained.
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

universe u

variable {B : Type u} [CommRing B] {I E : Type u}
  [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

/-- The SAME original selected indices followed by their actual original complement. -/
def originalPivotComplementEquiv (a : I ↪ E) : I ⊕ ((Set.range a)ᶜ : Set E) ≃ E :=
  (Equiv.sumCongr (Equiv.ofInjective a a.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range a))

omit [Fintype E] [DecidableEq I] in
@[simp]
theorem originalPivotComplementEquiv_inl (a : I ↪ E) (i : I) :
    originalPivotComplementEquiv a (Sum.inl i) = a i := rfl

omit [Fintype E] [DecidableEq I] in
@[simp]
theorem originalPivotComplementEquiv_inr (a : I ↪ E) (j : ((Set.range a)ᶜ : Set E)) :
    originalPivotComplementEquiv a (Sum.inr j) = j.val := rfl

/-- The coefficient matrix consists of the SAME original complementary columns. -/
def originalPivotComplementMatrix (C : Matrix I E B) (a : I ↪ E) :
    Matrix I ((Set.range a)ᶜ : Set E) B := C.submatrix id Subtype.val

/-- Reindexing by the actual original selected and complementary indices gives the ENTIRE original normalized matrix. -/
theorem originalPivotComplementMatrix_normalized (C : Matrix I E B) (a : I ↪ E)
    (h : ∀ i j, C i (a j) = if i = j then 1 else 0) :
    C.submatrix id (originalPivotComplementEquiv a) =
      PluckerQuot.normalizedMatrix (originalPivotComplementMatrix C a) := by
  ext i j
  cases j with
  | inl j =>
    simp only [Matrix.submatrix_apply, id_eq, originalPivotComplementEquiv_inl,
      PluckerQuot.normalizedMatrix_inl, Matrix.one_apply, h]
  | inr j =>
    simp only [Matrix.submatrix_apply, id_eq, originalPivotComplementEquiv_inr,
      PluckerQuot.normalizedMatrix_inr, originalPivotComplementMatrix]

/-- WHOLE original source reindexing, actual original full matrix, and the original normalized quotient commute. -/
theorem originalPivotComplementMatrix_whole_quotient (C : Matrix I E B) (a : I ↪ E)
    (h : ∀ i j, C i (a j) = if i = j then 1 else 0) :
    C.mulVecLin.comp
      (LinearEquiv.funCongrLeft B B (originalPivotComplementEquiv a).symm).toLinearMap =
      PluckerQuot.matrixQuotient (originalPivotComplementMatrix C a) := by
  have hm := Matrix.mulVecLin_submatrix (R := B) id (originalPivotComplementEquiv a) C
  rw [originalPivotComplementMatrix_normalized C a h,
    PluckerQuot.normalizedMatrix_mulVecLin] at hm
  exact hm.symm

end Hironaka.Algebra.PluckerQuotTransition
