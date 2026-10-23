import DeJongAlterations.Algebra.NodeFittingMatrixRelations

/-! # Degree and original coordinate-index invariance of full minors ideals -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingMatrix

universe u v w
variable {R : Type u} [CommRing R] {m : Type v} {n : Type w}

/-- Actual expansion of each larger original minor gives whole-ideal degree containment. -/
theorem determinantalIdeal_succ_le (k : ℕ) (A : Matrix m n R) :
    determinantalIdeal (k + 1) A ≤ determinantalIdeal k A := by
  apply Ideal.span_le.mpr
  rintro x ⟨r, c, rfl⟩
  rw [Matrix.det_succ_row_zero]
  apply (determinantalIdeal k A).sum_mem
  intro j _
  apply Ideal.mul_mem_left
  change (A.submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det ∈ determinantalIdeal k A
  exact minor_mem k A _ _

/-- The actual full determinant ideals form a decreasing sequence. -/
theorem determinantalIdeal_antitone (k l : ℕ) (h : k ≤ l) (A : Matrix m n R) :
    determinantalIdeal l A ≤ determinantalIdeal k A := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (determinantalIdeal_succ_le l A).trans ih

/-- An original minor larger than the original finite row set vanishes scheme-theoretically. -/
theorem determinantalIdeal_eq_bot_of_card_rows_lt [Fintype m] (k : ℕ) (A : Matrix m n R)
    (hk : Fintype.card m < k) : determinantalIdeal k A = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro x ⟨r, c, rfl⟩
  have hr : ¬Function.Injective r := by
    intro hh
    have hle : k ≤ Fintype.card m := by simpa using Fintype.card_le_of_injective r hh
    exact (Nat.not_le_of_lt hk) hle
  rw [minor_eq_zero_of_not_injective_rows k A r c hr]
  exact Ideal.zero_mem _

/-- The same whole-ideal vanishing holds above the original column count. -/
theorem determinantalIdeal_eq_bot_of_card_columns_lt [Fintype n] (k : ℕ) (A : Matrix m n R)
    (hk : Fintype.card n < k) : determinantalIdeal k A = ⊥ := by
  rw [← determinantalIdeal_transpose k A]
  exact determinantalIdeal_eq_bot_of_card_rows_lt k A.transpose hk

/-- Reindexing the actual original row and column types preserves every whole minors ideal. -/
theorem determinantalIdeal_submatrix_equiv {m' n' : Type*}
    (e : m' ≃ m) (f : n' ≃ n) (k : ℕ) (A : Matrix m n R) :
    determinantalIdeal k (A.submatrix e f) = determinantalIdeal k A := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨r, c, rfl⟩
    exact minor_mem k A (e ∘ r) (f ∘ c)
  · apply Ideal.span_le.mpr
    rintro x ⟨r, c, rfl⟩
    have hh := minor_mem k (A.submatrix e f) (e.symm ∘ r) (f.symm ∘ c)
    have he : (e ∘ (e.symm ∘ r)) = r := by funext i; simp
    have hf : (f ∘ (f.symm ∘ c)) = c := by funext i; simp
    rw [Matrix.submatrix_submatrix, he, hf] at hh
    exact hh

end DeJongAlterations.Algebra.NodeFittingMatrix
