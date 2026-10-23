import DeJongAlterations.Algebra.NodeFittingMatrixOrder

/-! # Exact full minors shift for one actual identity-generator stabilization -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingMatrix

universe u v w
variable {R : Type u} [CommRing R] {m : Type v} {n : Type w}

/-- The literal original relation matrix with one new generator and its identity relation. -/
def stabilize (A : Matrix m n R) : Matrix (Option m) (Option n) R
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some i, some j => A i j

private theorem exists_some_coordinates {α β : Type*} (r : α → Option β)
    (hr : ∀ i, r i ≠ none) : ∃ s : α → β, ∀ i, r i = some (s i) := by
  classical
  have hh : ∀ i, ∃ b, r i = some b := by
    intro i
    cases hi : r i with
    | none => exact False.elim (hr i hi)
    | some b => exact ⟨b, rfl⟩
  choose s hs using hh
  exact ⟨s, hs⟩

/-- Extending the original minor by the actual identity row and column retains its determinant exactly. -/
theorem stabilize_minor (k : ℕ) (A : Matrix m n R) (r : Fin k → m) (c : Fin k → n) :
    ((stabilize A).submatrix (Fin.cases none (fun i => some (r i)))
      (Fin.cases none (fun j => some (c j)))).det = (A.submatrix r c).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [stabilize, Matrix.submatrix]

private theorem stabilize_minor_mem_of_no_new_row (k : ℕ) (A : Matrix m n R)
    (r : Fin (k + 1) → Option m) (c : Fin (k + 1) → Option n)
    (hr : ∀ i, r i ≠ none) :
    ((stabilize A).submatrix r c).det ∈ determinantalIdeal k A := by
  classical
  obtain ⟨r', hr'⟩ := exists_some_coordinates r hr
  by_cases hc : ∃ j, c j = none
  · obtain ⟨j, hj⟩ := hc
    have hz : ((stabilize A).submatrix r c).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero j
      intro i
      change stabilize A (r i) (c j) = 0
      rw [hr' i, hj]
      rfl
    rw [hz]
    exact Ideal.zero_mem _
  · have hc' : ∀ j, c j ≠ none := by
      intro j hj
      exact hc ⟨j, hj⟩
    obtain ⟨c', hc'⟩ := exists_some_coordinates c hc'
    have he : (stabilize A).submatrix r c = A.submatrix r' c' := by
      ext i j
      change stabilize A (r i) (c j) = A (r' i) (c' j)
      rw [hr' i, hc' j]
      rfl
    rw [he]
    exact determinantalIdeal_succ_le k A (minor_mem (k + 1) A r' c')

/-- Every actual enlarged original minor lies in the original smaller minors ideal. -/
theorem stabilize_minor_mem (k : ℕ) (A : Matrix m n R)
    (r : Fin (k + 1) → Option m) (c : Fin (k + 1) → Option n) :
    ((stabilize A).submatrix r c).det ∈ determinantalIdeal k A := by
  classical
  by_cases hr : Function.Injective r
  · by_cases hc : Function.Injective c
    · by_cases hn : ∃ i, r i = none
      · obtain ⟨i, hi⟩ := hn
        by_cases hm : ∃ j, c j = none
        · obtain ⟨j, hj⟩ := hm
          have hrr : ∀ l, r (i.succAbove l) ≠ none := by
            intro l hz
            exact Fin.succAbove_ne i l (hr (hz.trans hi.symm))
          have hcc : ∀ l, c (j.succAbove l) ≠ none := by
            intro l hz
            exact Fin.succAbove_ne j l (hc (hz.trans hj.symm))
          obtain ⟨r', hr'⟩ := exists_some_coordinates (r ∘ i.succAbove) hrr
          obtain ⟨c', hc'⟩ := exists_some_coordinates (c ∘ j.succAbove) hcc
          simp only [Function.comp_def] at hr' hc'
          have he : (((stabilize A).submatrix r c).submatrix i.succAbove j.succAbove) =
              A.submatrix r' c' := by
            ext a b
            change stabilize A (r (i.succAbove a)) (c (j.succAbove b)) = A (r' a) (c' b)
            rw [hr' a, hc' b]
            rfl
          have hco : (((stabilize A).submatrix r c).submatrix i.succAbove j.succAbove).det ∈
              determinantalIdeal k A := by
            rw [he]
            exact minor_mem k A r' c'
          rw [Matrix.det_succ_row _ i]
          apply (determinantalIdeal k A).sum_mem
          intro l _
          by_cases hl : l = j
          · rw [hl]
            exact Ideal.mul_mem_left _ _ hco
          · have hz : (stabilize A).submatrix r c i l = 0 := by
              change stabilize A (r i) (c l) = 0
              rw [hi]
              cases hcl : c l with
              | none => exact False.elim (hl (hc (hcl.trans hj.symm)))
              | some b => rfl
            rw [hz, mul_zero, zero_mul]
            exact Ideal.zero_mem _
        · have hz : ((stabilize A).submatrix r c).det = 0 := by
            apply Matrix.det_eq_zero_of_row_eq_zero i
            intro j
            change stabilize A (r i) (c j) = 0
            rw [hi]
            cases hcj : c j with
            | none => exact False.elim (hm ⟨j, hcj⟩)
            | some b => rfl
          rw [hz]
          exact Ideal.zero_mem _
      · apply stabilize_minor_mem_of_no_new_row k A r c
        intro i hi
        exact hn ⟨i, hi⟩
    · rw [minor_eq_zero_of_not_injective_columns (k + 1) (stabilize A) r c hc]
      exact Ideal.zero_mem _
  · rw [minor_eq_zero_of_not_injective_rows (k + 1) (stabilize A) r c hr]
    exact Ideal.zero_mem _

/-- One actual identity-generator stabilization gives the exact whole original minors shift. -/
theorem determinantalIdeal_stabilize (k : ℕ) (A : Matrix m n R) :
    determinantalIdeal (k + 1) (stabilize A) = determinantalIdeal k A := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨r, c, rfl⟩
    exact stabilize_minor_mem k A r c
  · apply Ideal.span_le.mpr
    rintro x ⟨r, c, rfl⟩
    rw [← stabilize_minor k A r c]
    exact minor_mem (k + 1) (stabilize A) _ _

end DeJongAlterations.Algebra.NodeFittingMatrix
