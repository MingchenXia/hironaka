import DeJongAlterations.Algebra.NodeFittingMatrixBasic

/-! # Full actual minors under rectangular products and invertible changes -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingMatrix

open scoped BigOperators

universe u v w z
variable {R : Type u} [CommRing R] {m : Type v} {n : Type w} {p : Type z}

/-- Native determinant multilinearity expands an actual rectangular product minor. -/
theorem product_minor_expansion [Fintype n] (k : ℕ) (A : Matrix m n R) (B : Matrix n p R)
    (r : Fin k → m) (c : Fin k → p) :
    ((A * B).submatrix r c).det =
      ∑ t : Fin k → n, (∏ i, A (r i) (t i)) * (B.submatrix t c).det := by
  classical
  let g : Fin k → n → (Fin k → R) := fun i j => A (r i) j • fun l => B j (c l)
  have he := (Matrix.detRowAlternating (R := R) (n := Fin k)).toMultilinearMap.map_sum g
  have hleft : (fun i => ∑ j, g i j) = (A * B).submatrix r c := by
    ext i j
    simp [g, Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = Matrix.det (fun i => ∑ j, g i j) := congrArg Matrix.det hleft.symm
    _ = ∑ t : Fin k → n, Matrix.det (fun i => g i (t i)) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      exact Matrix.det_mul_column (fun i => A (r i) (t i)) (B.submatrix t c)

/-- Every original product minor belongs to the full original right factor's minors ideal. -/
theorem determinantalIdeal_mul_le_right [Fintype n] (k : ℕ)
    (A : Matrix m n R) (B : Matrix n p R) :
    determinantalIdeal k (A * B) ≤ determinantalIdeal k B := by
  classical
  apply Ideal.span_le.mpr
  rintro x ⟨r, c, rfl⟩
  rw [product_minor_expansion]
  exact (determinantalIdeal k B).sum_mem fun t _ => Ideal.mul_mem_left _ _ (minor_mem k B t c)

/-- Every original product minor belongs to the full original left factor's minors ideal. -/
theorem determinantalIdeal_mul_le_left [Fintype n] (k : ℕ)
    (A : Matrix m n R) (B : Matrix n p R) :
    determinantalIdeal k (A * B) ≤ determinantalIdeal k A := by
  have hh := determinantalIdeal_mul_le_right k B.transpose A.transpose
  rw [← Matrix.transpose_mul, determinantalIdeal_transpose, determinantalIdeal_transpose] at hh
  exact hh

/-- Actual invertible changes of original free generators preserve the entire original minors ideal. -/
theorem determinantalIdeal_mul_unit_left [Fintype m] [DecidableEq m] (k : ℕ)
    (U : (Matrix m m R)ˣ) (A : Matrix m n R) :
    determinantalIdeal k ((U : Matrix m m R) * A) = determinantalIdeal k A := by
  apply le_antisymm (determinantalIdeal_mul_le_right k _ _)
  have hh := determinantalIdeal_mul_le_right k (↑U⁻¹ : Matrix m m R) ((U : Matrix m m R) * A)
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at hh
  exact hh

/-- Actual invertible changes of original finite relations preserve the entire original minors ideal. -/
theorem determinantalIdeal_mul_unit_right [Fintype n] [DecidableEq n] (k : ℕ)
    (A : Matrix m n R) (U : (Matrix n n R)ˣ) :
    determinantalIdeal k (A * (U : Matrix n n R)) = determinantalIdeal k A := by
  apply le_antisymm (determinantalIdeal_mul_le_left k _ _)
  have hh := determinantalIdeal_mul_le_left k (A * (U : Matrix n n R)) (↑U⁻¹ : Matrix n n R)
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at hh
  exact hh

end DeJongAlterations.Algebra.NodeFittingMatrix
