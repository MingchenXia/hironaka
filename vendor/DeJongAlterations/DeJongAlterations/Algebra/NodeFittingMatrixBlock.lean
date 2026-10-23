import DeJongAlterations.Algebra.NodeFittingMatrixStabilization
import Lean.Elab.Tactic.Omega

/-! # Arbitrary literal identity blocks preserve saturated full presentation minors -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingMatrix

universe u v w
variable {R : Type u} [CommRing R] {m : Type v} {n : Type w}

/-- The original matrix with the actual finite identity block. -/
def blockStabilize (t : ℕ) (A : Matrix m n R) : Matrix (m ⊕ Fin t) (n ⊕ Fin t) R :=
  Matrix.fromBlocks A 0 0 1

/-- The actual successor identity index separates as the new distinguished generator. -/
def sumFinSuccOption (α : Type*) (t : ℕ) : α ⊕ Fin (t + 1) ≃ Option (α ⊕ Fin t) where
  toFun
    | Sum.inl a => some (Sum.inl a)
    | Sum.inr j => Fin.cases none (fun k => some (Sum.inr k)) j
  invFun
    | none => Sum.inr 0
    | some (Sum.inl a) => Sum.inl a
    | some (Sum.inr k) => Sum.inr k.succ
  left_inv x := by
    cases x with
    | inl a => rfl
    | inr j => exact Fin.cases rfl (fun _ => rfl) j
  right_inv x := by
    cases x with
    | none => rfl
    | some x => cases x <;> rfl

/-- The literal original successor block is exactly the original one-generator stabilization after reindexing. -/
theorem blockStabilize_succ_reindex (t : ℕ) (A : Matrix m n R) :
    (stabilize (blockStabilize t A)).submatrix (sumFinSuccOption m t) (sumFinSuccOption n t) =
      blockStabilize (t + 1) A := by
  ext x y
  rcases x with a | i <;> rcases y with b | j
  · rfl
  · exact Fin.cases rfl (fun _ => rfl) j
  · exact Fin.cases rfl (fun _ => rfl) i
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [blockStabilize, Matrix.fromBlocks, sumFinSuccOption, stabilize]
      · have hz : (0 : Fin (t + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        simp [blockStabilize, Matrix.fromBlocks, sumFinSuccOption, stabilize, hz]
    · refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [blockStabilize, Matrix.fromBlocks, Matrix.one_apply, sumFinSuccOption, stabilize]

/-- The actual empty added index has the original index equivalence. -/
def sumFinZeroEquiv (α : Type*) : α ⊕ Fin 0 ≃ α where
  toFun := Sum.elim id Fin.elim0
  invFun := Sum.inl
  left_inv x := by cases x with | inl _ => rfl | inr i => exact Fin.elim0 i
  right_inv _ := rfl

/-- The literal original empty stabilization has the original entries under its actual indices. -/
theorem blockStabilize_zero_reindex (A : Matrix m n R) :
    blockStabilize 0 A = A.submatrix (sumFinZeroEquiv m) (sumFinZeroEquiv n) := by
  ext x y
  rcases x with a | i <;> rcases y with b | j
  · rfl
  · exact Fin.elim0 j
  · exact Fin.elim0 i
  · exact Fin.elim0 i

/-- Arbitrary actual identity-block stabilization gives the exact whole original minors shift. -/
theorem determinantalIdeal_blockStabilize (k t : ℕ) (A : Matrix m n R) :
    determinantalIdeal (k + t) (blockStabilize t A) = determinantalIdeal k A := by
  induction t with
  | zero =>
    rw [blockStabilize_zero_reindex, determinantalIdeal_submatrix_equiv]
    rfl
  | succ t ih =>
    rw [← blockStabilize_succ_reindex, determinantalIdeal_submatrix_equiv, Nat.add_succ,
      determinantalIdeal_stabilize, ih]

/-- Any degree within the actual identity block already has its original identity minor. -/
theorem determinantalIdeal_blockStabilize_eq_top (k t : ℕ) (h : k ≤ t) (A : Matrix m n R) :
    determinantalIdeal k (blockStabilize t A) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have he : (blockStabilize t A).submatrix
      (fun i : Fin k => Sum.inr (Fin.castLE h i))
      (fun i : Fin k => Sum.inr (Fin.castLE h i)) = 1 := by
    ext i j
    simp [blockStabilize, Matrix.fromBlocks, Matrix.one_apply]
  have hh := minor_mem k (blockStabilize t A)
    (fun i : Fin k => Sum.inr (Fin.castLE h i))
    (fun i : Fin k => Sum.inr (Fin.castLE h i))
  rw [he, Matrix.det_one] at hh
  exact hh

/-- Actual Fitting degrees, with their original generator counts, are unchanged by the actual finite identity block. -/
theorem determinantalIdeal_blockStabilize_fittingDegree (i t n : ℕ) {p : Type*}
    (A : Matrix (Fin n) p R) :
    determinantalIdeal (n + t - i) (blockStabilize t A) = determinantalIdeal (n - i) A := by
  by_cases hi : i ≤ n
  · have he : n + t - i = (n - i) + t := by omega
    rw [he, determinantalIdeal_blockStabilize]
  · have he : n - i = 0 := by omega
    have hl : n + t - i ≤ t := by omega
    rw [determinantalIdeal_blockStabilize_eq_top _ _ hl, he, determinantalIdeal_zero]

end DeJongAlterations.Algebra.NodeFittingMatrix
