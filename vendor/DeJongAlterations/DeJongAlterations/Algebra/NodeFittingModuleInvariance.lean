import DeJongAlterations.Algebra.NodeFittingModulePresentation

/-! # Genuine presentation-independent full module Fitting ideals -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open NodeFittingMatrix Matrix

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The actual original finite matrix presentation computes the full Fitting-degree minors ideal. -/
def presentationIdeal (P : FiniteMatrixPresentation (R := R) M) (i : ℕ) : Ideal R :=
  determinantalIdeal (P.generatorCount - i) P.matrix

/-- The internally constructed actual invertible triangular generator change. -/
def comparisonUnit (P Q : FiniteMatrixPresentation (R := R) M) :
    (Matrix (Fin P.generatorCount ⊕ Fin Q.generatorCount)
      (Fin P.generatorCount ⊕ Fin Q.generatorCount) R)ˣ where
  val := Matrix.fromBlocks 1 (comparisonMatrix P Q) 0 1
  inv := Matrix.fromBlocks 1 (-comparisonMatrix P Q) 0 1
  val_inv := by rw [Matrix.fromBlocks_multiply]; simp
  inv_val := by rw [Matrix.fromBlocks_multiply]; simp

/-- The actual triangular row change gives exactly the literal original identity stabilization. -/
theorem comparisonUnit_mul_joinedMatrix (P Q : FiniteMatrixPresentation (R := R) M) :
    (comparisonUnit P Q : Matrix _ _ R) * joinedMatrix P Q =
      blockStabilize Q.generatorCount P.matrix := by
  change Matrix.fromBlocks 1 (comparisonMatrix P Q) 0 1 *
    Matrix.fromBlocks P.matrix (-comparisonMatrix P Q) 0 1 = _
  rw [Matrix.fromBlocks_multiply]
  simp [blockStabilize]

/-- The actual original common relation matrix computes the same original full presentation ideal. -/
theorem joinedMatrix_presentationIdeal (P Q : FiniteMatrixPresentation (R := R) M) (i : ℕ) :
    determinantalIdeal (P.generatorCount + Q.generatorCount - i) (joinedMatrix P Q) =
      presentationIdeal P i := by
  let C := comparisonMatrix P Q
  have hf : Matrix.fromBlocks 1 C 0 1 * joinedMatrix P Q =
      blockStabilize Q.generatorCount P.matrix := comparisonUnit_mul_joinedMatrix P Q
  have hb : Matrix.fromBlocks 1 (-C) 0 1 * blockStabilize Q.generatorCount P.matrix =
      joinedMatrix P Q := by
    rw [blockStabilize, Matrix.fromBlocks_multiply]
    simp [joinedMatrix, C]
  have hd : determinantalIdeal (P.generatorCount + Q.generatorCount - i) (joinedMatrix P Q) =
      determinantalIdeal (P.generatorCount + Q.generatorCount - i)
        (blockStabilize Q.generatorCount P.matrix) := by
    apply le_antisymm
    · rw [← hb]
      exact determinantalIdeal_mul_le_right _ _ _
    · rw [← hf]
      exact determinantalIdeal_mul_le_right _ _ _
  rw [hd, determinantalIdeal_blockStabilize_fittingDegree]
  rfl

/-- The actual finite relation map commutes with the same original row-index map. -/
theorem relationMap_submatrix_rows {a b c : Type*} [Fintype c]
    (A : Matrix b c R) (e : a → b) (z : c → R) :
    relationMap (A.submatrix e id) z = (relationMap A z) ∘ e := by
  ext i
  simp [relationMap, Fintype.linearCombination_apply, Matrix.submatrix,
    smul_eq_mul]

/-- Interchanging the original two common free summands retains the same original module map. -/
theorem joinedMap_swap (P Q : FiniteMatrixPresentation (R := R) M)
    (x : (Fin Q.generatorCount ⊕ Fin P.generatorCount) → R) :
    joinedMap P Q (x ∘ Equiv.sumComm _ _) = joinedMap Q P x := by
  change P.toModule (x ∘ Sum.inr) + Q.toModule (x ∘ Sum.inl) =
    Q.toModule (x ∘ Sum.inl) + P.toModule (x ∘ Sum.inr)
  exact add_comm _ _

/-- The reversed actual original relation matrix in the same original common coordinate module. -/
def reversedJoinedMatrix (P Q : FiniteMatrixPresentation (R := R) M) :
    Matrix (Fin P.generatorCount ⊕ Fin Q.generatorCount)
      (Fin Q.relationCount ⊕ Fin P.generatorCount) R :=
  (joinedMatrix Q P).submatrix (Equiv.sumComm _ _) id

/-- Both internally constructed original common relation matrices have exactly the same actual kernel image. -/
theorem reversedJoinedMatrix_range (P Q : FiniteMatrixPresentation (R := R) M) :
    LinearMap.range (relationMap (reversedJoinedMatrix P Q)) = LinearMap.ker (joinedMap P Q) := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    change joinedMap P Q (relationMap (reversedJoinedMatrix P Q) z) = 0
    rw [reversedJoinedMatrix, relationMap_submatrix_rows, joinedMap_swap]
    apply (joinedMatrix_range Q P).le
    exact ⟨z, rfl⟩
  · intro x hx
    have hh : (x ∘ Equiv.sumComm _ _) ∈ LinearMap.ker (joinedMap Q P) := by
      change joinedMap Q P (x ∘ Equiv.sumComm _ _) = 0
      rw [joinedMap_swap]
      exact hx
    obtain ⟨z, hz⟩ := (joinedMatrix_range Q P).ge hh
    refine ⟨z, ?_⟩
    rw [reversedJoinedMatrix, relationMap_submatrix_rows, hz]
    ext i
    cases i <;> rfl

/-- Any two actual finite original presentations of the same original module give exactly the same full ideals. -/
theorem presentationIdeal_eq (P Q : FiniteMatrixPresentation (R := R) M) (i : ℕ) :
    presentationIdeal P i = presentationIdeal Q i := by
  have hr : LinearMap.range (relationMap (joinedMatrix P Q)) =
      LinearMap.range (relationMap (reversedJoinedMatrix P Q)) :=
    (joinedMatrix_range P Q).trans (reversedJoinedMatrix_range P Q).symm
  calc
    _ = determinantalIdeal (P.generatorCount + Q.generatorCount - i) (joinedMatrix P Q) :=
      (joinedMatrix_presentationIdeal P Q i).symm
    _ = determinantalIdeal (P.generatorCount + Q.generatorCount - i) (reversedJoinedMatrix P Q) :=
      determinantalIdeal_eq_of_relationMap_range_eq _ _ _ hr
    _ = determinantalIdeal (P.generatorCount + Q.generatorCount - i) (joinedMatrix Q P) :=
      determinantalIdeal_submatrix_equiv (Equiv.sumComm _ _) (Equiv.refl _) _ _
    _ = determinantalIdeal (Q.generatorCount + P.generatorCount - i) (joinedMatrix Q P) := by
      rw [Nat.add_comm P.generatorCount Q.generatorCount]
    _ = presentationIdeal Q i := joinedMatrix_presentationIdeal Q P i

/-- Native finite presentation internally selects an actual original presentation. -/
def selectedPresentation [Module.FinitePresentation R M] : FiniteMatrixPresentation (R := R) M :=
  Classical.choice (exists_finiteMatrixPresentation M)

/-- The intrinsic original module Fitting ideal, proved independent of its internally chosen presentation. -/
def fittingIdeal [Module.FinitePresentation R M] (i : ℕ) : Ideal R :=
  presentationIdeal (selectedPresentation (R := R) (M := M)) i

/-- Every actual finite original presentation computes the same intrinsic full module Fitting ideal. -/
theorem fittingIdeal_eq_presentationIdeal [Module.FinitePresentation R M]
    (P : FiniteMatrixPresentation (R := R) M) (i : ℕ) :
    fittingIdeal (R := R) (M := M) i = presentationIdeal P i :=
  presentationIdeal_eq _ P i

end DeJongAlterations.Algebra.NodeFittingModule
