import DeJongAlterations.Algebra.NodeFittingMatrixBlock
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Native finite presentation and the full original common relation kernel

All finite presentations and comparison lifts are obtained from native
finite-presentation and actual projectivity/exactness. No Fitting-ideal
or target kernel certificate is assumed.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open NodeFittingMatrix Matrix

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R]

/-- The original native finite-free relation map is precisely its native matrix map. -/
theorem relationMap_eq_toLin {m n : Type*} [Fintype n] [DecidableEq n] (A : Matrix m n R) :
    relationMap A = Matrix.toLin' A := by
  ext x i
  simp [relationMap, Fintype.linearCombination_apply, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]

/-- Actual finite coordinate maps with native surjectivity and full native exactness. -/
structure FiniteMatrixPresentation (M : Type v) [AddCommGroup M] [Module R M] where
  generatorCount : ℕ
  relationCount : ℕ
  matrix : Matrix (Fin generatorCount) (Fin relationCount) R
  toModule : (Fin generatorCount → R) →ₗ[R] M
  surjective : Function.Surjective toModule
  exact : Function.Exact (relationMap matrix) toModule

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Native finite presentation constructs an actual matrix presentation internally. -/
theorem exists_finiteMatrixPresentation [Module.FinitePresentation R M] :
    Nonempty (FiniteMatrixPresentation (R := R) M) := by
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R M
  refine ⟨{
    generatorCount := n
    relationCount := m
    matrix := LinearMap.toMatrix' g
    toModule := f
    surjective := hf
    exact := ?_ }⟩
  rw [relationMap_eq_toLin, Matrix.toLin'_toMatrix']
  exact hg

variable {M}

/-- The actual native finite free source of the second original surjection lifts through the first. -/
def comparisonLift (P Q : FiniteMatrixPresentation (R := R) M) :
    (Fin Q.generatorCount → R) →ₗ[R] (Fin P.generatorCount → R) :=
  Classical.choose (Module.projective_lifting_property P.toModule Q.toModule P.surjective)

theorem comparisonLift_comp (P Q : FiniteMatrixPresentation (R := R) M) :
    P.toModule.comp (comparisonLift P Q) = Q.toModule :=
  Classical.choose_spec (Module.projective_lifting_property P.toModule Q.toModule P.surjective)

/-- The actual original lift's coefficient matrix. -/
def comparisonMatrix (P Q : FiniteMatrixPresentation (R := R) M) :
    Matrix (Fin P.generatorCount) (Fin Q.generatorCount) R :=
  LinearMap.toMatrix' (comparisonLift P Q)

@[simp]
theorem comparisonMatrix_mulVec (P Q : FiniteMatrixPresentation (R := R) M)
    (y : Fin Q.generatorCount → R) :
    comparisonMatrix P Q *ᵥ y = comparisonLift P Q y := by
  rw [← Matrix.toLin'_apply, comparisonMatrix, Matrix.toLin'_toMatrix']

/-- The actual original common free generators' first projection. -/
def sumLeftProjection (α β : Type*) : ((α ⊕ β) → R) →ₗ[R] (α → R) where
  toFun x := x ∘ Sum.inl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual original common free generators' second projection. -/
def sumRightProjection (α β : Type*) : ((α ⊕ β) → R) →ₗ[R] (β → R) where
  toFun x := x ∘ Sum.inr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The same original common finite generating map. -/
def joinedMap (P Q : FiniteMatrixPresentation (R := R) M) :
    ((Fin P.generatorCount ⊕ Fin Q.generatorCount) → R) →ₗ[R] M :=
  P.toModule.comp (sumLeftProjection _ _) + Q.toModule.comp (sumRightProjection _ _)

@[simp]
theorem joinedMap_apply (P Q : FiniteMatrixPresentation (R := R) M)
    (x : (Fin P.generatorCount ⊕ Fin Q.generatorCount) → R) :
    joinedMap P Q x = P.toModule (x ∘ Sum.inl) + Q.toModule (x ∘ Sum.inr) := rfl

/-- The actual original common finite generating map is surjective. -/
theorem joinedMap_surjective (P Q : FiniteMatrixPresentation (R := R) M) :
    Function.Surjective (joinedMap P Q) := by
  intro z
  obtain ⟨x, hx⟩ := P.surjective z
  refine ⟨Sum.elim x 0, ?_⟩
  change P.toModule x + Q.toModule 0 = z
  rw [map_zero, add_zero, hx]

/-- The original common map's internally constructed actual block relation matrix. -/
def joinedMatrix (P Q : FiniteMatrixPresentation (R := R) M) :
    Matrix (Fin P.generatorCount ⊕ Fin Q.generatorCount)
      (Fin P.relationCount ⊕ Fin Q.generatorCount) R :=
  Matrix.fromBlocks P.matrix (-comparisonMatrix P Q) 0 1

/-- The whole actual constructed relation map has the original coordinate formula. -/
theorem joinedMatrix_relationMap (P Q : FiniteMatrixPresentation (R := R) M)
    (z : (Fin P.relationCount ⊕ Fin Q.generatorCount) → R) :
    relationMap (joinedMatrix P Q) z =
      Sum.elim (relationMap P.matrix (z ∘ Sum.inl) - comparisonLift P Q (z ∘ Sum.inr))
        (z ∘ Sum.inr) := by
  rw [relationMap_eq_toLin, Matrix.toLin'_apply, joinedMatrix, Matrix.fromBlocks_mulVec]
  have hP : P.matrix *ᵥ (z ∘ Sum.inl) = relationMap P.matrix (z ∘ Sum.inl) := by
    rw [relationMap_eq_toLin, Matrix.toLin'_apply]
  rw [Matrix.neg_mulVec, comparisonMatrix_mulVec, Matrix.zero_mulVec, Matrix.one_mulVec,
    zero_add, hP, ← sub_eq_add_neg]

/-- The entire actual internally constructed common relation image is the actual common kernel. -/
theorem joinedMatrix_range (P Q : FiniteMatrixPresentation (R := R) M) :
    LinearMap.range (relationMap (joinedMatrix P Q)) = LinearMap.ker (joinedMap P Q) := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    change joinedMap P Q (relationMap (joinedMatrix P Q) z) = 0
    rw [joinedMatrix_relationMap]
    change P.toModule (relationMap P.matrix (z ∘ Sum.inl) - comparisonLift P Q (z ∘ Sum.inr)) +
      Q.toModule (z ∘ Sum.inr) = 0
    have hz : P.toModule (relationMap P.matrix (z ∘ Sum.inl)) = 0 := by
      apply (LinearMap.exact_iff.mp P.exact).ge
      exact ⟨z ∘ Sum.inl, rfl⟩
    have hl := DFunLike.congr_fun (comparisonLift_comp P Q) (z ∘ Sum.inr)
    change P.toModule (comparisonLift P Q (z ∘ Sum.inr)) = Q.toModule (z ∘ Sum.inr) at hl
    rw [map_sub, hz, hl]
    abel
  · intro x hx
    have hl := DFunLike.congr_fun (comparisonLift_comp P Q) (x ∘ Sum.inr)
    change P.toModule (comparisonLift P Q (x ∘ Sum.inr)) = Q.toModule (x ∘ Sum.inr) at hl
    have hk : (x ∘ Sum.inl) + comparisonLift P Q (x ∘ Sum.inr) ∈
        LinearMap.range (relationMap P.matrix) := by
      rw [← LinearMap.exact_iff.mp P.exact]
      change P.toModule ((x ∘ Sum.inl) + comparisonLift P Q (x ∘ Sum.inr)) = 0
      rw [map_add, hl]
      exact hx
    obtain ⟨a, ha⟩ := hk
    refine ⟨Sum.elim a (x ∘ Sum.inr), ?_⟩
    rw [joinedMatrix_relationMap]
    ext i
    cases i with
    | inl i =>
      change relationMap P.matrix a i - comparisonLift P Q (x ∘ Sum.inr) i = x (Sum.inl i)
      rw [ha]
      simp
    | inr i => rfl

end DeJongAlterations.Algebra.NodeFittingModule
