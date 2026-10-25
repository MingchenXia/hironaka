import DeJongAlterations.Algebra.NodeFittingModuleInvariance
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Entire intrinsic module Fitting ideals under actual coefficient extension

Actual native tensor maps and original scalar-extended coordinate bases
produce the actual coefficient-image presentation. No Noetherian or
flatness hypothesis is used. Geometric overlap and ideal-sheaf gluing are separate.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open NodeFittingMatrix Matrix
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The same original relation matrix presents an actually isomorphic module. -/
def FiniteMatrixPresentation.mapEquiv {N : Type z} [AddCommGroup N] [Module R N]
    (P : FiniteMatrixPresentation (R := R) M) (e : M ≃ₗ[R] N) :
    FiniteMatrixPresentation (R := R) N where
  generatorCount := P.generatorCount
  relationCount := P.relationCount
  matrix := P.matrix
  toModule := e.toLinearMap.comp P.toModule
  surjective := e.surjective.comp P.surjective
  exact := e.injective.comp_exact_iff_exact.mpr P.exact

/-- Every actual module equivalence preserves the entire original intrinsic Fitting ideal. -/
theorem fittingIdeal_equiv {N : Type z} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N] (e : M ≃ₗ[R] N) (i : ℕ) :
    fittingIdeal (R := R) (M := M) i = fittingIdeal (R := R) (M := N) i := by
  let P := selectedPresentation (R := R) (M := M)
  calc
    _ = presentationIdeal P i := rfl
    _ = presentationIdeal (P.mapEquiv e) i := rfl
    _ = _ := (fittingIdeal_eq_presentationIdeal (P.mapEquiv e) i).symm

/-- Actual native matrix coordinates are the whole original basis-coordinate triangle. -/
theorem relationMap_toMatrix_coordinates {U V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (bu : Module.Basis a R U) (bv : Module.Basis b R V) (g : U →ₗ[R] V) (x : a → R) :
    relationMap (LinearMap.toMatrix bu bv g) x = bv.equivFun (g (bu.equivFun.symm x)) := by
  rw [relationMap_eq_toLin, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix']
  rfl

/-- Whole native exactness transports through the actual original free coordinate bases. -/
theorem exact_in_coordinates {U V N : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup N]
    [Module R U] [Module R V] [Module R N]
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (bu : Module.Basis a R U) (bv : Module.Basis b R V)
    (g : U →ₗ[R] V) (f : V →ₗ[R] N) (he : Function.Exact g f) :
    Function.Exact (relationMap (LinearMap.toMatrix bu bv g))
      (f.comp bv.equivFun.symm.toLinearMap) := by
  apply LinearMap.exact_iff.mpr
  ext x
  constructor
  · intro hx
    have hk : bv.equivFun.symm x ∈ LinearMap.ker f := hx
    obtain ⟨u, hu⟩ := (LinearMap.exact_iff.mp he).le hk
    refine ⟨bu.equivFun u, ?_⟩
    rw [relationMap_toMatrix_coordinates, LinearEquiv.symm_apply_apply, hu,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    change f (bv.equivFun.symm (relationMap (LinearMap.toMatrix bu bv g) x)) = 0
    rw [relationMap_toMatrix_coordinates, LinearEquiv.symm_apply_apply]
    apply (LinearMap.exact_iff.mp he).ge
    exact ⟨bu.equivFun.symm x, rfl⟩

variable (S : Type w) [CommRing S] [Algebra R S]

/-- The actual native scalar extension of the original standard finite free basis. -/
def extendedCoordinateBasis (n : ℕ) :
    Module.Basis (Fin n) S (S ⊗[R] (Fin n → R)) :=
  _root_.Algebra.TensorProduct.basis S (Pi.basisFun R (Fin n))

/-- The actual original matrix in its actual original standard coordinate bases. -/
theorem originalCoordinateMatrix (P : FiniteMatrixPresentation (R := R) M) :
    LinearMap.toMatrix (Pi.basisFun R (Fin P.relationCount))
      (Pi.basisFun R (Fin P.generatorCount)) (relationMap P.matrix) = P.matrix := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr, relationMap_eq_toLin,
    Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply]

/-- The actual native base-changed relation matrix is the exact coefficient image of the original. -/
theorem extendedCoordinateMatrix (P : FiniteMatrixPresentation (R := R) M) :
    LinearMap.toMatrix (extendedCoordinateBasis (R := R) S P.relationCount)
      (extendedCoordinateBasis (R := R) S P.generatorCount)
      ((relationMap P.matrix).baseChange S) = P.matrix.map (algebraMap R S) := by
  rw [extendedCoordinateBasis, extendedCoordinateBasis, LinearMap.toMatrix_baseChange,
    originalCoordinateMatrix]

/-- Actual native tensoring of the original surjection in the actual extended original basis. -/
def baseChangeToModule (P : FiniteMatrixPresentation (R := R) M) :
    (Fin P.generatorCount → S) →ₗ[S] (S ⊗[R] M) :=
  (P.toModule.baseChange S).comp
    (extendedCoordinateBasis (R := R) S P.generatorCount).equivFun.symm.toLinearMap

/-- The actual native tensor module has the internally constructed original coefficient-image presentation. -/
def baseChangePresentation (P : FiniteMatrixPresentation (R := R) M) :
    FiniteMatrixPresentation (R := S) (S ⊗[R] M) where
  generatorCount := P.generatorCount
  relationCount := P.relationCount
  matrix := P.matrix.map (algebraMap R S)
  toModule := baseChangeToModule S P
  surjective := (LinearMap.lTensor_surjective S P.surjective).comp
    (extendedCoordinateBasis (R := R) S P.generatorCount).equivFun.symm.surjective
  exact := by
    have he := lTensor_exact S P.exact P.surjective
    have hc := exact_in_coordinates
      (extendedCoordinateBasis (R := R) S P.relationCount)
      (extendedCoordinateBasis (R := R) S P.generatorCount)
      ((relationMap P.matrix).baseChange S) (P.toModule.baseChange S) he
    rw [extendedCoordinateMatrix] at hc
    exact hc

/-- Actual whole intrinsic Fitting ideals commute with every coefficient extension, with no flatness assumption. -/
theorem fittingIdeal_baseChange [Module.FinitePresentation R M] (i : ℕ) :
    (fittingIdeal (R := R) (M := M) i).map (algebraMap R S) =
      fittingIdeal (R := S) (M := S ⊗[R] M) i := by
  let P := selectedPresentation (R := R) (M := M)
  rw [fittingIdeal_eq_presentationIdeal P i,
    fittingIdeal_eq_presentationIdeal (baseChangePresentation S P) i]
  change (determinantalIdeal (P.generatorCount - i) P.matrix).map (algebraMap R S) =
    determinantalIdeal (P.generatorCount - i) (P.matrix.map (algebraMap R S))
  exact determinantalIdeal_map _ _ _

end DeJongAlterations.Algebra.NodeFittingModule
