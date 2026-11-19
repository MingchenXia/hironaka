import Hironaka.Algebra.ProjectiveLinearCoordinatesMatrix

/-!
# Actual scalar extension of the SAME original entire linear equivalence
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u v w

variable (k : Type u) (L : Type v) [Field k] [Field L] (φ : k →+* L)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The entire actual original linear map's scalar extension uses its SAME original standard-basis matrix coefficients. -/
def scalarLinearMap {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) : (ι → L) →ₗ[L] (ι → L) :=
  Matrix.toLin' ((LinearMap.toMatrix' e.toLinearMap).map φ)

/-- The whole actual original inverse-matrix identity internally proves the scalar inverse identity. -/
theorem scalarLinearMap_inverse {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) (x : ι → L) :
    scalarLinearMap k L φ e.symm (scalarLinearMap k L φ e x) = x := by
  change Matrix.toLin' ((LinearMap.toMatrix' e.symm.toLinearMap).map φ)
    (Matrix.toLin' ((LinearMap.toMatrix' e.toLinearMap).map φ) x) = x
  rw [← Matrix.toLin'_mul_apply, ← Matrix.map_mul, linearEquiv_matrix_symm_mul k e]
  simp

/-- The SAME original actual entire linear equivalence internally produces an actual whole scalar linear equivalence, without an inverse or coefficient certificate. -/
def scalarLinearEquiv {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) : (ι → L) ≃ₗ[L] (ι → L) where
  __ := scalarLinearMap k L φ e
  invFun := scalarLinearMap k L φ e.symm
  left_inv := scalarLinearMap_inverse k L φ e
  right_inv := by
    intro x
    exact scalarLinearMap_inverse k L φ e.symm x

/-- The actual scalar extension retains the literal whole original coefficient-vector triangle. -/
theorem scalarLinearEquiv_coefficient_triangle {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) (x : ι → k) :
    scalarLinearEquiv k L φ e (φ ∘ x) = φ ∘ (e x) := by
  ext i
  change Matrix.mulVec ((LinearMap.toMatrix' e.toLinearMap).map φ) (φ ∘ x) i = φ (e x i)
  rw [← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec]
  simp only [LinearEquiv.coe_coe]

/-- The actual matrix of the internally constructed whole scalar linear equivalence is the literal original whole matrix with its original coefficients mapped by φ. -/
theorem scalarLinearEquiv_toMatrix {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) :
    LinearMap.toMatrix' (scalarLinearEquiv k L φ e).toLinearMap =
      (LinearMap.toMatrix' e.toLinearMap).map φ :=
  LinearMap.toMatrix'_toLin' _

end Hironaka.Algebra.ProjectiveLinearCoordinates
