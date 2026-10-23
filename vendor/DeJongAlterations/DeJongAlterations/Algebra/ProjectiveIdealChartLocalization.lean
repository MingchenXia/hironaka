/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.ProjectiveIdealChartAlgebra
/- Reused from EnvelopeProperty/Projective/ChartLocalization.lean; SHA256 2a454b97911509a1c781ad2bd541f3921e9087f6c0e791da8a0b031c38c0bb78. -/


/-!
# Localized homogeneous substitutions for projective charts

Over any commutative coefficient ring, the substitution `X_j ↦ T`,
`X_i ↦ U_i T` extends from the homogeneous polynomial ring to its
localization at `X_j`, with target localized at `T`. Composing this map
with the genuine chart-ratio homomorphism is the coefficient inclusion
on every chart polynomial. Cancellation uses units rather than a domain
or comparisons of seminorm values.
-/

open scoped Polynomial
open Polynomial

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveIdeal

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The polynomial ring of a chart with its homogeneous parameter inverted. -/
abbrev ChartParameterLocalization (R : Type*) [CommRing R] (j : Fin (n + 1)) :=
  Localization.Away (Polynomial.X : (CoordinateRing R j)[X])

/-- The coefficient-ring inclusion into the localized chart polynomial ring. -/
def chartCoefficientsToLocalization (j : Fin (n + 1)) :
    CoordinateRing R j →ₐ[R] ChartParameterLocalization R j :=
  (IsScalarTower.toAlgHom R (CoordinateRing R j)[X] (ChartParameterLocalization R j)).comp
    (CAlgHom : CoordinateRing R j →ₐ[R] (CoordinateRing R j)[X])

/-- Homogeneous substitution followed by localization of its polynomial parameter. -/
def chartHomogenizeToLocalization (j : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] ChartParameterLocalization R j :=
  (IsScalarTower.toAlgHom R (CoordinateRing R j)[X] (ChartParameterLocalization R j)).comp
    (chartHomogenize j)

/-- The selected homogeneous coordinate is sent to the inverted parameter. -/
theorem chartHomogenizeToLocalization_isUnit_X (j : Fin (n + 1)) :
    IsUnit (chartHomogenizeToLocalization (R := R) j (MvPolynomial.X j)) := by
  change IsUnit (algebraMap (CoordinateRing R j)[X] (ChartParameterLocalization R j)
    (chartHomogenize j (MvPolynomial.X j)))
  simp only [chartHomogenize, MvPolynomial.aeval_X, coordinateDehomCoord_self, Polynomial.C_1, one_mul]
  exact IsLocalization.Away.algebraMap_isUnit Polynomial.X

/-- Extend the homogeneous substitution to the localization of the selected coordinate. -/
def chartHomogenizeLocalization (j : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R]
      ChartParameterLocalization R j :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X j)
    (chartHomogenizeToLocalization_isUnit_X j)

/-- The localized substitution agrees with the original substitution on every polynomial. -/
@[simp]
theorem chartHomogenizeLocalization_algebraMap (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    chartHomogenizeLocalization j
        (algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j)) F) =
      algebraMap (CoordinateRing R j)[X] (ChartParameterLocalization R j) (chartHomogenize j F) := by
  simp only [chartHomogenizeLocalization, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- The ratio substitution is cancelled as an equality of algebra maps on the full chart ring. -/
theorem chartHomogenizeLocalization_comp_chartRatioHom (j : Fin (n + 1)) :
    (chartHomogenizeLocalization (R := R) j).comp (chartRatioHom j) =
      chartCoefficientsToLocalization j := by
  ext i
  change chartHomogenizeLocalization j (chartRatioHom j (MvPolynomial.X i)) =
    algebraMap (CoordinateRing R j)[X] (ChartParameterLocalization R j) (Polynomial.C (MvPolynomial.X i))
  have h := congrArg (chartHomogenizeLocalization (R := R) j)
    (chartRatioHom_dehomCoord_mul j i.1)
  simp only [map_mul, chartHomogenizeLocalization_algebraMap,
    chartHomogenize, MvPolynomial.aeval_X, coordinateDehomCoord_self,
    coordinateDehomCoord_ne j i, Polynomial.C_1, one_mul] at h
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := ChartParameterLocalization R j) (Polynomial.X : (CoordinateRing R j)[X])).mul_right_cancel h

/-- Cancellation holds at every chart polynomial, preserving every eventual seminorm evaluation. -/
@[simp]
theorem chartHomogenizeLocalization_chartRatioHom (j : Fin (n + 1)) (a : CoordinateRing R j) :
    chartHomogenizeLocalization j (chartRatioHom j a) =
      algebraMap (CoordinateRing R j)[X] (ChartParameterLocalization R j) (Polynomial.C a) :=
  AlgHom.congr_fun (chartHomogenizeLocalization_comp_chartRatioHom j) a

/-- Dehomogenization extends to the coordinate localization since the coordinate maps to one. -/
def coordinateDehomLocalization (j : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] CoordinateRing R j :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X j)
    (f := coordinateDehom j) (by simp [coordinateDehom])

@[simp]
theorem coordinateDehomLocalization_algebraMap (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    coordinateDehomLocalization j
        (algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j)) F) =
      coordinateDehom j F := by
  simp only [coordinateDehomLocalization, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

end DeJongAlterations.Geometry.ProjectiveIdeal
