/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Projective
import Mathlib.RingTheory.Localization.Algebra
/- Reused from EnvelopeProperty/Projective/ChartAlgebra.lean; SHA256 ec1313439e9e0c17b8f73d22d2f20b2691fa9a840012885e30b0f107f7f34f11. -/


/-!
# Homogeneous substitutions for affine projective charts

These algebraic identities hold over any commutative coefficient ring. Dehomogenizing
at `j` sends `X_j` to one and the other variables to the affine chart variables.
Homogeneous substitution sends `X_j` to `T` and `X_i` to `U_i T`.
Its coefficient of `T^d` is the dehomogenization of the degree-`d` component.
-/

open scoped Polynomial
open Polynomial

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveIdeal

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The affine coordinates complementary to the selected homogeneous coordinate. -/
abbrev ChartIndex (j : Fin (n + 1)) := {i : Fin (n + 1) // i ≠ j}

/-- The coordinate ring of a projective chart over an arbitrary commutative ring. -/
abbrev CoordinateRing (R : Type*) [CommRing R] (j : Fin (n + 1)) :=
  MvPolynomial (ChartIndex j) R

def coordinateDehomCoord (j : Fin (n + 1)) (i : Fin (n + 1)) : CoordinateRing R j :=
  if h : i = j then 1 else MvPolynomial.X ⟨i, h⟩

def coordinateDehom (j : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R →ₐ[R] CoordinateRing R j :=
  MvPolynomial.aeval (coordinateDehomCoord j)

def chartHomogenize (j : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] (CoordinateRing R j)[X] :=
  MvPolynomial.aeval fun i => Polynomial.C (coordinateDehomCoord j i) * Polynomial.X

/-- Affine coordinates are sent to the genuine fractions `X_i / X_j`. -/
def chartRatioHom (j : Fin (n + 1)) :
    CoordinateRing R j →ₐ[R] Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.aeval fun i : ChartIndex j =>
    IsLocalization.mk'
      (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))
      (MvPolynomial.X i.1)
      (⟨MvPolynomial.X j ^ 1, 1, rfl⟩ :
        Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))

@[simp]
theorem coordinateDehomCoord_self (j : Fin (n + 1)) : coordinateDehomCoord (R := R) j j = 1 := by
  simp [coordinateDehomCoord]

@[simp]
theorem coordinateDehomCoord_ne (j : Fin (n + 1)) (i : ChartIndex j) :
    coordinateDehomCoord (R := R) j i.1 = MvPolynomial.X i := by
  simp [coordinateDehomCoord, i.2]

/-- A monomial acquires one power of `T` for each homogeneous variable occurrence. -/
theorem chartHomogenize_monomial (j : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) (c : R) :
    chartHomogenize j (MvPolynomial.monomial m c) =
      Polynomial.C (coordinateDehom j (MvPolynomial.monomial m c)) *
        Polynomial.X ^ Finsupp.degree m := by
  simp only [chartHomogenize, coordinateDehom, MvPolynomial.aeval_monomial]
  change Polynomial.C (algebraMap R (CoordinateRing R j) c) *
      (∏ i ∈ m.support, (Polynomial.C (coordinateDehomCoord j i) * Polynomial.X) ^ m i) =
    Polynomial.C (algebraMap R (CoordinateRing R j) c *
      ∏ i ∈ m.support, coordinateDehomCoord j i ^ m i) *
        Polynomial.X ^ (∑ i ∈ m.support, m i)
  simp_rw [mul_pow, ← map_pow]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, map_mul, mul_assoc]

/-- A homogeneous form is sent to its dehomogenization times a pure power of `T`. -/
theorem chartHomogenize_of_isHomogeneous (j : Fin (n + 1))
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    chartHomogenize j F = Polynomial.C (coordinateDehom j F) * Polynomial.X ^ d := by
  classical
  rw [← F.support_sum_monomial_coeff, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [chartHomogenize_monomial]
  have hdeg : Finsupp.degree m = d := hF.degree_eq_sum_deg_support hm |>.symm
  rw [hdeg]

/-- The homogeneous component of degree `d` maps to a pure `T^d` term. -/
theorem chartHomogenize_homogeneousComponent (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    chartHomogenize j (MvPolynomial.homogeneousComponent d F) =
      Polynomial.C (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) * Polynomial.X ^ d :=
  chartHomogenize_of_isHomogeneous j (MvPolynomial.homogeneousComponent_isHomogeneous d F)

/-- Polynomial coefficients of the homogeneous substitution are exact dehomogenizations. -/
theorem chartHomogenize_coeff (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    (chartHomogenize j F).coeff d = coordinateDehom j (MvPolynomial.homogeneousComponent d F) := by
  classical
  conv_lhs => rw [← F.support_sum_monomial_coeff]
  rw [map_sum, Polynomial.finsetSum_coeff]
  rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [chartHomogenize_monomial, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm]

/-- Multiplying a dehomogenized coordinate ratio by the selected coordinate cancels
its denominator, including the selected coordinate itself. -/
theorem chartRatioHom_dehomCoord_mul (j i : Fin (n + 1)) :
    chartRatioHom j (coordinateDehomCoord (R := R) j i) *
        algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X j) =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X i) := by
  by_cases hij : i = j
  · subst i
    simp
  · simp only [coordinateDehomCoord, dif_neg hij, chartRatioHom, MvPolynomial.aeval_X]
    simpa only [pow_one] using
      IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))
        (MvPolynomial.X i) (⟨MvPolynomial.X j ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X j))

/-- Evaluate the homogeneous substitution back in the coordinate localization,
using the genuine ratios and the original selected coordinate. -/
def chartRehom (j : Fin (n + 1)) :
    (CoordinateRing R j)[X] →ₐ[R]
      Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) :=
  Polynomial.eval₂AlgHom (chartRatioHom j)
    (algebraMap (MvPolynomial (Fin (n + 1)) R)
      (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X j))
    (fun _ => Commute.all _ _)

@[simp]
theorem chartRehom_C (j : Fin (n + 1)) (a : CoordinateRing R j) :
    chartRehom j (Polynomial.C a) = chartRatioHom j a :=
  Polynomial.eval₂_C _ _

@[simp]
theorem chartRehom_X (j : Fin (n + 1)) :
    chartRehom (R := R) j Polynomial.X =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X j) :=
  Polynomial.eval₂_X _ _

/-- Rehomogenization recovers the original polynomial as an equality of algebra maps. -/
theorem chartRehom_comp_chartHomogenize (j : Fin (n + 1)) :
    (chartRehom (R := R) j).comp (chartHomogenize j) =
      IsScalarTower.toAlgHom R (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X j)) := by
  ext i
  simp only [AlgHom.comp_apply, chartHomogenize, MvPolynomial.aeval_X, map_mul,
    chartRehom_C, chartRehom_X]
  exact chartRatioHom_dehomCoord_mul j i

@[simp]
theorem chartRehom_chartHomogenize (j : Fin (n + 1)) (F : MvPolynomial (Fin (n + 1)) R) :
    chartRehom j (chartHomogenize j F) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j)) F :=
  AlgHom.congr_fun (chartRehom_comp_chartHomogenize j) F

/-- The dehomogenization of a form multiplied by the selected coordinate to its degree
is precisely the original form in the localization. -/
theorem chartRatioHom_dehom_mul_pow (j : Fin (n + 1))
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    chartRatioHom j (coordinateDehom j F) *
        (algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X j)) ^ d =
      algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j)) F := by
  calc
    _ = chartRehom j (Polynomial.C (coordinateDehom j F) * Polynomial.X ^ d) := by
      simp only [map_mul, map_pow, chartRehom_C, chartRehom_X]
    _ = chartRehom j (chartHomogenize j F) :=
      congrArg (chartRehom j) (chartHomogenize_of_isHomogeneous j hF).symm
    _ = _ := chartRehom_chartHomogenize j F

theorem chartRatioHom_dehom_homogeneousComponent_mul_pow (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    chartRatioHom j (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) *
        (algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X j)) ^ d =
      algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j))
        (MvPolynomial.homogeneousComponent d F) :=
  chartRatioHom_dehom_mul_pow j (MvPolynomial.homogeneousComponent_isHomogeneous d F)

end DeJongAlterations.Geometry.ProjectiveIdeal
