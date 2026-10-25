import DeJongAlterations.Algebra.ProjectiveIdealChartAlgebra
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual affine Segre chart coordinate maps

Target coordinate ratios map to genuine pure tensors of source ratios.
The row and column substitutions construct an algebraic right inverse on
the whole tensor-product ring, proving actual chart-map surjectivity.
-/

open MvPolynomial
open scoped TensorProduct
open DeJongAlterations.Geometry.ProjectiveIdeal

noncomputable section

namespace DeJongAlterations.Algebra.Segre

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- The actual target projective dimension. -/
def dimension (m n : ℕ) : ℕ := (m + 1) * (n + 1) - 1

/-- Pair coordinates identify with the native finite homogeneous coordinate index. -/
def indexEquiv (m n : ℕ) :
    Fin (m + 1) × Fin (n + 1) ≃ Fin (dimension m n + 1) :=
  finProdFinEquiv.trans (finCongr (by
    exact (Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos n))).symm))

/-- The actual product of normalized source coordinates, as a pure tensor. -/
def chartCoordinate (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : Fin (m + 1)) (l : Fin (n + 1)) :
    CoordinateRing R i ⊗[R] CoordinateRing R j :=
  coordinateDehomCoord i k ⊗ₜ[R] coordinateDehomCoord j l

/-- The Segre homomorphism on the actual affine coordinate polynomial rings. -/
def chartMap (i : Fin (m + 1)) (j : Fin (n + 1)) :
    CoordinateRing R (indexEquiv m n (i, j)) →ₐ[R]
      CoordinateRing R i ⊗[R] CoordinateRing R j :=
  MvPolynomial.aeval fun k =>
    chartCoordinate i j ((indexEquiv m n).symm k.val).1 ((indexEquiv m n).symm k.val).2

/-- The normalized coordinate formula holds for every homogeneous coordinate, including the pivot. -/
theorem chartMap_coordinate (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : Fin (m + 1)) (l : Fin (n + 1)) :
    chartMap (R := R) i j
      (coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (k, l))) =
      chartCoordinate i j k l := by
  by_cases h : (k, l) = (i, j)
  · cases h
    simp [chartMap, chartCoordinate, Algebra.TensorProduct.one_def]
  · have he : indexEquiv m n (k, l) ≠ indexEquiv m n (i, j) :=
      fun he => h ((indexEquiv m n).injective he)
    simp [coordinateDehomCoord, he, chartMap, chartCoordinate]

/-- Lift each left affine coordinate to the corresponding actual target row ratio. -/
def chartLeftSection (i : Fin (m + 1)) (j : Fin (n + 1)) :
    CoordinateRing R i →ₐ[R] CoordinateRing R (indexEquiv m n (i, j)) :=
  MvPolynomial.aeval fun k : ChartIndex i =>
    coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (k.val, j))

/-- Lift each right affine coordinate to the corresponding actual target column ratio. -/
def chartRightSection (i : Fin (m + 1)) (j : Fin (n + 1)) :
    CoordinateRing R j →ₐ[R] CoordinateRing R (indexEquiv m n (i, j)) :=
  MvPolynomial.aeval fun l : ChartIndex j =>
    coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (i, l.val))

/-- Row and column maps give an actual algebraic section on the whole tensor product. -/
def chartSection (i : Fin (m + 1)) (j : Fin (n + 1)) :
    CoordinateRing R i ⊗[R] CoordinateRing R j →ₐ[R]
      CoordinateRing R (indexEquiv m n (i, j)) :=
  Algebra.TensorProduct.lift (chartLeftSection i j) (chartRightSection i j)
    (fun _ _ => Commute.all _ _)

/-- The whole tensor-product section is a right inverse of the actual Segre chart map. -/
theorem chartMap_comp_section (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (chartMap (R := R) i j).comp (chartSection i j) =
      AlgHom.id R (CoordinateRing R i ⊗[R] CoordinateRing R j) := by
  apply Algebra.TensorProduct.ext
  · ext k
    simp [chartSection, chartLeftSection, chartMap_coordinate, chartCoordinate]
  · ext l
    simp [chartSection, chartRightSection, chartMap_coordinate, chartCoordinate]

/-- The actual affine Segre chart map is surjective, with no field or domain assumptions. -/
theorem chartMap_surjective (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Function.Surjective (chartMap (R := R) i j) := by
  intro z
  exact ⟨chartSection i j z, AlgHom.congr_fun (chartMap_comp_section i j) z⟩

/-- Every actual normalized Segre coordinate family satisfies the rank-one relations. -/
theorem chartCoordinate_rank_one (i : Fin (m + 1)) (j : Fin (n + 1))
    (k k' : Fin (m + 1)) (l l' : Fin (n + 1)) :
    chartCoordinate (R := R) i j k l * chartCoordinate i j k' l' =
      chartCoordinate i j k l' * chartCoordinate i j k' l := by
  simp [chartCoordinate, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

end DeJongAlterations.Algebra.Segre
