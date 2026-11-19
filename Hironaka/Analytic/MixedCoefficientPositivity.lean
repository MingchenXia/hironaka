import Hironaka.Analytic.PotentialTheory.MixedMongeAmpereBasic
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

/-!
# Positivity of the mixed coefficient on positive semidefinite inputs

Gram decomposition, slot multilinearity, and the rank-one formula
`C(Q₁,…,Qₙ) = |det V|²` show that the real part of the mixed coefficient of
positive semidefinite matrices is nonnegative.
-/

noncomputable section

open scoped ComplexOrder

namespace Hironaka.MixedMongeAmpere

open Hironaka.MixedMongeAmpere

variable {n : ℕ}

private def matrixRow (j : Fin n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun A := A j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The permutation sum defining the mixed coefficient is multilinear in its
matrix slots. This packages determinant row multilinearity so that Gram sums
can be expanded with `MultilinearMap.map_sum`. -/
private def mixedCoefficientMultilinear :
    MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) ℂ :=
  ∑ σ : Equiv.Perm (Fin n),
    (Matrix.detRowAlternating.toMultilinearMap.compLinearMap
      (fun j => matrixRow j)).domDomCongr σ

@[simp] private theorem mixedCoefficientMultilinear_apply
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficientMultilinear H = mixedCoefficient H := by
  classical
  simp [mixedCoefficientMultilinear, mixedCoefficient, matrixRow, Matrix.det]
  rfl

/-- For rank-one positive inputs, the mixed coefficient is the squared norm
of the determinant of the matrix whose rows are the defining vectors. -/
private theorem mixedCoefficient_vecMulVec (v : Fin n → Fin n → ℂ) :
    mixedCoefficient (fun i => Matrix.vecMulVec (v i) (star (v i))) =
      Matrix.det (fun i j => v i j) * star (Matrix.det (fun i j => v i j)) := by
  classical
  let V : Matrix (Fin n) (Fin n) ℂ := fun i j => v i j
  have hterm (σ : Equiv.Perm (Fin n)) :
      Matrix.det (fun j k => Matrix.vecMulVec (v (σ j)) (star (v (σ j))) j k) =
        (∏ j, v (σ j) j) * ((σ.sign : ℂ) * star V.det) := by
    let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => v (σ j) j)
    let W : Matrix (Fin n) (Fin n) ℂ := (V.submatrix σ id).map (starRingEnd ℂ)
    have hmatrix :
        (fun j k => Matrix.vecMulVec (v (σ j)) (star (v (σ j))) j k) = D * W := by
      ext j k
      rw [Matrix.diagonal_mul]
      change v (σ j) j * star (v (σ j) k) =
        v (σ j) j * star (v (σ j) k)
      rfl
    rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
    have hW : W.det = (σ.sign : ℂ) * star V.det := by
      rw [show W.det = star (V.submatrix σ id).det by
        exact ((starRingEnd ℂ).map_det (V.submatrix σ id)).symm]
      rw [Matrix.det_permute]
      simp
    rw [hW]
  rw [mixedCoefficient]
  change (∑ σ : Equiv.Perm (Fin n),
    Matrix.det (fun j k => Matrix.vecMulVec (v (σ j)) (star (v (σ j))) j k)) =
      V.det * star V.det
  simp_rw [hterm]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  change (∑ σ : Equiv.Perm (Fin n), (∏ j, V (σ j) j) * (σ.sign : ℂ)) * star V.det =
    V.det * star V.det
  have hdet : V.det = ∑ σ : Equiv.Perm (Fin n), (∏ j, V (σ j) j) * (σ.sign : ℂ) := by
    simpa [Units.smul_def, mul_comm] using Matrix.det_apply V
  rw [← hdet]

/-- The real part of the actual permutation-sum coefficient is nonnegative
for PSD inputs. A proof is Gram decomposition, slot multilinearity, and the
rank-one formula `C(Q₁,...,Qₙ) = |det V|²`. Individual summands need not be PSD. -/
theorem mixedCoefficient_re_nonneg (H : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i, (H i).PosSemidef) : 0 ≤ (mixedCoefficient H).re := by
  classical
  choose m v hv using fun i => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hH i)
  have hExpand :
      mixedCoefficient H =
        ∑ r : ∀ i, Fin (m i),
          mixedCoefficient (fun i => Matrix.vecMulVec (v i (r i)) (star (v i (r i)))) := by
    rw [← mixedCoefficientMultilinear_apply]
    have hHsum : H = fun i => ∑ a, Matrix.vecMulVec (v i a) (star (v i a)) := by
      funext i
      exact hv i
    rw [hHsum]
    rw [MultilinearMap.map_sum]
    simp only [mixedCoefficientMultilinear_apply]
  rw [hExpand, Complex.re_sum]
  exact Finset.sum_nonneg fun r _ => by
    rw [mixedCoefficient_vecMulVec]
    let z : ℂ := Matrix.det (fun i j => v i (r i) j)
    change 0 ≤ (z * star z).re
    rw [Complex.star_def, Complex.mul_conj]
    simpa using Complex.normSq_nonneg z

end Hironaka.MixedMongeAmpere
