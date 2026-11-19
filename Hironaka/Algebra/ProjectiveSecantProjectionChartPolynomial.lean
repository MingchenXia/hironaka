import Hironaka.Algebra.ProjectiveSecantProjectionChartAlgebra
import Hironaka.Algebra.ProjectiveSecantTangentDifferential

/-!
# Exact whole original chart polynomial relation and its actual discarded derivative
-/

noncomputable section

open MvPolynomial AlgebraicGeometry HomogeneousLocalization

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The exact original first-coordinate polynomial splitting intertwines its actual discarded partial with the actual polynomial derivative, in every characteristic. -/
theorem original_finSuccEquiv_pderiv_zero (H : MvPolynomial (Fin (n + 2)) k) :
    Polynomial.derivative (MvPolynomial.finSuccEquiv k (n + 1) H) =
      MvPolynomial.finSuccEquiv k (n + 1) (MvPolynomial.pderiv 0 H) := by
  induction H using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [Polynomial.derivative_mul, MvPolynomial.finSuccEquiv_X_zero, hP, mul_comm]
    · simp [Polynomial.derivative_mul, MvPolynomial.finSuccEquiv_X_succ,
        MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero l), hP, mul_comm]

variable (j : Fin (n + 1)) {S : Type u} [CommRing S] (φ : CoordinateRing k j.succ →+* S)

/-- The literal original homogeneous coefficients map to their actual target-chart ratios. -/
theorem sourceProjectionChartMap_coeff (P : MvPolynomial (Fin (n + 1)) k) :
    sourceProjectionChartMap k n j φ (chartCoefficients k n j P) =
      φ (MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j P)) :=
  sourceProjectionChartMap_ratio k n j φ _

/-- The exact whole original chart polynomial in the actual discarded coordinate. -/
def sourceProjectionPolynomial (H : MvPolynomial (Fin (n + 2)) k) :
    Polynomial (HomogeneousChartRing k j) :=
  (MvPolynomial.finSuccEquiv k (n + 1) H).map (chartCoefficients k n j)

/-- The whole original chart polynomial evaluates to the actual original source map of exact original dehomogenization. -/
theorem sourceProjectionPolynomial_eval (H : MvPolynomial (Fin (n + 2)) k) :
    Polynomial.eval₂ (sourceProjectionChartMap k n j φ) (sourceDiscardedRatio k n j φ)
      (sourceProjectionPolynomial k n j H) = φ (coordinateDehom j.succ H) := by
  rw [sourceProjectionPolynomial, Polynomial.eval₂_map]
  have h : (Polynomial.eval₂RingHom
      ((sourceProjectionChartMap k n j φ).comp (chartCoefficients k n j))
        (sourceDiscardedRatio k n j φ)).comp
      (MvPolynomial.finSuccEquiv k (n + 1)).toRingHom = φ.comp (coordinateDehom j.succ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (C a)) = _
      rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        Polynomial.eval₂_C, RingHom.comp_apply, sourceProjectionChartMap_coeff]
      change φ (MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j (C a))) =
        φ (coordinateDehom j.succ (C a))
      simp [coordinateDehom]
    · intro i
      refine Fin.cases ?_ (fun l => ?_) i
      · change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (MvPolynomial.X 0)) = _
        rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X]
        change sourceDiscardedRatio k n j φ = φ (coordinateDehom j.succ (MvPolynomial.X 0))
        simp only [sourceDiscardedRatio, coordinateDehom, MvPolynomial.aeval_X,
          coordinateDehomCoord, dif_neg (Fin.succ_ne_zero j).symm, discardedChartIndex]
      · change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (MvPolynomial.X l.succ)) = _
        rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval₂_C, RingHom.comp_apply,
          sourceProjectionChartMap_coeff]
        change φ (MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j (MvPolynomial.X l))) =
          φ (coordinateDehom j.succ (MvPolynomial.X l.succ))
        by_cases hl : l = j
        · subst l
          simp [coordinateDehom]
        · simp only [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord,
            dif_neg hl, dif_neg (Fin.succ_inj.not.mpr hl), MvPolynomial.rename_X, chartIndexLift]
  exact DFunLike.congr_fun h H

/-- The actual derivative of the same whole original chart polynomial evaluates to the actual original source map of the same original discarded partial. -/
theorem sourceProjectionPolynomial_eval_derivative (H : MvPolynomial (Fin (n + 2)) k) :
    Polynomial.eval₂ (sourceProjectionChartMap k n j φ) (sourceDiscardedRatio k n j φ)
      (sourceProjectionPolynomial k n j H).derivative = φ (coordinateDehom j.succ (MvPolynomial.pderiv 0 H)) := by
  change Polynomial.eval₂ _ _ ((MvPolynomial.finSuccEquiv k (n + 1) H).map _).derivative = _
  rw [Polynomial.derivative_map, original_finSuccEquiv_pderiv_zero]
  exact sourceProjectionPolynomial_eval k n j φ (MvPolynomial.pderiv 0 H)

end Hironaka.Algebra.ProjectiveSecant
