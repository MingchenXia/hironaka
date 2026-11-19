import Hironaka.Algebra.ProjectiveProjectionFiniteCharts

/-!
# The actual discarded-coordinate ratio is integral on every projection chart

The relation is the very original monic homogeneous form with its original
remaining coordinates dehomogenized. No integral-ratio certificate is supplied.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry HomogeneousLocalization

namespace Hironaka.Algebra.ProjectiveProjectionFinite

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1))) (j : Fin (n + 1))

private local instance chartBaseAlgebra {m : ℕ} (i : Fin (m + 1)) :
    Algebra k (HomogeneousChartRing k i) := homogeneousChartAlgebra i

/-- The original remaining homogeneous coefficients become their actual target-chart ratios. -/
def chartCoefficients : MvPolynomial (Fin (n + 1)) k →+* HomogeneousChartRing k j :=
  (homogeneousChartRatioHom j).toRingHom.comp (coordinateDehom j).toRingHom

/-- Every original homogeneous coefficient retains its literal chart substitution. -/
theorem projectionChartMap_coeff (P : MvPolynomial (Fin (n + 1)) k) :
    projectionChartMap k n J j (chartCoefficients k n j P) =
      fullChartPolynomialMap k n J j (MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j P)) :=
  projectionChartMap_ratio k n J j _

/-- Evaluating the original monic polynomial in the actual discarded ratio is exactly
original dehomogenization on the actual quotient chart, for every original polynomial. -/
theorem chart_eval_relation (F : MvPolynomial (Fin (n + 2)) k) :
    Polynomial.eval₂ (projectionChartMap k n J j) (discardedRatio k n J j)
      ((MvPolynomial.finSuccEquiv k (n + 1) F).map (chartCoefficients k n j)) =
      fullChartPolynomialMap k n J j (coordinateDehom j.succ F) := by
  rw [Polynomial.eval₂_map]
  have h : (Polynomial.eval₂RingHom
      ((projectionChartMap k n J j).comp (chartCoefficients k n j)) (discardedRatio k n J j)).comp
      (MvPolynomial.finSuccEquiv k (n + 1)).toRingHom =
      (fullChartPolynomialMap k n J j).comp (coordinateDehom j.succ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (C a)) = _
      rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        Polynomial.eval₂_C, RingHom.comp_apply, projectionChartMap_coeff]
      change fullChartPolynomialMap k n J j
          (MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j (C a))) =
        fullChartPolynomialMap k n J j (coordinateDehom j.succ (C a))
      simp [coordinateDehom]
    · intro i
      refine Fin.cases ?_ (fun ℓ => ?_) i
      · change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (X 0)) = _
        rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X]
        change discardedRatio k n J j = fullChartPolynomialMap k n J j (coordinateDehom j.succ (X 0))
        simp only [discardedRatio, coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord,
          dif_neg (Fin.succ_ne_zero j).symm, discardedChartIndex]
      · change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (X ℓ.succ)) = _
        rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval₂_C, RingHom.comp_apply,
          projectionChartMap_coeff]
        change fullChartPolynomialMap k n J j
            (MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j (X ℓ))) =
          fullChartPolynomialMap k n J j (coordinateDehom j.succ (X ℓ.succ))
        by_cases hℓ : ℓ = j
        · subst ℓ
          simp [coordinateDehom]
        · simp only [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord,
            dif_neg hℓ, dif_neg (Fin.succ_inj.not.mpr hℓ), MvPolynomial.rename_X, chartIndexLift]
  exact DFunLike.congr_fun h F

/-- The actual discarded-coordinate ratio is internally integral on every actual chart. -/
theorem discardedRatio_isIntegral
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _)) :
    letI := (projectionChartMap k n J j).toAlgebra
    IsIntegral (HomogeneousChartRing k j) (discardedRatio k n J j) := by
  let := (projectionChartMap k n J j).toAlgebra
  obtain ⟨d, F, hFJ, hFhom, hFmon⟩ := exists_monic_homogeneous_form k n J hout
  refine ⟨(MvPolynomial.finSuccEquiv k (n + 1) F).map (chartCoefficients k n j), hFmon.map _, ?_⟩
  change Polynomial.eval₂ (projectionChartMap k n J j) _ _ = 0
  rw [chart_eval_relation]
  exact fullChartPolynomialMap_dehom_eq_zero k n J j hFJ

/-- Every literal chart map of the original projective projection is genuinely finite. -/
theorem projectionChartMap_finite
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _)) :
    (projectionChartMap k n J j).Finite := by
  let := (projectionChartMap k n J j).toAlgebra
  let S := Algebra.adjoin (HomogeneousChartRing k j) {discardedRatio k n J j}
  let : Module.Finite (HomogeneousChartRing k j) S :=
    Algebra.finite_adjoin_simple_of_isIntegral (discardedRatio_isIntegral k n J j hout)
  exact Module.Finite.of_surjective S.val.toLinearMap (by
    intro z
    refine ⟨⟨z, ?_⟩, rfl⟩
    change z ∈ Algebra.adjoin (HomogeneousChartRing k j) _
    rw [chart_adjoin_discardedRatio_eq_top]
    trivial)

end Hironaka.Algebra.ProjectiveProjectionFinite
