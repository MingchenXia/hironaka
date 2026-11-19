import Hironaka.Algebra.ProjectiveProjectionFiniteCharts

/-!
# The literal coordinate chart map is exactly the native homogeneous localization map

The full original ring homomorphisms are identified, including the
original quotient ideal and all original homogeneous fractions.
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

/-- The native homogeneous localization map with its literal original source denominator. -/
def nativeProjectionChartMap : HomogeneousChartRing k j →+* QuotientChart k n J j :=
  HomogeneousLocalization.map (partialGradedMap k n J) (by
    rintro x ⟨m, rfl⟩
    exact ⟨m, by rw [map_pow, partialGradedMap_X]⟩)

/-- The exact native map on every original homogeneous numerator. -/
theorem nativeProjectionChartMap_mk (m : ℕ) (F : MvPolynomial (Fin (n + 1)) k)
    (hF : F ∈ ProjectiveGrading k n (m • (1 : ℕ))) :
    nativeProjectionChartMap k n J j (Away.mk _ (MvPolynomial.isHomogeneous_X k j) m F hF) =
      Away.mk _ ((GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal).map_mem
        (MvPolynomial.isHomogeneous_X k j.succ)) m (partialGradedMap k n J F)
        ((partialGradedMap k n J).map_mem hF) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (partialGradedMap k n J F) ⟨partialGradedMap k n J (X j ^ m), _⟩ =
    Localization.mk (partialGradedMap k n J F) ⟨Ideal.Quotient.mk J.toIdeal (X j.succ) ^ m, _⟩
  simp only [map_pow, partialGradedMap_X]

/-- Dehomogenization preserves the original remaining coordinates on the whole polynomial ring. -/
theorem coordinateDehom_rename_succ (F : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial.rename (chartIndexLift n j) (coordinateDehom j F) =
      coordinateDehom j.succ (MvPolynomial.rename Fin.succ F) := by
  have h : (MvPolynomial.rename (chartIndexLift n j) : CoordinateRing k j →ₐ[k]
      CoordinateRing k j.succ).comp (coordinateDehom j) =
      (coordinateDehom j.succ).comp (MvPolynomial.rename Fin.succ) := by
    ext i
    by_cases hi : i = j
    · subst i
      simp [coordinateDehom]
    · simp only [AlgHom.comp_apply, coordinateDehom, MvPolynomial.aeval_X,
        coordinateDehomCoord, dif_neg hi, dif_neg (Fin.succ_inj.not.mpr hi),
        MvPolynomial.rename_X, chartIndexLift]
  exact AlgHom.congr_fun h F

/-- The literal original affine coordinate map equals the entire native Away.map. -/
theorem projectionChartMap_eq_native :
    projectionChartMap k n J j = nativeProjectionChartMap k n J j := by
  apply RingHom.ext
  intro z
  obtain ⟨m, F, hF, rfl⟩ := Away.mk_surjective (ProjectiveGrading k n)
    (MvPolynomial.isHomogeneous_X k j) z
  change fullChartPolynomialMap k n J j
    (MvPolynomial.rename (chartIndexLift n j)
      (homogeneousChartDehom j (Away.mk _ (MvPolynomial.isHomogeneous_X k j) m F hF))) = _
  rw [homogeneousChartDehom_mk, coordinateDehom_rename_succ]
  have hF' : (MvPolynomial.rename Fin.succ F).IsHomogeneous m :=
    (show F.IsHomogeneous m from by simpa using hF).rename_isHomogeneous
  have he := AlgHom.congr_fun (homogeneousChartRatioHom_comp_dehom (R := k) j.succ)
    (Away.mk _ (MvPolynomial.isHomogeneous_X k j.succ) m (MvPolynomial.rename Fin.succ F)
      (by simpa using hF'))
  rw [AlgHom.comp_apply, homogeneousChartDehom_mk, AlgHom.id_apply] at he
  change Away.map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal)
    (X j.succ) (homogeneousChartRatioHom j.succ (coordinateDehom j.succ (MvPolynomial.rename Fin.succ F))) = _
  rw [he, Away.map_mk, nativeProjectionChartMap_mk]
  rfl

end Hironaka.Algebra.ProjectiveProjectionFinite
