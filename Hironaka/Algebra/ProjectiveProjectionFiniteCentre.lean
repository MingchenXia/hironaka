import Hironaka.Geometry.ProjectiveIdealQuotient
import Hironaka.Geometry.ProjectiveIdealCharts
import Hironaka.Algebra.ProjectiveIdealPolynomialGrading
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# The standard projective centre and an internally obtained original monic relation

The hypothesis is avoidance of the actual native projective point. The
original homogeneous form and its monic polynomial are outputs.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry TopologicalSpace

namespace Hironaka.Algebra.ProjectiveProjectionFinite

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The original homogeneous substitution defining the actual standard centre. -/
def centreGradedMap : ProjectiveGrading k (n + 1) →+*ᵍ
    MvPolynomial.homogeneousSubmodule Unit k where
  __ := (MvPolynomial.aeval (Fin.cases (MvPolynomial.X ()) (fun _ => 0)) :
    MvPolynomial (Fin (n + 2)) k →ₐ[k] MvPolynomial Unit k).toRingHom
  map_mem {i} {F} hF := by
    have hcoord (j : Fin (n + 2)) :
        (Fin.cases (MvPolynomial.X ()) (fun _ => 0) j : MvPolynomial Unit k).IsHomogeneous 1 := by
      refine Fin.cases ?_ (fun _ => ?_) j
      · exact MvPolynomial.isHomogeneous_X _ _
      · exact MvPolynomial.isHomogeneous_zero Unit k 1
    change ((MvPolynomial.aeval (Fin.cases (MvPolynomial.X ()) (fun _ => 0))) F).IsHomogeneous i
    simpa only [one_mul] using hF.aeval _ hcoord

@[simp]
theorem centreGradedMap_X_zero : centreGradedMap k n (X 0) = X () := by
  simp [centreGradedMap]

@[simp]
theorem centreGradedMap_X_succ (i : Fin (n + 1)) : centreGradedMap k n (X i.succ) = 0 := by
  simp [centreGradedMap]

/-- The literal native rational projective point (1:0:...:0). -/
def centrePoint : ProjectiveSpectrum (ProjectiveGrading k (n + 1)) where
  asHomogeneousIdeal := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Unit k)).comap
    (centreGradedMap k n)
  isPrime := (inferInstance : (⊥ : Ideal (MvPolynomial Unit k)).IsPrime).comap
    (centreGradedMap k n).toRingHom
  not_irrelevant_le h := by
    have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 2))))
    change centreGradedMap k n (X 0) = 0 at hX
    rw [centreGradedMap_X_zero] at hX
    exact MvPolynomial.X_ne_zero () hX

/-- The actual standard-centre substitution agrees with literal coefficient specialization. -/
theorem centreGradedMap_univariate :
    (MvPolynomial.uniqueAlgEquiv k Unit).toRingHom.comp (centreGradedMap k n).toRingHom =
      (Polynomial.mapRingHom (MvPolynomial.constantCoeff : MvPolynomial (Fin (n + 1)) k →+* k)).comp
        (MvPolynomial.finSuccEquiv k (n + 1)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [centreGradedMap, MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MvPolynomial.uniqueAlgEquiv, MvPolynomial.finSuccEquiv_X_zero]
    · simp [MvPolynomial.finSuccEquiv_X_succ]

/-- Every coefficient of the actual centre polynomial is an original pure-X0 coefficient. -/
theorem centreGradedMap_coeff (F : MvPolynomial (Fin (n + 2)) k) (d : ℕ) :
    ((MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n F)).coeff d =
      F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d) := by
  have h := DFunLike.congr_fun (centreGradedMap_univariate k n) F
  change (MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n F) = _ at h
  rw [h]
  change (Polynomial.map MvPolynomial.constantCoeff (MvPolynomial.finSuccEquiv k (n + 1) F)).coeff d = _
  rw [Polynomial.coeff_map]
  exact MvPolynomial.finSuccEquiv_coeff_coeff _ F d

/-- An actual homogeneous form has only its degree-th pure-X0 term at the actual centre. -/
theorem centreGradedMap_homogeneous {F : MvPolynomial (Fin (n + 2)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    (MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n F) =
      Polynomial.monomial d (F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d)) := by
  apply Polynomial.ext
  intro i
  rw [centreGradedMap_coeff, Polynomial.coeff_monomial]
  by_cases hid : d = i
  · subst i
    simp
  · rw [if_neg hid]
    apply hF.coeff_eq_zero
    simpa [Finsupp.cons_zero_eq_single_zero] using Ne.symm hid

/-- Outside-ness supplies an actual original homogeneous form with nonzero pure-X0 coefficient. -/
theorem exists_homogeneous_form (J : HomogeneousIdeal (ProjectiveGrading k (n + 1)))
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 2)) k),
      F ∈ J ∧ F.IsHomogeneous d ∧ F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hout
  intro F hF
  change centreGradedMap k n F = 0
  rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply (MvPolynomial.uniqueAlgEquiv k Unit).injective
  rw [map_zero, centreGradedMap_homogeneous k n (MvPolynomial.homogeneousComponent_isHomogeneous d F)]
  have hJ : MvPolynomial.homogeneousComponent d F ∈ J := by
    rw [← proj_eq_homogeneousComponent]
    exact J.isHomogeneous d hF
  rw [h d (MvPolynomial.homogeneousComponent d F) hJ
    (MvPolynomial.homogeneousComponent_isHomogeneous d F), Polynomial.monomial_zero_right]

/-- A homogeneous form's highest possible X0 coefficient is the original constant pure-X0 coefficient. -/
theorem homogeneous_univariate_coeff {F : MvPolynomial (Fin (n + 2)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    (MvPolynomial.finSuccEquiv k (n + 1) F).coeff d =
      MvPolynomial.C (F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d)) := by
  have hc := hF.finSuccEquiv_coeff_isHomogeneous d 0 (Nat.add_zero d)
  have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    (Nat.eq_zero_of_le_zero hc.totalDegree_le)
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at heq
  exact heq

/-- Outside-ness internally produces the actual original homogeneous monic relation. -/
theorem exists_monic_homogeneous_form (J : HomogeneousIdeal (ProjectiveGrading k (n + 1)))
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 2)) k), F ∈ J ∧ F.IsHomogeneous d ∧
      (MvPolynomial.finSuccEquiv k (n + 1) F).Monic := by
  obtain ⟨d, F, hJ, hF, hc⟩ := exists_homogeneous_form k n J hout
  let c := F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d)
  let G := MvPolynomial.C c⁻¹ * F
  have hG : G.IsHomogeneous d := by
    simpa using (MvPolynomial.isHomogeneous_C _ c⁻¹).mul hF
  refine ⟨d, G, J.toIdeal.mul_mem_left _ hJ, hG, ?_⟩
  apply Polynomial.monic_of_degree_le d
  · exact (Polynomial.degree_le_of_natDegree_le (le_trans (by
      rw [MvPolynomial.natDegree_finSuccEquiv]
      exact MvPolynomial.degreeOf_le_totalDegree G 0) hG.totalDegree_le))
  · rw [homogeneous_univariate_coeff k n hG]
    simp only [G, c, MvPolynomial.coeff_C_mul]
    rw [inv_mul_cancel₀ hc, map_one]

end Hironaka.Algebra.ProjectiveProjectionFinite
