import Hironaka.Algebra.ProjectiveProjectionFiniteCone

/-!
# The original partial-coordinate graded map contracts relevant primes to relevant primes

Outside-ness, and not a false literal irrelevant-ideal containment,
produces the genuine projective relevance condition internally.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Algebra.ProjectiveProjectionFinite

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1)))

/-- The literal degree-preserving partial-coordinate homomorphism of the original quotient. -/
def partialGradedMap : ProjectiveGrading k n →+*ᵍ
    GradedQuotient.grading (ProjectiveGrading k (n + 1)) J.toIdeal :=
  (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal).comp
    { __ := (MvPolynomial.rename Fin.succ).toRingHom
      map_mem h := h.rename_isHomogeneous }

@[simp]
theorem partialGradedMap_X (i : Fin (n + 1)) :
    partialGradedMap k n J (X i) = Ideal.Quotient.mk J.toIdeal (X i.succ) := by
  simp [partialGradedMap, GradedRingHom.comp_apply]

/-- The actual graded map retains the original coefficient-algebra homomorphism. -/
theorem partialGradedMap_toRingHom :
    (partialGradedMap k n J).toRingHom = (partialCoordinateMap k n J).toRingHom := rfl

/-- The actual outside centre forces every contracted native homogeneous prime to be relevant. -/
theorem partialGradedMap_relevant
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _))
    (p : ProjectiveSpectrum (GradedQuotient.grading (ProjectiveGrading k (n + 1)) J.toIdeal)) :
    ¬ HomogeneousIdeal.irrelevant (ProjectiveGrading k n) ≤
      p.asHomogeneousIdeal.comap (partialGradedMap k n J) := by
  intro hp
  have htail (i : Fin (n + 1)) : Ideal.Quotient.mk J.toIdeal (X i.succ) ∈ p.asHomogeneousIdeal := by
    have h := hp (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X k i))
    change partialGradedMap k n J (X i) ∈ p.asHomogeneousIdeal at h
    rwa [partialGradedMap_X] at h
  let I := p.asHomogeneousIdeal.toIdeal
  let : I.IsPrime := p.isPrime
  let D := CoordinateQuotient k n J ⧸ I
  let ψ : MvPolynomial (Fin (n + 2)) k →+* D :=
    (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk J.toIdeal)
  let b := ψ (X 0)
  have hψ : ψ = (Polynomial.eval₂RingHom (algebraMap k D) b).comp
      ((MvPolynomial.uniqueAlgEquiv k Unit).toRingHom.comp (centreGradedMap k n).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ψ, centreGradedMap, MvPolynomial.uniqueAlgEquiv]
      rfl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [centreGradedMap, MvPolynomial.uniqueAlgEquiv, b]
      · change ψ (X j.succ) = Polynomial.eval₂ _ _
          ((MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n (X j.succ)))
        rw [centreGradedMap_X_succ, map_zero, Polynomial.eval₂_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (htail j)
  obtain ⟨d, F, hFJ, hFhom, hc⟩ := exists_homogeneous_form k n J hout
  have hFzero : ψ F = 0 := by
    change Ideal.Quotient.mk I (Ideal.Quotient.mk J.toIdeal F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hFJ, map_zero]
  have hb : b = 0 := by
    rw [hψ] at hFzero
    change Polynomial.eval₂ (algebraMap k D) b
      ((MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n F)) = 0 at hFzero
    rw [centreGradedMap_homogeneous k n hFhom, Polynomial.eval₂_monomial] at hFzero
    have hcoeff : algebraMap k D (F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d)) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k D).injective).mpr hc
    exact eq_zero_of_pow_eq_zero (mul_eq_zero.mp hFzero |>.resolve_left hcoeff)
  have hzero : Ideal.Quotient.mk J.toIdeal (X 0) ∈ p.asHomogeneousIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hb
  apply p.not_irrelevant_le
  rw [← GradedQuotient.map_irrelevant (ProjectiveGrading k (n + 1)) J]
  apply HomogeneousIdeal.map_le_of_le_comap
  change (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).toIdeal ≤ _
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine Fin.cases hzero (fun j => htail j) i

end Hironaka.Algebra.ProjectiveProjectionFinite
