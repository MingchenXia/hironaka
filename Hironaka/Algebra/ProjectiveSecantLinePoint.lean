import Hironaka.Algebra.ProjectiveProjectionFiniteRelevance

/-!
# Relevant original homogeneous primes supported at a coordinate endpoint
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- Original relevance and vanishing of every remaining coordinate force the literal original endpoint prime. -/
theorem eq_centrePoint_of_remaining_mem (p : projectiveSpace k (n + 1))
    (htail : ∀ j : Fin (n + 1), X j.succ ∈ p.asHomogeneousIdeal) : p = centrePoint k n := by
  let I := p.asHomogeneousIdeal.toIdeal
  let : I.IsPrime := p.isPrime
  let D := MvPolynomial (Fin (n + 2)) k ⧸ I
  let ψ : MvPolynomial (Fin (n + 2)) k →+* D := Ideal.Quotient.mk I
  let b := ψ (X 0)
  have hb : b ≠ 0 := by
    intro h
    have hzero : X (0 : Fin (n + 2)) ∈ p.asHomogeneousIdeal := Ideal.Quotient.eq_zero_iff_mem.mp h
    apply p.not_irrelevant_le
    change (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).toIdeal ≤ _
    rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Fin.cases hzero (fun j => htail j) j
  have hψ : ψ = (Polynomial.eval₂RingHom (algebraMap k D) b).comp
      ((MvPolynomial.uniqueAlgEquiv k Unit).toRingHom.comp (centreGradedMap k n).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ψ, centreGradedMap, MvPolynomial.uniqueAlgEquiv]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [centreGradedMap, MvPolynomial.uniqueAlgEquiv, b]
      · change ψ (X j.succ) = Polynomial.eval₂ _ _
          ((MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n (X j.succ)))
        rw [centreGradedMap_X_succ, map_zero, Polynomial.eval₂_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (htail j)
  apply ProjectiveSpectrum.ext
  apply HomogeneousSubmodule.ext'
  intro d F hF
  change F ∈ I ↔ centreGradedMap k n F = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ψ F = 0 ↔ centreGradedMap k n F = 0
  have hψF : ψ F = algebraMap k D (F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d)) * b ^ d := by
    rw [hψ]
    change Polynomial.eval₂ (algebraMap k D) b ((MvPolynomial.uniqueAlgEquiv k Unit) (centreGradedMap k n F)) = _
    rw [centreGradedMap_homogeneous k n hF, Polynomial.eval₂_monomial]
  have hcentre : centreGradedMap k n F = 0 ↔ F.coeff ((0 : Fin (n + 1) →₀ ℕ).cons d) = 0 := by
    constructor
    · intro hz
      have hc := congrArg (fun P : MvPolynomial Unit k => ((MvPolynomial.uniqueAlgEquiv k Unit) P).coeff d) hz
      rw [centreGradedMap_homogeneous k n hF, map_zero, Polynomial.coeff_zero, Polynomial.coeff_monomial] at hc
      simpa using hc
    · intro hz
      apply (MvPolynomial.uniqueAlgEquiv k Unit).injective
      simp only [centreGradedMap_homogeneous k n hF, hz, map_zero]
  rw [hcentre, hψF]
  simp only [mul_eq_zero, pow_ne_zero d hb, or_false, map_eq_zero]

end Hironaka.Algebra.ProjectiveSecant
