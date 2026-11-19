import Hironaka.Geometry.AffineBlowup
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Ideal.Operations

/-!
# Rees algebras after multiplying the ideal by a nonzero principal factor

The forward map is actual polynomial substitution `T ↦ c T`, so degree `d`
is multiplied by `c ^ d`. Its surjectivity follows from the literal ideal-power
identity; cancellation in the domain supplies injectivity and a genuine inverse.
-/

noncomputable section

open Polynomial

namespace Hironaka.Algebra.ReesPrincipalFactor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The actual ideal obtained by multiplying the centre by a principal factor. -/
def scaledIdeal (c : A) (I : Ideal A) : Ideal A := Ideal.span {c} * I

/-- Powers of the scaled centre retain exactly the corresponding principal power. -/
theorem scaledIdeal_pow (c : A) (I : Ideal A) (n : ℕ) :
    scaledIdeal c I ^ n = Ideal.span {c ^ n} * I ^ n := by
  rw [scaledIdeal, mul_pow, Ideal.span_singleton_pow]

/-- A coefficient belongs to the actual scaled power exactly when it has a lift. -/
theorem mem_scaledIdeal_pow (c : A) (I : Ideal A) (n : ℕ) (b : A) :
    b ∈ scaledIdeal c I ^ n ↔ ∃ a ∈ I ^ n, c ^ n * a = b := by
  rw [scaledIdeal_pow, Ideal.mem_span_singleton_mul]

/-- Polynomial substitution by `c T` restricts to the actual two Rees subalgebras. -/
def reesScale (c : A) (I : Ideal A) : reesAlgebra I →+* reesAlgebra (scaledIdeal c I) where
  toFun p := ⟨(p : A[X]).comp (C c * X), fun n =>
    (mem_scaledIdeal_pow c I n _).mpr ⟨(p : A[X]).coeff n, p.2 n, by
      rw [comp_C_mul_X_coeff, mul_comm]⟩⟩
  map_one' := Subtype.ext (map_one (compRingHom (C c * X)))
  map_mul' p q := Subtype.ext (map_mul (compRingHom (C c * X)) (p : A[X]) (q : A[X]))
  map_zero' := Subtype.ext (map_zero (compRingHom (C c * X)))
  map_add' p q := Subtype.ext (map_add (compRingHom (C c * X)) (p : A[X]) (q : A[X]))

@[simp]
theorem reesScale_coe (c : A) (I : Ideal A) (p : reesAlgebra I) :
    (reesScale c I p : A[X]) = (p : A[X]).comp (C c * X) := rfl

/-- The actual degree-`n` coefficient is multiplied by `c ^ n`. -/
@[simp]
theorem reesScale_coeff (c : A) (I : Ideal A) (p : reesAlgebra I) (n : ℕ) :
    (reesScale c I p : A[X]).coeff n = (p : A[X]).coeff n * c ^ n :=
  comp_C_mul_X_coeff

/-- The literal polynomial monomial scaling identity. -/
theorem monomial_comp_scale (c a : A) (n : ℕ) :
    (monomial n a).comp (C c * X) = monomial n (c ^ n * a) := by
  ext m
  rw [comp_C_mul_X_coeff]
  by_cases h : n = m
  · subst m
    simp only [coeff_monomial, ite_true, mul_comm]
  · simp only [coeff_monomial, if_neg h, zero_mul]

/-- Scaling preserves the genuine polynomial-degree pieces of the Rees rings. -/
def reesScaleGraded (c : A) (I : Ideal A) :
    reesGrading I →+*ᵍ reesGrading (scaledIdeal c I) where
  __ := reesScale c I
  map_mem {i p} hp := by
    apply (mem_reesGrading_iff _ _ _).mpr
    change (p : A[X]).comp (C c * X) = _
    rw [(mem_reesGrading_iff I i p).mp hp, monomial_comp_scale]
    rw [reesScale_coeff, mul_comm]

/-- Even when the factor is a zero divisor, every target homogeneous piece has a lift. -/
theorem exists_homogeneous_preimage (c : A) (I : Ideal A) (n : ℕ)
    (q : reesAlgebra (scaledIdeal c I)) (hq : q ∈ reesGrading (scaledIdeal c I) n) :
    ∃ p : reesAlgebra I, p ∈ reesGrading I n ∧ reesScale c I p = q := by
  obtain ⟨a, ha, heq⟩ := (mem_scaledIdeal_pow c I n _).mp (q.2 n)
  refine ⟨⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩, ⟨a, rfl⟩, ?_⟩
  apply Subtype.ext
  change (monomial n a).comp (C c * X) = (q : A[X])
  rw [monomial_comp_scale, heq]
  exact ((mem_reesGrading_iff _ _ q).mp hq).symm

/-- Lifting the finite support gives surjectivity of the actual Rees map. -/
theorem reesScale_surjective (c : A) (I : Ideal A) : Function.Surjective (reesScale c I) := by
  intro q
  have lift (n : ℕ) : ∃ a ∈ I ^ n, c ^ n * a = (q : A[X]).coeff n :=
    (mem_scaledIdeal_pow c I n _).mp (q.2 n)
  choose a ha heq using lift
  let p (n : ℕ) : reesAlgebra I :=
    ⟨monomial n (a n), reesAlgebra.monomial_mem.mpr (ha n)⟩
  refine ⟨∑ n ∈ (q : A[X]).support, p n, ?_⟩
  apply Subtype.ext
  change (reesAlgebra (scaledIdeal c I)).val
    (reesScale c I (∑ n ∈ (q : A[X]).support, p n)) = (q : A[X])
  simp only [map_sum]
  change (∑ n ∈ (q : A[X]).support, (monomial n (a n)).comp (C c * X)) = (q : A[X])
  simp only [monomial_comp_scale, heq]
  exact (Polynomial.sum_def _ _).symm.trans (Polynomial.sum_monomial_eq _)

/-- The map is literally the identity on the original coefficient ring. -/
@[simp]
theorem reesScale_algebraMap (c : A) (I : Ideal A) (a : A) :
    reesScale c I (algebraMap A (reesAlgebra I) a) =
      algebraMap A (reesAlgebra (scaledIdeal c I)) a := by
  apply Subtype.ext
  change (C a).comp (C c * X) = C a
  exact C_comp

/-- The corresponding degree-zero homomorphism preserves the native base identification. -/
theorem reesScaleGraded_degreeZero (c : A) (I : Ideal A) :
    (reesScaleGraded c I).gradedZeroRingHom.comp (reesDegreeZeroEquiv I).toRingHom =
      (reesDegreeZeroEquiv (scaledIdeal c I)).toRingHom := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact reesScale_algebraMap c I a

/-- The actual scaled degree-one generator belongs to the actual scaled centre. -/
theorem mul_mem_scaledIdeal (c : A) (I : Ideal A) (a : A) (ha : a ∈ I) :
    c * a ∈ scaledIdeal c I := by
  exact Ideal.mem_span_singleton_mul.mpr ⟨a, ha, rfl⟩

/-- Scaling carries the genuine degree-one chart generator to the scaled generator. -/
theorem reesScaleGraded_degreeOne (c : A) (I : Ideal A) (a : A) (ha : a ∈ I) :
    reesScaleGraded c I (reesDegreeOne I a ha) =
      reesDegreeOne (scaledIdeal c I) (c * a) (mul_mem_scaledIdeal c I a ha) := by
  apply Subtype.ext
  change (monomial 1 a).comp (C c * X) = monomial 1 (c * a)
  simpa only [pow_one] using monomial_comp_scale c a 1

variable [IsDomain A]

/-- Nonzero factors give coefficientwise cancellation and thus injectivity. -/
theorem reesScale_injective (c : A) (I : Ideal A) (hc : c ≠ 0) :
    Function.Injective (reesScale c I) := by
  intro p q hpq
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  have hn := congrArg (fun z : reesAlgebra (scaledIdeal c I) => (z : A[X]).coeff n) hpq
  rw [reesScale_coeff, reesScale_coeff] at hn
  exact mul_right_cancel₀ (pow_ne_zero n hc) hn

/-- The actual Rees substitution is bijective for a nonzero principal factor in a domain. -/
theorem reesScale_bijective (c : A) (I : Ideal A) (hc : c ≠ 0) :
    Function.Bijective (reesScale c I) :=
  ⟨reesScale_injective c I hc, reesScale_surjective c I⟩

/-- A genuine equivalence of the actual Rees rings, not a supplied comparison witness. -/
def reesRingEquiv (c : A) (I : Ideal A) (hc : c ≠ 0) :
    reesAlgebra I ≃+* reesAlgebra (scaledIdeal c I) :=
  RingEquiv.ofBijective (reesScale c I) (reesScale_bijective c I hc)

@[simp]
theorem reesRingEquiv_apply (c : A) (I : Ideal A) (hc : c ≠ 0) (p : reesAlgebra I) :
    reesRingEquiv c I hc p = reesScale c I p := rfl

/-- The genuine inverse preserves the actual degree pieces, by homogeneous lifting. -/
def reesScaleInverseGraded (c : A) (I : Ideal A) (hc : c ≠ 0) :
    reesGrading (scaledIdeal c I) →+*ᵍ reesGrading I where
  __ := (reesRingEquiv c I hc).symm.toRingHom
  map_mem {i q} hq := by
    obtain ⟨p, hp, heq⟩ := exists_homogeneous_preimage c I i q hq
    change (reesRingEquiv c I hc).symm q ∈ reesGrading I i
    rw [← heq]
    change (reesRingEquiv c I hc).symm (reesRingEquiv c I hc p) ∈ reesGrading I i
    simpa only [RingEquiv.symm_apply_apply] using hp

/-- The native graded inverse is a left inverse. -/
theorem reesScaleInverseGraded_comp (c : A) (I : Ideal A) (hc : c ≠ 0) :
    (reesScaleInverseGraded c I hc).comp (reesScaleGraded c I) =
      GradedRingHom.id (reesGrading I) := by
  apply GradedRingHom.ext
  intro p
  change (reesRingEquiv c I hc).symm (reesRingEquiv c I hc p) = p
  exact RingEquiv.symm_apply_apply _ _

/-- The native graded inverse is a right inverse. -/
theorem reesScaleGraded_comp_inverse (c : A) (I : Ideal A) (hc : c ≠ 0) :
    (reesScaleGraded c I).comp (reesScaleInverseGraded c I hc) =
      GradedRingHom.id (reesGrading (scaledIdeal c I)) := by
  apply GradedRingHom.ext
  intro q
  change reesRingEquiv c I hc ((reesRingEquiv c I hc).symm q) = q
  exact RingEquiv.apply_symm_apply _ _

/-- The inverse graded map is genuinely surjective as well. -/
theorem reesScaleInverseGraded_surjective (c : A) (I : Ideal A) (hc : c ≠ 0) :
    Function.Surjective (reesScaleInverseGraded c I hc) :=
  (reesRingEquiv c I hc).symm.surjective

end Hironaka.Algebra.ReesPrincipalFactor
