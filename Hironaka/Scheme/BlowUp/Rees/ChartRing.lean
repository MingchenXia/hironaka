/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUpAlgebra
public import Hironaka.Scheme.BlowUp.Rees.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The chart rings of the affine blow-up: `(R̃_{at})₀ ≅ R[I/a]`

For `g ∈ I`, the degree-zero elements of the localized Rees algebra `R̃_g` form the ring
`R[I g⁻¹]` of fractions `f/gˡ` with `f ∈ Iˡ` [Hau14, Definition 4.16], and the affine chart
`D₊(a t)` of `Proj` of the Rees algebra is the spectrum of the affine blow-up algebra `R[I/a]`
[Sta, Tag 0804].  This file proves the ring isomorphism behind these statements, between
Mathlib's degree-zero homogeneous localization `HomogeneousLocalization.Away (grading I) (a t)`
of the graded Rees algebra and the affine blow-up algebra `affineBlowUpAlgebra I a ⊆ R_a`.

## The construction

Evaluation at `1/a` is the `R`-algebra map `reesAlgebra I → R_a`, `∑ pₙ tⁿ ↦ ∑ pₙ/aⁿ`
(`reesAlgebra.evalInv`, Mathlib's `Polynomial.aeval` at `IsLocalization.Away.invSelf a`).  It
sends `a t` to `a · (1/a) = 1`, so it extends to the localization `(reesAlgebra I)_{at}`
(`reesAlgebra.awayLift`, by `IsLocalization.Away.lift`) and restricts along `val` to the
degree-zero part (`reesAlgebra.chartHom`).  On the fraction `x tⁿ/(at)ⁿ` it gives `x/aⁿ`
(`reesAlgebra.chartHom_mk_eq_awayFrac`, by the normal form of the grading), so its image lies in
`R[I/a]` and, by `mem_affineBlowUpAlgebra_iff`, is all of it.  Injectivity: if `x/aⁿ = 0` in
`R_a` then `aᵏx = 0` for some `k`, so `(at)ᵏ · x tⁿ = aᵏx · tⁿ⁺ᵏ = 0` and the fraction
`x tⁿ/(at)ⁿ` is already `0` in the localization of the Rees algebra.  The result is
`reesAlgebra.chartRingEquiv a : Away (grading I) (a t) ≃+* affineBlowUpAlgebra I a`, compatible
with the constants: `R → grading I 0 → Away → R[I/a]` is `algebraMap R R[I/a]`
(`reesAlgebra.chartRingEquiv_fromZeroRingHom`).  The ring isomorphism and the constant-map
compatibility are the two halves of "isomorphism of `R`-algebras": Mathlib puts no `R`-algebra
structure on `HomogeneousLocalization`, only one over `grading I 0`, so the ring equivalence is
built first and the compatibility with the constants proved separately.

## Boundary cases

No hypothesis on `a` beyond `a ∈ I` (carried by `a : I`).  For `a` nilpotent both rings are
zero rings and the isomorphism is between singletons; for `a = 1 ∈ I = R` it is
`(R[t]_t)₀ ≅ R`.
-/

@[expose] public section

open AlgebraicGeometry

open Polynomial HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

section EvalInv

/-- Evaluation of the Rees algebra at `1/a`: the `R`-algebra map `reesAlgebra I → R_a`,
`∑ pₙ tⁿ ↦ ∑ pₙ/aⁿ`. -/
noncomputable def reesAlgebra.evalInv (a : R) : reesAlgebra I →ₐ[R] Localization.Away a :=
  (Polynomial.aeval (IsLocalization.Away.invSelf a : Localization.Away a)).comp
    (Subalgebra.val (reesAlgebra I))

variable {I}

theorem reesAlgebra.evalInv_apply (a : R) (p : reesAlgebra I) :
    reesAlgebra.evalInv I a p =
      Polynomial.aeval (IsLocalization.Away.invSelf a : Localization.Away a) (p : R[X]) :=
  rfl

/-- Evaluation at `1/a` sends the monomial `c tⁿ` to `c/aⁿ`. -/
theorem reesAlgebra.evalInv_of_coe_eq_monomial {a : R} {n : ℕ} {c : R} {p : reesAlgebra I}
    (hp : (p : R[X]) = monomial n c) : reesAlgebra.evalInv I a p = awayFrac a n c := by
  rw [reesAlgebra.evalInv_apply, hp, aeval_monomial]
  unfold awayFrac
  rw [Localization.mk_eq_mk'_apply, IsLocalization.eq_mk'_iff_mul_eq]
  change algebraMap R (Localization.Away a) c * IsLocalization.Away.invSelf a ^ n *
    algebraMap R (Localization.Away a) (a ^ n) = algebraMap R (Localization.Away a) c
  rw [map_pow, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf a),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- Evaluation at `1/a` sends the degree-one element `a t` to `1`. -/
theorem reesAlgebra.evalInv_degreeOne (a : I) :
    reesAlgebra.evalInv I a (reesAlgebra.degreeOne I a) = 1 := by
  rw [reesAlgebra.evalInv_of_coe_eq_monomial (reesAlgebra.coe_degreeOne a), awayFrac_one]
  exact Localization.mk_self ⟨(a : R), Submonoid.mem_powers _⟩

end EvalInv

section ChartHom

variable {I}

/-- The ring map `(reesAlgebra I)_{at} → R_a` extending evaluation at `1/a`, which sends the
unit `at` to `1`. -/
noncomputable def reesAlgebra.awayLift (a : I) :
    Localization.Away (reesAlgebra.degreeOne I a) →+* Localization.Away (a : R) :=
  IsLocalization.Away.lift (reesAlgebra.degreeOne I a) (g := (reesAlgebra.evalInv I a).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, reesAlgebra.evalInv_degreeOne]
      exact isUnit_one)

theorem reesAlgebra.awayLift_algebraMap (a : I) (p : reesAlgebra I) :
    reesAlgebra.awayLift a
        (algebraMap (reesAlgebra I) (Localization.Away (reesAlgebra.degreeOne I a)) p) =
      reesAlgebra.evalInv I a p :=
  IsLocalization.Away.lift_eq _ _ p

/-- The chart map: the ring map from the degree-zero part `(R̃_{at})₀` to `R_a`,
`x tⁿ/(at)ⁿ ↦ x/aⁿ` (`reesAlgebra.chartHom_mk_eq_awayFrac`). -/
noncomputable def reesAlgebra.chartHom (a : I) :
    Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a) →+* Localization.Away (a : R) :=
  (reesAlgebra.awayLift a).comp
    (algebraMap (Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a))
      (Localization.Away (reesAlgebra.degreeOne I a)))

/-- Membership in the `n`-th piece written with the degree `n • 1` of `Away.mk`. -/
theorem reesAlgebra.mem_grading_smul_one_iff {n : ℕ} {p : reesAlgebra I} :
    p ∈ reesAlgebra.grading I (n • 1) ↔ p ∈ reesAlgebra.grading I n := by
  rw [smul_eq_mul, mul_one]

theorem reesAlgebra.chartHom_mk (a : I) (n : ℕ) (x : reesAlgebra I)
    (hx : x ∈ reesAlgebra.grading I (n • 1)) :
    reesAlgebra.chartHom a (Away.mk _ (reesAlgebra.degreeOne_mem a) n x hx) =
      reesAlgebra.evalInv I a x := by
  simp only [reesAlgebra.chartHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.mk_eq_mk'_apply]
  unfold reesAlgebra.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  simp [map_pow, reesAlgebra.evalInv_degreeOne]

/-- The chart map sends `x tⁿ/(at)ⁿ` to `x/aⁿ`. -/
theorem reesAlgebra.chartHom_mk_eq_awayFrac (a : I) (n : ℕ) (x : reesAlgebra I)
    (hx : x ∈ reesAlgebra.grading I (n • 1)) :
    reesAlgebra.chartHom a (Away.mk _ (reesAlgebra.degreeOne_mem a) n x hx) =
      awayFrac (a : R) n ((x : R[X]).coeff n) := by
  rw [reesAlgebra.chartHom_mk]
  exact reesAlgebra.evalInv_of_coe_eq_monomial
    (reesAlgebra.eq_monomial_of_mem_grading (reesAlgebra.mem_grading_smul_one_iff.mp hx)).1

/-- The image of the chart map lies in `R[I/a]` (the normal form of the grading and
`Away.mk_surjective`). -/
theorem reesAlgebra.chartHom_mem (a : I)
    (z : Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) :
    reesAlgebra.chartHom a z ∈ affineBlowUpAlgebra I a := by
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective _ (reesAlgebra.degreeOne_mem a) z
  rw [reesAlgebra.chartHom_mk_eq_awayFrac]
  exact awayFrac_mem_affineBlowUpAlgebra n
    (reesAlgebra.eq_monomial_of_mem_grading (reesAlgebra.mem_grading_smul_one_iff.mp hx)).2

/-- Injectivity of the chart map: if `x/aⁿ = 0` in `R_a` then `aᵏx = 0` for some `k`, so `(at)ᵏ`
kills `x tⁿ` and the fraction vanishes in `(R̃_{at})₀`. -/
theorem reesAlgebra.chartHom_injective (a : I) : Function.Injective (reesAlgebra.chartHom a) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective _ (reesAlgebra.degreeOne_mem a) z
  have hx' := reesAlgebra.eq_monomial_of_mem_grading (reesAlgebra.mem_grading_smul_one_iff.mp hx)
  rw [reesAlgebra.chartHom_mk_eq_awayFrac] at hz
  unfold awayFrac at hz
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hz
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨reesAlgebra.degreeOne I a ^ k, k, rfl⟩, Subtype.ext ?_⟩
  change ((reesAlgebra.degreeOne I a ^ k * x : reesAlgebra I) : R[X]) = 0
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, reesAlgebra.coe_degreeOne, monomial_pow, hx'.1,
    monomial_mul_monomial, hk, monomial_zero_right]

/-- **The chart ring isomorphism** `(R̃_{at})₀ ≃+* R[I/a]`, `x tⁿ/(at)ⁿ ↦ x/aⁿ`
[Hau14, Definition 4.16]; [Sta, Tags 0804 and 052P]. -/
noncomputable def reesAlgebra.chartRingEquiv (a : I) :
    Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a) ≃+* affineBlowUpAlgebra I a :=
  RingEquiv.ofBijective
    ((reesAlgebra.chartHom a).codRestrict (affineBlowUpAlgebra I a) (reesAlgebra.chartHom_mem a))
    ⟨fun z w h => reesAlgebra.chartHom_injective a (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
      obtain ⟨n, x, hx, rfl⟩ := (mem_affineBlowUpAlgebra_iff a.2).mp hy
      refine ⟨Away.mk _ (reesAlgebra.degreeOne_mem a) n
        ⟨monomial n x, reesAlgebra.monomial_mem.mpr hx⟩
        (reesAlgebra.mem_grading_smul_one_iff.mpr (reesAlgebra.mem_grading_of_coe_eq_monomial rfl)),
        Subtype.ext ?_⟩
      change reesAlgebra.chartHom a _ = awayFrac (a : R) n x
      rw [reesAlgebra.chartHom_mk_eq_awayFrac]
      congr 1
      exact coeff_monomial_same n x⟩

@[simp]
theorem reesAlgebra.coe_chartRingEquiv_mk (a : I) (n : ℕ) (x : reesAlgebra I)
    (hx : x ∈ reesAlgebra.grading I (n • 1)) :
    (reesAlgebra.chartRingEquiv a (Away.mk _ (reesAlgebra.degreeOne_mem a) n x hx) :
      Localization.Away (a : R)) = awayFrac (a : R) n ((x : R[X]).coeff n) :=
  reesAlgebra.chartHom_mk_eq_awayFrac a n x hx

theorem reesAlgebra.coe_chartRingEquiv_apply (a : I)
    (z : Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) :
    (reesAlgebra.chartRingEquiv a z : Localization.Away (a : R)) = reesAlgebra.chartHom a z :=
  rfl

/-- The `val` of a constant of degree zero in the homogeneous localization is the constant. -/
theorem reesAlgebra.val_fromZeroRingHom (x : Submonoid (reesAlgebra I))
    (f : reesAlgebra.grading I 0) :
    (fromZeroRingHom (reesAlgebra.grading I) x f).val =
      algebraMap (reesAlgebra I) (Localization x) (f : reesAlgebra I) := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

/-- Compatibility with the constants: `R → grading I 0 → (R̃_{at})₀ → R_a` is `algebraMap R R_a`;
with `reesAlgebra.chartRingEquiv` this is the statement that the chart ring isomorphism is one of
`R`-algebras. -/
theorem reesAlgebra.chartHom_fromZeroRingHom (a : I) (r : R) :
    reesAlgebra.chartHom a
        (fromZeroRingHom (reesAlgebra.grading I) _ ((reesAlgebra.gradingZeroEquiv I).symm r)) =
      algebraMap R (Localization.Away (a : R)) r := by
  simp only [reesAlgebra.chartHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    reesAlgebra.val_fromZeroRingHom, reesAlgebra.awayLift_algebraMap]
  change reesAlgebra.evalInv I a (algebraMap R (reesAlgebra I) r) = _
  exact (reesAlgebra.evalInv I a).commutes r

theorem reesAlgebra.chartRingEquiv_fromZeroRingHom (a : I) (r : R) :
    reesAlgebra.chartRingEquiv a
        (fromZeroRingHom (reesAlgebra.grading I) _ ((reesAlgebra.gradingZeroEquiv I).symm r)) =
      algebraMap R (affineBlowUpAlgebra I a) r :=
  Subtype.ext
    ((reesAlgebra.chartHom_fromZeroRingHom a r).trans (Subalgebra.coe_algebraMap _ r).symm)

end ChartHom

