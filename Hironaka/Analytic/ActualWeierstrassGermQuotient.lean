/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.OkaGermRelations
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false

/-! # Actual Weierstrass polynomial and germ quotients

Natural monic distinguished polynomials produce exact divisibility recovery
and an isomorphism of the existing polynomial and holomorphic-germ quotients.
This does not assume or establish factoriality or nearby primitive families.
-/

noncomputable section
open Filter Topology Polynomial
namespace Hironaka.ActualWeierstrassGermQuotient
open HolGerm OkaGermRelations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Natural distinguished monic polynomials recover actual polynomial
divisibility from divisibility in the actual holomorphic-germ ring. -/
theorem shiftEval_dvd_iff {W : (HolGerm E)[X]} (hW : W.Monic)
    (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0)
    (P : (HolGerm E)[X]) : shiftEval 0 W ∣ shiftEval 0 P ↔ W ∣ P := by
  constructor
  · rintro ⟨c, hc⟩
    have hm := congrArg (shiftEval (E := E) 0) (modByMonic_add_div P W)
    simp only [map_add, map_mul] at hm
    have hrem : shiftEval 0 (P %ₘ W) =
        (c - shiftEval 0 (P /ₘ W)) * shiftEval 0 W := by
      rw [hc] at hm
      linear_combination hm
    have hz := eq_zero_of_shiftEval_eq_mul hW hW0 (P %ₘ W)
      (c - shiftEval 0 (P /ₘ W)) (degree_modByMonic_lt P hW) hrem
    exact (modByMonic_eq_zero_iff_dvd hW).mp hz
  · rintro ⟨Q, hQ⟩
    exact ⟨shiftEval 0 Q, by rw [hQ, map_mul]⟩

/-- Actual Weierstrass division and uniqueness internally produce the
isomorphism between the existing polynomial and holomorphic-germ quotients. -/
def quotientEquiv {W : (HolGerm E)[X]} (hW : W.Monic)
    (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0) :
    ((HolGerm E)[X] ⧸ Ideal.span ({W} : Set (HolGerm E)[X])) ≃+*
      (HolGerm (E × ℂ) ⧸
        Ideal.span ({shiftEval 0 W} : Set (HolGerm (E × ℂ)))) := by
  let I : Ideal (HolGerm (E × ℂ)) := Ideal.span ({shiftEval 0 W} : Set _)
  let F := (Ideal.Quotient.mk I).comp (shiftEval (E := E) 0)
  have hsurj : Function.Surjective F := by
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, ρ, _, hr⟩ := exists_eq_mul_shiftEval_add hW hW0 h
    refine ⟨ρ, ?_⟩
    change Ideal.Quotient.mk I (shiftEval 0 ρ) = Ideal.Quotient.mk I h
    rw [hr, map_add, map_mul]
    have hz : Ideal.Quotient.mk I (shiftEval 0 W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [hz, mul_zero, zero_add]
  have hker : RingHom.ker F = Ideal.span ({W} : Set (HolGerm E)[X]) := by
    ext P
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk I (shiftEval 0 P) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    exact shiftEval_dvd_iff hW hW0 P
  exact (Ideal.quotEquivOfEq hker.symm).trans (F.quotientKerEquivOfSurjective hsurj)

/-- The actual quotient isomorphism preserves and reflects primeness of
natural distinguished monic polynomials, without a supplied prime certificate. -/
theorem prime_shiftEval_iff {W : (HolGerm E)[X]} (hW : W.Monic)
    (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0) :
    Prime (shiftEval 0 W) ↔ Prime W := by
  have hΦ : shiftEval 0 W ≠ 0 := by
    intro h
    apply hW.ne_zero
    apply shiftEval_zero_injective
    simpa only [map_zero] using h
  rw [← Ideal.span_singleton_prime hΦ, ← Ideal.span_singleton_prime hW.ne_zero,
    ← Ideal.Quotient.isDomain_iff_prime, ← Ideal.Quotient.isDomain_iff_prime]
  exact (quotientEquiv hW hW0).symm.toMulEquiv.isDomain_iff

end Hironaka.ActualWeierstrassGermQuotient
