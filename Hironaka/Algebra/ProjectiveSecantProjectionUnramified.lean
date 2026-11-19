import Mathlib.RingTheory.Unramified.Field

/-!
# An actual monogenic relation with invertible derivative is formally unramified

The native square-zero Taylor argument adapts the proof in
Mathlib/RingTheory/Unramified/Field.lean, SHA256
f5b5f16c8f436a5b63f025518b05ffa4ee020bd4b8f1082bdb93b1d9c7e70cb8.
This is an algebraic helper. The original projection construction must
produce its actual relation and derivative unit internally.
-/

noncomputable section

open Polynomial Algebra

namespace Hironaka.Algebra.ProjectiveSecant

/-- Actual original monogenic algebra generation and an actual original relation with invertible derivative give genuine formal unramifiedness. -/
theorem formallyUnramified_of_monogenic_relation {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (t : S) (hgen : Algebra.adjoin R {t} = ⊤) (G : R[X]) (hG : Polynomial.aeval t G = 0)
    (hG' : IsUnit (Polynomial.aeval t G.derivative)) : Algebra.FormallyUnramified R S := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f₁ f₂ e
  have ht : f₁ t = f₂ t := by
    have hd : f₁ t - f₂ t ∈ I := by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e t
    have h := Polynomial.eval_add_of_sq_eq_zero (G.map (algebraMap R B)) (f₂ t)
      (f₁ t - f₂ t) (show (f₁ t - f₂ t) ^ 2 ∈ ⊥ from hI ▸ Ideal.pow_mem_pow hd 2)
    simp only [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply, hG, map_zero,
      derivative_map, zero_add] at h
    rwa [eq_comm, (hG'.map f₂).mul_right_eq_zero, sub_eq_zero] at h
  have hsurj : Function.Surjective (Polynomial.aeval (R := R) t) :=
    (AlgHom.range_eq_top _).mp ((Algebra.adjoin_singleton_eq_range_aeval R t).symm.trans hgen)
  ext z
  obtain ⟨P, rfl⟩ := hsurj z
  rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, ht]

end Hironaka.Algebra.ProjectiveSecant
