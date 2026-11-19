/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The derivative ideal along an algebra isomorphism

`D(e(J)) = e(D(J))` for a `k`-algebra isomorphism `e : A ≃ₐ[k] B`, and `Dʳ(e(J)) = e(Dʳ(J))` for
the iterates: the `k`-derivations of `B` are the conjugates `e ∘ δ ∘ e⁻¹` of those of `A`
(`Derivation.conjAlgEquiv`), so the generators `δ f` of `D(J)` correspond. This is the case of an
isomorphism of [Kol07, Lemma 74 (4)], the compatibility of `D` with smooth pull-back; it is used on
manifolds for the stalk maps of local analytic isomorphisms
(`Hironaka/Resolution/Analytic/MaximalContact/StalkEquiv.lean`,
`Hironaka/Resolution/Analytic/OrderReduction/BDLemmas.lean`). The derivative ideal is
`Ideal.derivative` of `Hironaka/Algebra/Derivative/Basic.lean`.
-/

@[expose] public section

namespace Derivation

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The conjugate `e ∘ δ ∘ e⁻¹` of a `k`-derivation of `A` along a `k`-algebra isomorphism
`e : A ≃ₐ[k] B`, a `k`-derivation of `B`. -/
def conjAlgEquiv (e : A ≃ₐ[k] B) (δ : Derivation k A A) : Derivation k B B :=
  Derivation.mk' (e.toLinearMap ∘ₗ δ.toLinearMap ∘ₗ e.symm.toLinearMap) fun a b => by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
    change e (δ (e.symm a * e.symm b)) = a • e (δ (e.symm b)) + b • e (δ (e.symm a))
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.apply_symm_apply]

theorem conjAlgEquiv_apply (e : A ≃ₐ[k] B) (δ : Derivation k A A) (b : B) :
    δ.conjAlgEquiv e b = e (δ (e.symm b)) := rfl

end Derivation

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The case of an isomorphism of [Kol07, Lemma 74 (4)]: the derivative of the image ideal is the
image of the derivative. -/
theorem derivative_map_algEquiv (e : A ≃ₐ[k] B) (J : Ideal A) :
    derivative k (J.map e) = (derivative k J).map e := by
  apply le_antisymm
  · rw [derivative_le_iff]
    refine ⟨Ideal.map_mono (le_derivative J), fun δ g hg => ?_⟩
    obtain ⟨f, hf, rfl⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hg
    have h : δ (e f) = e ((δ.conjAlgEquiv e.symm) f) := by
      simp [Derivation.conjAlgEquiv_apply]
    rw [h]
    exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivative _ hf)
  · rw [Ideal.map_le_iff_le_comap, derivative_le_iff]
    refine ⟨fun f hf => Ideal.mem_comap.mpr (le_derivative _ (Ideal.mem_map_of_mem _ hf)),
      fun δ f hf => ?_⟩
    rw [Ideal.mem_comap]
    have h : e (δ f) = (δ.conjAlgEquiv e) (e f) := by
      simp [Derivation.conjAlgEquiv_apply]
    rw [h]
    exact derivation_apply_mem_derivative _ (Ideal.mem_map_of_mem _ hf)

/-- The iterated derivatives along an isomorphism. -/
theorem derivativeIter_map_algEquiv (e : A ≃ₐ[k] B) (r : ℕ) (J : Ideal A) :
    derivativeIter k r (J.map e) = (derivativeIter k r J).map e := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h1 : derivativeIter k (r + 1) (J.map e) = derivative k (derivativeIter k r (J.map e)) :=
      Function.iterate_succ_apply' _ _ _
    have h2 : derivativeIter k (r + 1) J = derivative k (derivativeIter k r J) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, h2, ih, derivative_map_algEquiv]

end Ideal
