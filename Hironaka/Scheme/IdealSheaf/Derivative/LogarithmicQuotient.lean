/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Hironaka.Algebra.Derivative.Equiv
public import Hironaka.Algebra.Local.QuotientCoords
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Restriction of the logarithmic derivative ideal to the hypersurface

[Kol07, (87.1)]: `D^r(−log S)(I)|_S = D^r(I|_S)`, the logarithmic derivations along `S` restrict to
all the derivations of `S`. At the level of rings: for a surjection `ψ : A → B` of `k`-algebras
with kernel `J` and `Ω_{A/k}` projective (for instance `A` formally smooth over `k`, as the stalks
of a smooth scheme are), `ψ(D(−log J)(I)) = D(ψ(I))` (`Ideal.logDerivative_map_of_surjective`;
`logDerivative_map_mk` for `B = A/J`), and likewise for the iterates
(`logDerivativeIter_map_of_surjective`).

* `⊆`: a `k`-derivation `δ` of `A` preserving `J = ker ψ` **descends** to `B`, `δ_B(ψ a) = ψ(δ a)`
  (`Derivation.descendOfSurjective`: the quotient derivation `quotientOfMapLE` of
  `Hironaka/Algebra/Local/QuotientCoords.lean` on `A/J`, conjugated along the first isomorphism
  theorem `A/J ≅ B`); so `ψ(δ f) = δ_B(ψ f) ∈ D(ψ(I))`.
* `⊇`: a `k`-derivation `δ'` of `B` **lifts** to a `k`-derivation `δ` of `A` preserving `ker ψ`
  with `ψ ∘ δ = δ' ∘ ψ` (`Derivation.exists_preservesIdeal_ker_of_surjective`): through
  `Der_k(A, B) ≅ Hom_A(Ω_{A/k}, B)`, the `A`-linear map `Ω_{A/k} → B` of `δ' ∘ ψ` lifts along the
  surjection `A → B` because `Ω_{A/k}` is projective (Mathlib's `projective_lifting_property`); the
  lift preserves the kernel since `ψ(δ a) = δ'(ψ a) = 0` for `a ∈ ker ψ`. Then
  `δ'(ψ f) = ψ(δ f) ∈ ψ(D(−log J)(I))` for `f ∈ I`, and Leibniz extends this to `ψ(I)`.

In coordinates with `S = (x₁)`, the logarithmic generators `x₁ ∂₁, ∂₂, …` restrict to
`0, ∂̄₂, …`, which is `Dlog_map_quotient` of `Hironaka/Algebra/Local/LogDeriv.lean`; the proof here
needs no coordinates. The conjugation of a derivation by an algebra isomorphism is
`Derivation.conjAlgEquiv` of `Hironaka/Algebra/Derivative/Equiv.lean`.

Used for the logarithmic derivative ideal sheaf
(`Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean`) and for Corollary 89
(`Hironaka/Resolution/Algebraic/Kol07/Corollary89.lean`).
-/

@[expose] public section

open KaehlerDifferential

namespace Derivation

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

variable (ψ : A →ₐ[k] B)

/-- A derivation of `A` preserving the kernel of the surjection `ψ : A → B` descends to a
derivation of `B`, `δ_B(ψ a) = ψ(δ a)` (`quotientOfMapLE` on `A / ker ψ`, transported along
`A / ker ψ ≅ B`). -/
noncomputable def descendOfSurjective (hψ : Function.Surjective ψ) {δ : Derivation k A A}
    (hδ : δ.PreservesIdeal (RingHom.ker ψ)) : Derivation k B B :=
  (δ.quotientOfMapLE _ fun f hf => hδ f hf).conjAlgEquiv
    (Ideal.quotientKerAlgEquivOfSurjective hψ)

theorem descendOfSurjective_apply (hψ : Function.Surjective ψ) {δ : Derivation k A A}
    (hδ : δ.PreservesIdeal (RingHom.ker ψ)) (a : A) :
    descendOfSurjective ψ hψ hδ (ψ a) = ψ (δ a) := by
  rw [descendOfSurjective, conjAlgEquiv_apply, Ideal.quotientKerAlgEquivOfSurjective_symm_apply,
    quotientOfMapLE_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- When `Ω_{A/k}` is projective, every `k`-derivation of `B` lifts through the surjection
`ψ : A → B` to a `k`-derivation of `A` preserving `ker ψ`. -/
theorem exists_preservesIdeal_ker_of_surjective [Module.Projective A (Ω[A⁄k])]
    (hψ : Function.Surjective ψ) (δ' : Derivation k B B) :
    ∃ δ : Derivation k A A, δ.PreservesIdeal (RingHom.ker ψ) ∧ ∀ a, ψ (δ a) = δ' (ψ a) := by
  let _ : Algebra A B := ψ.toRingHom.toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  let d : Derivation k A B := δ'.compAlgebraMap A
  have hsurj : Function.Surjective (Algebra.linearMap A B) := hψ
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (Algebra.linearMap A B)
    d.liftKaehlerDifferential hsurj
  have hδ : ∀ a, ψ (linearMapEquivDerivation k A h a) = δ' (ψ a) := by
    intro a
    have h1 : linearMapEquivDerivation k A h a = h (D k A a) := rfl
    have h2 := LinearMap.congr_fun hh (D k A a)
    rw [LinearMap.comp_apply, Algebra.linearMap_apply, liftKaehlerDifferential_comp_D] at h2
    rw [h1]
    change algebraMap A B (h (D k A a)) = δ' (ψ a)
    rw [h2]
    rfl
  refine ⟨linearMapEquivDerivation k A h, fun a ha => ?_, hδ⟩
  rw [RingHom.mem_ker] at ha ⊢
  rw [hδ a, ha, map_zero]

end Derivation

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- [Kol07, (87.1)] at the level of rings: for a surjection `ψ : A → B` of `k`-algebras with
`Ω_{A/k}` projective, `ψ(D(−log (ker ψ))(I)) = D(ψ(I))`. -/
theorem logDerivative_map_of_surjective [Module.Projective A (Ω[A⁄k])] (ψ : A →ₐ[k] B)
    (hψ : Function.Surjective ψ) (I : Ideal A) :
    (logDerivative k (RingHom.ker ψ) I).map ψ = derivative k (I.map ψ) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    refine logDerivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
      (le_derivative _ (Ideal.mem_map_of_mem _ hf)), fun δ hδ f hf => ?_⟩
    rw [Ideal.mem_comap, ← Derivation.descendOfSurjective_apply ψ hψ hδ]
    exact derivation_apply_mem_derivative _ (Ideal.mem_map_of_mem _ hf)
  · refine derivative_le_iff.mpr ⟨Ideal.map_mono (le_logDerivative _ I), fun δ' x hx => ?_⟩
    obtain ⟨δ, hδ, hcomm⟩ := Derivation.exists_preservesIdeal_ker_of_surjective ψ hψ δ'
    have key : ∀ f ∈ I, δ' (ψ f) ∈ (logDerivative k (RingHom.ker ψ) I).map ψ := fun f hf => by
      rw [← hcomm f]
      exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivative hδ hf)
    change x ∈ Ideal.span (ψ '' (I : Set A)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact key f hf
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul b x hx' hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx)
        (Ideal.mul_mem_right _ _ (Ideal.map_mono (le_logDerivative _ I) hx'))

/-- The iterates: `ψ(D^r(−log (ker ψ))(I)) = D^r(ψ(I))`. -/
theorem logDerivativeIter_map_of_surjective [Module.Projective A (Ω[A⁄k])] (ψ : A →ₐ[k] B)
    (hψ : Function.Surjective ψ) (r : ℕ) (I : Ideal A) :
    (logDerivativeIter k (RingHom.ker ψ) r I).map ψ = derivativeIter k r (I.map ψ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [logDerivativeIter_succ, derivativeIter_succ, logDerivative_map_of_surjective ψ hψ, ih]

/-- The same for a ring map `ψ` compatible with the `k`-structures (the stalk map of a closed
immersion of `k`-schemes). -/
theorem logDerivativeIter_map_of_surjective' [Module.Projective A (Ω[A⁄k])] (ψ : A →+* B)
    (hc : ∀ c : k, ψ (algebraMap k A c) = algebraMap k B c) (hψ : Function.Surjective ψ) (r : ℕ)
    (I : Ideal A) :
    (logDerivativeIter k (RingHom.ker ψ) r I).map ψ = derivativeIter k r (I.map ψ) :=
  logDerivativeIter_map_of_surjective { ψ with commutes' := hc } hψ r I

/-- [Kol07, (87.1)] for a quotient: for `A` formally smooth over `k` and any ideal `J`,
`D(−log J)(I) · (A/J) = D(I · (A/J))`. -/
theorem logDerivative_map_mk [Algebra.FormallySmooth k A] (J I : Ideal A) :
    (logDerivative k J I).map (Ideal.Quotient.mk J) =
      derivative k (I.map (Ideal.Quotient.mk J)) := by
  have hker : RingHom.ker (Ideal.Quotient.mkₐ k J) = J := Ideal.ext fun a => by
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  have h := logDerivative_map_of_surjective (Ideal.Quotient.mkₐ k J)
    (Ideal.Quotient.mkₐ_surjective k J) I
  rw [hker] at h
  exact h

end Ideal
