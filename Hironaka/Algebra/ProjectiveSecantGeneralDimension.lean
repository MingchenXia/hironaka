import Hironaka.Algebra.ProjectiveSecantDimension
import Mathlib.RingTheory.Ideal.Maps

/-!
# Original dimension equations without domain or reducedness assumptions
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual injective map from a domain remains injective in an internally obtained prime quotient. -/
theorem exists_prime_quotient_injective
    {R : Type u} {A : Type v} [CommRing R] [IsDomain R] [CommRing A]
    (f : R →+* A) (hf : Function.Injective f) :
    ∃ Q : Ideal A, Q.IsPrime ∧ Function.Injective ((Ideal.Quotient.mk Q).comp f) := by
  have hle : (⊥ : Ideal A).comap f ≤ (⊥ : Ideal R) := by
    intro x hx
    change f x = 0 at hx
    exact Ideal.mem_bot.mpr (hf (hx.trans (map_zero f).symm))
  obtain ⟨Q, _, hQ, hQle⟩ :=
    Ideal.exists_ideal_comap_le_prime (f := f) (⊥ : Ideal R) (⊥ : Ideal A) hle
  refine ⟨Q, hQ, ?_⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply Ideal.mem_bot.mp
  apply hQle
  change f (x - y) ∈ Q
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change ((Ideal.Quotient.mk Q).comp f) (x - y) = 0
  rw [map_sub, hxy, sub_self]

variable (k A : Type u) [Field k] [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- Excess original coordinates cannot inject into any original finite-type algebra of smaller dimension. -/
theorem not_injective_of_dimension_lt_general {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ k →ₐ[k] A) (hdim : ringKrullDim A < Fintype.card σ) :
    ¬ Function.Injective f := by
  intro hf
  obtain ⟨Q, hQ, hQinj⟩ := exists_prime_quotient_injective f.toRingHom hf
  let : Q.IsPrime := hQ
  let g : MvPolynomial σ k →ₐ[k] A ⧸ Q := (Ideal.Quotient.mkₐ k Q).comp f
  exact not_injective_of_dimension_lt k (A ⧸ Q) g
    ((ringKrullDim_quotient_le Q).trans_lt hdim) hQinj

/-- The nonzero relation belongs to the kernel of the whole original map, including original nilpotents. -/
theorem exists_nonzero_relation_of_dimension_lt_general {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ k →ₐ[k] A) (hdim : ringKrullDim A < Fintype.card σ) :
    ∃ F : MvPolynomial σ k, F ≠ 0 ∧ f F = 0 := by
  have h := not_injective_of_dimension_lt_general k A f hdim
  change ¬ (∀ P Q, f P = f Q → P = Q) at h
  push Not at h
  obtain ⟨P, Q, heq, hne⟩ := h
  refine ⟨P - Q, sub_ne_zero.mpr hne, ?_⟩
  simp only [map_sub, heq, sub_self]

end Hironaka.Algebra.ProjectiveSecant
