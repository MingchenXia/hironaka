/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.Algebra.Tower

/-!
# A local ring in gluing form with two branches: the jets of its two branches

Let `A ⊆ B` be the local ring of a curve at a point `x` and the semilocal ring of its normalization
over `x`, where `B` has exactly two maximal ideals `𝔫₁ ≠ 𝔫₂` (the two points of `x̃`), both with
residue field `k`, and `A` is the **gluing subalgebra** of `B`: an element of `B` lies in `A` as
soon as it takes the same value `c ∈ k` at `𝔫₁` and `𝔫₂` (M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification/source/
semi-stable.tex`, App. B, l. 4383–4387; CRV1's `CurvesField.gluing`). Let `D_i = B_{𝔫_i}` (the
local rings of the normalization at the two branches) and `φ_i : A → D_i`.

This file proves the three properties of the pair `(φ₁, φ₂)` from which
`CurvesField.OrdinaryGluing.nonempty_completion_algEquiv_formalUV` computes the completion of `A`:

* `exists_sub_mem_maximalIdeal`: every `a ∈ A` is congruent to a constant modulo `𝔪_A` (the residue
  field of `A` is `k`);
* `mem_maximalIdeal_pow_of_branches` (**the topology of `A` is induced by the branches**): if
  `φ_i(a) ∈ 𝔪_{D_i}^N` for `i = 1, 2`, then `a ∈ 𝔪_A^N`. Indeed `a ∈ 𝔫₁^N ∩ 𝔫₂^N = (𝔫₁𝔫₂)^N`, and
  `(𝔫₁𝔫₂)^N` is the image of `𝔪_A^N` for `N ≥ 1`, since `𝔫₁𝔫₂ ⊆ 𝔫₁ ∩ 𝔫₂ ⊆ A`;
* `exists_branches_approx` (**approximation of the branches**): for `d_i ∈ D_i` with the same
  residue `c ∈ k`, there is `a ∈ A` with `φ_i(a) ≡ d_i mod 𝔪_{D_i}^N` (Chinese remainder theorem
  in `B` and the gluing condition).

Blueprint: `sm-curves-fields-ordinary-gluing.tex`, `lem:sm-og-branch-jets`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

open IsLocalRing

set_option autoImplicit false

noncomputable section

section Approximation

variable {B : Type*} [CommRing B] (n : Ideal B) [hn : n.IsMaximal]

/-- Elements of `B_𝔫` are approximated by elements of `B` modulo every power of the maximal
ideal: for `d = b / s` with `s ∉ 𝔫`, write `s s' + t = 1` with `t ∈ 𝔫^N`; then `b s' ≡ d`. -/
theorem exists_algebraMap_sub_mem_pow (N : ℕ) (d : Localization.AtPrime n) :
    ∃ b : B, algebraMap B (Localization.AtPrime n) b - d ∈
      maximalIdeal (Localization.AtPrime n) ^ N := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective n.primeCompl d
  have hs : (s : B) ∉ n := s.2
  have h1 : IsCoprime (Ideal.span {(s : B)}) n := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := hn.eq_of_le h le_sup_right
    have hmem : (s : B) ∈ Ideal.span {(s : B)} ⊔ n :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    rw [← heq] at hmem
    exact hs hmem
  obtain ⟨i, hi, t, ht, hit⟩ := (h1.pow_right (n := N)).exists
  obtain ⟨s', rfl⟩ := Ideal.mem_span_singleton'.1 hi
  refine ⟨b * s', ?_⟩
  have hu : IsLocalization.mk' (Localization.AtPrime n) b s *
      algebraMap B (Localization.AtPrime n) s = algebraMap B (Localization.AtPrime n) b :=
    IsLocalization.mk'_spec _ b s
  have heq : algebraMap B (Localization.AtPrime n) (b * s') -
      IsLocalization.mk' (Localization.AtPrime n) b s =
      -(IsLocalization.mk' (Localization.AtPrime n) b s * algebraMap B _ t) := by
    have h2 : algebraMap B (Localization.AtPrime n) s' * algebraMap B _ s +
        algebraMap B _ t = 1 := by
      rw [← map_mul, ← map_add, hit, map_one]
    rw [map_mul]
    linear_combination (-(algebraMap B (Localization.AtPrime n) s')) * hu +
      (IsLocalization.mk' (Localization.AtPrime n) b s) * h2
  rw [heq]
  refine (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ ?_)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal n, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ht

/-- An element of `B` whose image in `B_𝔫` lies in `𝔪^N` lies in `𝔫^N`. -/
theorem mem_pow_of_algebraMap_mem (N : ℕ) {b : B}
    (hb : algebraMap B (Localization.AtPrime n) b ∈ maximalIdeal (Localization.AtPrime n) ^ N) :
    b ∈ n ^ N := by
  rw [← IsLocalization.AtPrime.under_maximalIdeal_pow n (Localization.AtPrime n) N]
  exact hb

/-- The image of `𝔫^N` in `B_𝔫` lies in `𝔪^N`. -/
theorem algebraMap_mem_pow {N : ℕ} {b : B} (hb : b ∈ n ^ N) :
    algebraMap B (Localization.AtPrime n) b ∈ maximalIdeal (Localization.AtPrime n) ^ N := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal n, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hb

end Approximation

section Branches

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
  [Algebra A B] [Algebra.IsIntegral A B] [Algebra k A] [Algebra k B] [IsScalarTower k A B]
  (n₁ n₂ : Ideal B) [n₁.IsMaximal] [n₂.IsMaximal]

/-- The contraction of a maximal ideal of `B` is the maximal ideal of `A`. -/
theorem comap_eq_maximalIdeal (n : Ideal B) [n.IsMaximal] :
    n.comap (algebraMap A B) = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)

include n₁ in
/-- **The residue field of `A` is `k`** if that of some maximal ideal of `B` is. -/
theorem exists_sub_mem_maximalIdeal (hres : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ n₁)
    (a : A) : ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A := by
  obtain ⟨c, hc⟩ := hres (algebraMap A B a)
  refine ⟨c, ?_⟩
  rw [← comap_eq_maximalIdeal n₁, Ideal.mem_comap, map_sub, ← IsScalarTower.algebraMap_apply]
  exact hc

omit [Algebra k A] [IsScalarTower k A B] [n₂.IsMaximal] in
/-- Products of `N ≥ 1` elements of `𝔫₁ 𝔫₂` come from `𝔪_A^N`, when `A` is the gluing subalgebra. -/
theorem exists_mem_pow_of_mem_mul_pow
    (hgl : ∀ b : B, (∃ c : k, b - algebraMap k B c ∈ n₁ ∧ b - algebraMap k B c ∈ n₂) →
      ∃ a : A, algebraMap A B a = b) :
    ∀ N : ℕ, ∀ b ∈ (n₁ * n₂) ^ (N + 1), ∃ a ∈ maximalIdeal A ^ (N + 1), algebraMap A B a = b := by
  have base : ∀ b ∈ n₁ * n₂, ∃ a ∈ maximalIdeal A, algebraMap A B a = b := by
    intro b hb
    obtain ⟨h1, h2⟩ : b ∈ n₁ ⊓ n₂ := Ideal.mul_le_inf hb
    obtain ⟨a, rfl⟩ := hgl b ⟨0, by simpa using h1, by simpa using h2⟩
    refine ⟨a, ?_, rfl⟩
    rw [← comap_eq_maximalIdeal n₁]
    exact h1
  intro N
  induction N with
  | zero => simpa using base
  | succ N ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, ha, rfl⟩ := ih x hx
      obtain ⟨a', ha', rfl⟩ := base y hy
      refine ⟨a * a', ?_, map_mul _ _ _⟩
      rw [pow_succ]
      exact Ideal.mul_mem_mul ha ha'
    · obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨a', ha', rfl⟩ := hy
      exact ⟨a + a', Ideal.add_mem _ ha ha', map_add _ _ _⟩

omit [Algebra k A] [IsScalarTower k A B] in
/-- **The topology of `A` is induced by its two branches.** If `A` is the gluing subalgebra of
`B` with respect to two distinct maximal ideals `𝔫₁, 𝔫₂`, then `a ∈ A` with
`φ_i(a) ∈ 𝔪_{B_{𝔫_i}}^N` (`i = 1, 2`) lies in `𝔪_A^N`. -/
theorem mem_maximalIdeal_pow_of_branches (hAB : Function.Injective (algebraMap A B))
    (hne : n₁ ≠ n₂)
    (hgl : ∀ b : B, (∃ c : k, b - algebraMap k B c ∈ n₁ ∧ b - algebraMap k B c ∈ n₂) →
      ∃ a : A, algebraMap A B a = b)
    (N : ℕ) (a : A)
    (h₁ : algebraMap B (Localization.AtPrime n₁) (algebraMap A B a) ∈
      maximalIdeal (Localization.AtPrime n₁) ^ N)
    (h₂ : algebraMap B (Localization.AtPrime n₂) (algebraMap A B a) ∈
      maximalIdeal (Localization.AtPrime n₂) ^ N) :
    a ∈ maximalIdeal A ^ N := by
  rcases N with _ | N
  · simp
  have hb₁ := mem_pow_of_algebraMap_mem n₁ _ h₁
  have hb₂ := mem_pow_of_algebraMap_mem n₂ _ h₂
  have hcop : IsCoprime (n₁ ^ (N + 1)) (n₂ ^ (N + 1)) :=
    (Ideal.isCoprime_of_isMaximal hne).pow
  have hmem : algebraMap A B a ∈ (n₁ * n₂) ^ (N + 1) := by
    rw [mul_pow, Ideal.mul_eq_inf_of_isCoprime hcop]
    exact ⟨hb₁, hb₂⟩
  obtain ⟨a', ha', he⟩ := exists_mem_pow_of_mem_mul_pow n₁ n₂ hgl N _ hmem
  rw [← hAB he]
  exact ha'

omit [IsLocalRing A] [Algebra.IsIntegral A B] [Algebra k A] [IsScalarTower k A B] in
/-- **Approximation of the branches.** If `A` is the gluing subalgebra of `B` with respect to two
distinct maximal ideals `𝔫₁, 𝔫₂`, then for `d_i ∈ B_{𝔫_i}` with the same residue `c ∈ k` and every
`N` there is `a ∈ A` with `φ_i(a) ≡ d_i` modulo `𝔪_{B_{𝔫_i}}^N` for `i = 1, 2`. -/
theorem exists_branches_approx (hne : n₁ ≠ n₂)
    (hgl : ∀ b : B, (∃ c : k, b - algebraMap k B c ∈ n₁ ∧ b - algebraMap k B c ∈ n₂) →
      ∃ a : A, algebraMap A B a = b)
    (N : ℕ) (d₁ : Localization.AtPrime n₁) (d₂ : Localization.AtPrime n₂) (c : k)
    (hd₁ : d₁ - algebraMap k (Localization.AtPrime n₁) c ∈ maximalIdeal (Localization.AtPrime n₁))
    (hd₂ : d₂ - algebraMap k (Localization.AtPrime n₂) c ∈
      maximalIdeal (Localization.AtPrime n₂)) :
    ∃ a : A, algebraMap B (Localization.AtPrime n₁) (algebraMap A B a) - d₁ ∈
        maximalIdeal (Localization.AtPrime n₁) ^ N ∧
      algebraMap B (Localization.AtPrime n₂) (algebraMap A B a) - d₂ ∈
        maximalIdeal (Localization.AtPrime n₂) ^ N := by
  rcases N with _ | N
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨b₁, hb₁⟩ := exists_algebraMap_sub_mem_pow n₁ (N + 1) d₁
  obtain ⟨b₂, hb₂⟩ := exists_algebraMap_sub_mem_pow n₂ (N + 1) d₂
  -- the Chinese remainder theorem
  obtain ⟨e₁, he₁, e₂, he₂, he⟩ :=
    ((Ideal.isCoprime_of_isMaximal hne).pow (m := N + 1) (n := N + 1)).exists
  set b := b₁ * e₂ + b₂ * e₁ with hbdef
  have hbb₁ : b - b₁ ∈ n₁ ^ (N + 1) := by
    have : b - b₁ = (b₂ - b₁) * e₁ := by rw [hbdef]; linear_combination b₁ * he
    rw [this]
    exact Ideal.mul_mem_left _ _ he₁
  have hbb₂ : b - b₂ ∈ n₂ ^ (N + 1) := by
    have : b - b₂ = (b₁ - b₂) * e₂ := by rw [hbdef]; linear_combination b₂ * he
    rw [this]
    exact Ideal.mul_mem_left _ _ he₂
  -- the values of `b` at the two branches are `c`
  have hval : ∀ (n : Ideal B) [n.IsMaximal] (b' : B) (d : Localization.AtPrime n),
      b - b' ∈ n ^ (N + 1) →
      algebraMap B (Localization.AtPrime n) b' - d ∈
        maximalIdeal (Localization.AtPrime n) ^ (N + 1) →
      d - algebraMap k (Localization.AtPrime n) c ∈ maximalIdeal (Localization.AtPrime n) →
      b - algebraMap k B c ∈ n := by
    intro n _ b' d hbb' hb' hd
    have h1 : algebraMap B (Localization.AtPrime n) (b' - algebraMap k B c) ∈
        maximalIdeal (Localization.AtPrime n) := by
      have : algebraMap B (Localization.AtPrime n) (b' - algebraMap k B c) =
          (algebraMap B (Localization.AtPrime n) b' - d) +
            (d - algebraMap k (Localization.AtPrime n) c) := by
        rw [map_sub, ← IsScalarTower.algebraMap_apply]
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero N) hb') hd
    have h2 : b' - algebraMap k B c ∈ n := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime n) n]
      exact h1
    have : b - algebraMap k B c = (b - b') + (b' - algebraMap k B c) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero N) hbb') h2
  obtain ⟨a, ha⟩ := hgl b ⟨c, hval n₁ b₁ d₁ hbb₁ hb₁ hd₁, hval n₂ b₂ d₂ hbb₂ hb₂ hd₂⟩
  refine ⟨a, ?_, ?_⟩
  · have : algebraMap B (Localization.AtPrime n₁) (algebraMap A B a) - d₁ =
        algebraMap B (Localization.AtPrime n₁) (b - b₁) +
          (algebraMap B (Localization.AtPrime n₁) b₁ - d₁) := by
      rw [ha, map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ (algebraMap_mem_pow n₁ hbb₁) hb₁
  · have : algebraMap B (Localization.AtPrime n₂) (algebraMap A B a) - d₂ =
        algebraMap B (Localization.AtPrime n₂) (b - b₂) +
          (algebraMap B (Localization.AtPrime n₂) b₂ - d₂) := by
      rw [ha, map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ (algebraMap_mem_pow n₂ hbb₂) hb₂

end Branches

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryGluing
