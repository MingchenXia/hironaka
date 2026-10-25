/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryGluingDVR
import DeJongAlterations.StableModification.CurvesField.OrdinaryGluingBranches
import DeJongAlterations.StableModification.CurvesField.OrdinaryGluingCompletion

/-!
# Gluing form implies completed form for ordinary points with at most two branches (local algebra)

Let `A = 𝒪_{C,x}` be the local ring of a reduced curve over a field `k` at a closed point, `B` the
semilocal ring of the normalization over `x` (a finite `A`-algebra `B ⊇ A`, integrally closed in an
`A`-algebra `L ⊇ B` in which some `s ∈ 𝔪_A` is invertible), and assume that `x` is an ordinary
point in gluing form: all points of `x̃` (the maximal ideals of `B`) are `k`-points and `A` is the
gluing subalgebra `Gl(B) = {b ∈ B | b(x̃₁) = ⋯ = b(x̃ₙ) ∈ k}` (CRV1's `CurvesField.gluing`). This
file proves the converse of CRV4's `eq_gluing_of_isGeometricOrdinaryDoublePoint` and
`eq_gluing_of_isSmoothAt` (blueprint `lem:sm-ordinary-completion`, direction "gluing ⇒ completed"
for `n = 2, 1`):

* `nonempty_completion_algEquiv_formalUV_of_gluing`: **if `|x̃| = 2`, then
  `Â ≅ k[[u, v]]/(uv)`** as `k`-algebras. The local rings `B_{𝔫ᵢ}` of the normalization at the two
  points are discrete valuation rings (`isDiscreteValuationRing_localization`) with residue field
  `k`, so their completions are `k[[t]]`; the jets of `A` are those of its two branches
  (`mem_maximalIdeal_pow_of_branches`, `exists_branches_approx`), and
  `nonempty_completion_algEquiv_formalUV` identifies `Â` with
  `{(f, g) ∈ k[[t]]² : f(0) = g(0)} ≅ k[[u, v]]/(uv)`.
* `exists_isDiscreteValuationRing_of_gluing`: **if `|x̃| = 1`, then `A = B` is a discrete valuation
  ring** (hence regular; over a perfect field, `x` is a smooth point).

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, App. B, l. 4381–4397).

Blueprint: `sm-curves-fields-ordinary-gluing.tex`, `thm:sm-og-local`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

open IsLocalRing
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
open DeJongAlterations.Algebra.CompletionRegularityBasics
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

set_option autoImplicit false

universe u v w

noncomputable section

variable {k : Type u} [Field k] {A : Type v} {B : Type v} {L : Type w} [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra k A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Algebra k B] [IsScalarTower k A B] [CommRing L] [Algebra A L]

/-- A residue field `B ⧸ 𝔫` equal to `k` gives a constant `c` with `b ≡ c mod 𝔫`. -/
theorem exists_sub_mem_of_surjective {n : Ideal B}
    (hres : Function.Surjective (algebraMap k (B ⧸ n))) (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ n := by
  obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk n b)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Ideal.Quotient.mk_algebraMap]

/-- The residue field of `B_𝔫` is `k` if that of `𝔫` is. -/
theorem exists_sub_mem_localization {n : Ideal B} [n.IsMaximal]
    (hres : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ n) (d : Localization.AtPrime n) :
    ∃ c : k, d - algebraMap k (Localization.AtPrime n) c ∈
      maximalIdeal (Localization.AtPrime n) := by
  obtain ⟨b, hb⟩ := exists_algebraMap_sub_mem_pow n 1 d
  obtain ⟨c, hc⟩ := hres b
  refine ⟨c, ?_⟩
  have h1 : algebraMap B (Localization.AtPrime n) (b - algebraMap k B c) ∈
      maximalIdeal (Localization.AtPrime n) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ n _).2 hc
  rw [pow_one] at hb
  have : d - algebraMap k (Localization.AtPrime n) c =
      algebraMap B (Localization.AtPrime n) (b - algebraMap k B c) -
        (algebraMap B (Localization.AtPrime n) b - d) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
    ring
  rw [this]
  exact Ideal.sub_mem _ h1 hb

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- The composite `A → B → B_𝔫` is a local homomorphism. -/
theorem isLocalHom_comp_algebraMap [Algebra.IsIntegral A B] (n : Ideal B) [n.IsMaximal] :
    IsLocalHom ((algebraMap B (Localization.AtPrime n)).comp (algebraMap A B)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : algebraMap A B a ∈ n := by
    rw [← Ideal.mem_comap, comap_eq_maximalIdeal n]
    exact hna
  have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime n) n _).2 h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

/-- **Gluing form with two branches implies completed form** (Temkin, App. B, l. 4381–4387, the
case `n = 2` of `lem:sm-ordinary-completion`, "⇐"). Let `A` be a one-dimensional Noetherian local
`k`-algebra, `B ⊇ A` a finite `A`-algebra which is integrally closed in an `A`-algebra `L ⊇ B` in
which some `s ∈ 𝔪_A` is invertible (the semilocal ring of the normalization), such that `B` has
exactly two maximal ideals, both with residue field `k`, and `A` is the gluing subalgebra of `B`.
Then `Â ≅ k[[u, v]]/(uv)` as `k`-algebras. -/
theorem nonempty_completion_algEquiv_formalUV_of_gluing
    (hAB : Function.Injective (algebraMap A B)) (ι : B →ₐ[A] L) (hι : Function.Injective ι)
    (hint : ∀ y : L, IsIntegral A y → y ∈ ι.range) {s : A} (hs : s ∈ maximalIdeal A)
    (hsL : IsUnit (algebraMap A L s))
    (hres : ∀ m : MaximalSpectrum B, Function.Surjective (algebraMap k (B ⧸ m.asIdeal)))
    (hgl : rangeIn k A B = gluing k B) (hcard : Nat.card (MaximalSpectrum B) = 2) :
    Nonempty (Completion A ≃ₐ[k] FormalUV k) := by
  obtain ⟨m₁, m₂, hne, hcov⟩ := Nat.card_eq_two_iff.1 hcard
  have hm : ∀ m : MaximalSpectrum B, m = m₁ ∨ m = m₂ := fun m => by
    have : m ∈ ({m₁, m₂} : Set (MaximalSpectrum B)) := hcov ▸ Set.mem_univ m
    simpa using this
  set n₁ := m₁.asIdeal
  set n₂ := m₂.asIdeal
  have : n₁.IsMaximal := m₁.isMaximal
  have : n₂.IsMaximal := m₂.isMaximal
  have hne' : n₁ ≠ n₂ := fun h => hne (MaximalSpectrum.ext h)
  have hres₁ : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ n₁ := exists_sub_mem_of_surjective (hres m₁)
  have hres₂ : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ n₂ := exists_sub_mem_of_surjective (hres m₂)
  have hgl' : ∀ b : B, (∃ c : k, b - algebraMap k B c ∈ n₁ ∧ b - algebraMap k B c ∈ n₂) →
      ∃ a : A, algebraMap A B a = b := by
    rintro b ⟨c, h₁, h₂⟩
    have hb : b ∈ gluing k B := ⟨c, fun m => by rcases hm m with rfl | rfl <;> assumption⟩
    rw [← hgl] at hb
    obtain ⟨a, rfl⟩ := hb
    exact ⟨a, rfl⟩
  -- the two branches are discrete valuation rings with residue field `k`
  obtain ⟨_, _⟩ := isDiscreteValuationRing_localization ι hι hint hs hsL n₁
  obtain ⟨_, _⟩ := isDiscreteValuationRing_localization ι hι hint hs hsL n₂
  obtain ⟨e₁⟩ := nonempty_powerSeries_algEquiv_completion (k := k)
    (exists_sub_mem_localization hres₁)
  obtain ⟨e₂⟩ := nonempty_powerSeries_algEquiv_completion (k := k)
    (exists_sub_mem_localization hres₂)
  have := isLocalHom_comp_algebraMap (A := A) n₁
  have := isLocalHom_comp_algebraMap (A := A) n₂
  have hφ : ∀ (n : Ideal B) [n.IsPrime] (c : k), ((algebraMap B (Localization.AtPrime n)).comp
      (algebraMap A B)) (algebraMap k A c) = algebraMap k (Localization.AtPrime n) c := by
    intro n _ c
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact nonempty_completion_algEquiv_formalUV _ _ (hφ n₁) (hφ n₂) e₁ e₂
    (exists_sub_mem_maximalIdeal n₁ hres₁)
    (fun N a h₁ h₂ => mem_maximalIdeal_pow_of_branches n₁ n₂ hAB hne' hgl' N a h₁ h₂)
    (fun N d₁ d₂ c hd₁ hd₂ => exists_branches_approx (A := A) n₁ n₂ hne' hgl' N d₁ d₂ c hd₁ hd₂)

omit [Module.Finite A B] [Algebra k A] [Algebra k B] [IsScalarTower k A B] in
/-- **Gluing form with one branch: `A` is a discrete valuation ring.** Under the hypotheses of
`nonempty_completion_algEquiv_formalUV_of_gluing` with `A = B` (the case `|x̃| = 1` of the gluing
form), `A` is integrally closed in `L`, hence a discrete valuation ring. -/
theorem exists_isDiscreteValuationRing_of_surjective (hAB : Function.Surjective (algebraMap A B))
    (hAB' : Function.Injective (algebraMap A B)) (ι : B →ₐ[A] L) (hι : Function.Injective ι)
    (hint : ∀ y : L, IsIntegral A y → y ∈ ι.range) {s : A} (hs : s ∈ maximalIdeal A)
    (hsL : IsUnit (algebraMap A L s)) :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  have hAL : algebraMap A L = ι.toRingHom.comp (algebraMap A B) := by
    ext a
    exact (ι.commutes a).symm
  refine isDiscreteValuationRing_of_isIntegrallyClosedIn hs (L := L) ?_ hsL fun y hy => ?_
  · rw [hAL]
    exact hι.comp hAB'
  · obtain ⟨b, rfl⟩ := hint y hy
    obtain ⟨a, rfl⟩ := hAB b
    exact ⟨a, by rw [hAL]; rfl⟩

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- In gluing form with a single point `x̃`, `A = B`: every `b ∈ B` is congruent to a constant at
the unique maximal ideal, hence lies in the gluing subalgebra. -/
theorem algebraMap_surjective_of_gluing
    (hres : ∀ m : MaximalSpectrum B, Function.Surjective (algebraMap k (B ⧸ m.asIdeal)))
    (hgl : rangeIn k A B = gluing k B) (hcard : Nat.card (MaximalSpectrum B) = 1) :
    Function.Surjective (algebraMap A B) := by
  obtain ⟨m₀, hm₀⟩ := Nat.card_eq_one_iff_exists.1 hcard
  intro b
  obtain ⟨c, hc⟩ := exists_sub_mem_of_surjective (hres m₀) b
  have hb : b ∈ gluing k B := ⟨c, fun m => by rw [hm₀ m]; exact hc⟩
  rw [← hgl] at hb
  obtain ⟨a, rfl⟩ := hb
  exact ⟨a, rfl⟩

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryGluing
