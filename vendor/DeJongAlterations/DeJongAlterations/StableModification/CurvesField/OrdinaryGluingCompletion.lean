/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletionBranches
import DeJongAlterations.StableModification.Resolution.LocalDVR
import DeJongAlterations.Algebra.CompletionLocalMap
import DeJongAlterations.Algebra.CompletionRegularityAscent

/-!
# The completion of a local ring with two formal branches

Let `A` be a Noetherian local `k`-algebra with residue field `k`, and let `φ_i : A → D_i`
(`i = 1, 2`) be local homomorphisms into Noetherian local `k`-algebras whose completions are power
series rings, `e_i : k[[t]] ≅ D̂_i`. Assume:

* (**the topology of `A` is induced by the branches**) if `φ₁(a) ∈ 𝔪_{D₁}^N` and
  `φ₂(a) ∈ 𝔪_{D₂}^N`, then `a ∈ 𝔪_A^N`;
* (**approximation**) for `d_i ∈ D_i` with the same residue `c ∈ k` and every `N` there is `a ∈ A`
  with `φ_i(a) ≡ d_i mod 𝔪_{D_i}^N`.

Then **`Â ≅ k[[u, v]]/(uv)`** (`nonempty_completion_algEquiv_formalUV`): the induced map
`Θ = (e₁⁻¹ ∘ φ̂₁, e₂⁻¹ ∘ φ̂₂) : Â → k[[t]] × k[[t]]` is injective with image the pairs with equal
constant terms, which is the image of CRV4's branch embedding
`OrdinaryCompletion.branchMap : k[[u, v]]/(uv) → k[[t]] × k[[t]]` (`u ↦ (t, 0)`, `v ↦ (0, t)`).
Injectivity: if `Θ(x) = 0`, a representative `a` of `x mod 𝔪^N` has `φ_i(a) ∈ 𝔪_{D_i}^N`, so
`a ∈ 𝔪^N`. Surjectivity: for a pair `(f, g)` with `f(0) = g(0)`, the approximations `a_N` of
`(e₁ f, e₂ g)` modulo `𝔪^{N+1}` form a Cauchy sequence (first property), whose limit maps to
`(f, g)`.

This is the computation `Ô_{C,x} = Gl(B̂) = {(f, g) ∈ k[[t]]² : f(0) = g(0)} ≅ k[[u, v]]/(uv)` of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, App. B, l. 4381–4387), for
`n = 2`, with `D_i` the local rings of the normalization at the two points over `x`
(`OrdinaryGluing.mem_maximalIdeal_pow_of_branches`, `OrdinaryGluing.exists_branches_approx`).

The completions `D̂_i ≅ k[[t]]` come from `nonempty_powerSeries_algEquiv_completion`: the
completion of a discrete valuation ring with residue field `k` is `k[[t]]` (Claude's
`Resolution.nonempty_powerSeries_algEquiv_of_ringKrullDim_eq_one`).

Blueprint: `sm-curves-fields-ordinary-gluing.tex`, `lem:sm-og-dvr-completion`,
`prop:sm-og-completion`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

open IsLocalRing AdicCompletion
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
open DeJongAlterations.Algebra.CompletionRegularityBasics
open DeJongAlterations.Algebra.CompletionLocalMap
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

set_option autoImplicit false

universe u v w

noncomputable section

section PowerSeries

/-- **The completion of a discrete valuation ring with residue field `k` is `k[[t]]`.** -/
theorem nonempty_powerSeries_algEquiv_completion {k : Type u} [Field k] {D : Type v} [CommRing D]
    [IsDomain D] [IsDiscreteValuationRing D] [Algebra k D]
    (hres : ∀ d : D, ∃ c : k, d - algebraMap k D c ∈ maximalIdeal D) :
    Nonempty (PowerSeries k ≃ₐ[k] Completion D) := by
  have : IsRegularLocalRing (Completion D) :=
    DeJongAlterations.Algebra.CompletionRegularityAscent.isRegularLocalRing_completion D
  have hdim : ringKrullDim (Completion D) = 1 := by
    rw [← (isRegularLocalRing_iff (Completion D)).1 inferInstance,
      AdicCompletion.spanFinrank_maximalIdeal_eq, (isRegularLocalRing_iff D).1 inferInstance,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  refine Resolution.nonempty_powerSeries_algEquiv_of_ringKrullDim_eq_one hdim fun y => ?_
  obtain ⟨z, rfl⟩ := (AdicCompletion.residueField_map_bijective D).2 y
  obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨c, hc⟩ := hres d
  refine ⟨c, ?_⟩
  have h1 : residue D d = residue D (algebraMap k D c) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hc
  rw [h1, IsLocalRing.ResidueField.map_residue, RingHom.comp_apply, AdicCompletion.algebraMap_apply]
  rfl

end PowerSeries

section Assembly

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A] [Algebra k A]
  {D₁ D₂ : Type w} [CommRing D₁] [IsLocalRing D₁] [IsNoetherianRing D₁]
  [Algebra k D₁] [CommRing D₂] [IsLocalRing D₂] [IsNoetherianRing D₂] [Algebra k D₂]

/-- If `c` is the constant term of `f`, then `e(f) - c` lies in the maximal ideal of `D̂`. -/
theorem sub_algebraMap_constantCoeff_mem {D : Type w} [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [Algebra k D] (e : PowerSeries k ≃ₐ[k] Completion D) (f : PowerSeries k) :
    e f - algebraMap k (Completion D) (PowerSeries.constantCoeff f) ∈
      maximalIdeal (Completion D) := by
  have hf : f - PowerSeries.C (PowerSeries.constantCoeff f) ∈ maximalIdeal (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp
  have : e (f - PowerSeries.C (PowerSeries.constantCoeff f)) ∈ maximalIdeal (Completion D) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff e]
    exact hf
  rwa [map_sub, ← PowerSeries.algebraMap_eq, AlgEquiv.commutes] at this

/-- `y ∈ D̂` lies in the maximal ideal iff its image in `D ⧸ 𝔪` is zero. -/
theorem mem_maximalIdeal_iff_evalₐ_one {D : Type w} [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] (y : Completion D) :
    y ∈ maximalIdeal (Completion D) ↔ evalₐ (maximalIdeal D) 1 y = 0 := by
  rw [AdicCompletion.mem_maximalIdeal_iff_eval_one_eq_zero]
  have h : (maximalIdeal D ^ 1 • ⊤ : Ideal D) = maximalIdeal D ^ 1 := by ext x; simp
  change _ ↔ Ideal.quotientEquivAlgOfEq D h (y.val 1) = 0
  rw [EmbeddingLike.map_eq_zero_iff]

variable (φ₁ : A →+* D₁) (φ₂ : A →+* D₂) [IsLocalHom φ₁] [IsLocalHom φ₂]
  (hφ₁ : ∀ c : k, φ₁ (algebraMap k A c) = algebraMap k D₁ c)
  (hφ₂ : ∀ c : k, φ₂ (algebraMap k A c) = algebraMap k D₂ c)

/-- The completed branch map `Â → D̂` of a local homomorphism `φ : A → D`, as a `k`-algebra
map. -/
def completionAlgHom {D : Type w} [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra k D]
    (φ : A →+* D) [IsLocalHom φ] (hφ : ∀ c : k, φ (algebraMap k A c) = algebraMap k D c) :
    Completion A →ₐ[k] Completion D :=
  { completionMap φ with
    commutes' := fun c => by
      change completionMap φ (algebraMap k (Completion A) c) = _
      rw [AdicCompletion.algebraMap_apply, completionMap_of, hφ,
        ← AdicCompletion.algebraMap_apply] }

theorem completionAlgHom_apply {D : Type w} [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra k D] (φ : A →+* D) [IsLocalHom φ]
    (hφ : ∀ c : k, φ (algebraMap k A c) = algebraMap k D c) (x : Completion A) :
    completionAlgHom φ hφ x = completionMap φ x := rfl

/-- `evalₐ N` of the completed branch map is `φ` applied to a representative. -/
theorem evalₐ_completionMap_mk {D : Type w} [CommRing D] [IsLocalRing D] (φ : A →+* D)
    [IsLocalHom φ] (N : ℕ) (x : Completion A) (a : A)
    (ha : Ideal.Quotient.mk _ a = evalₐ (maximalIdeal A) N x) :
    evalₐ (maximalIdeal D) N (completionMap φ x) = Ideal.Quotient.mk _ (φ a) := by
  rw [evalₐ_completionMap, ← ha, Ideal.quotientMap_mk]

include hφ₁ hφ₂ in
/-- **The completion of a local ring with two formal branches is `k[[u, v]]/(uv)`.** -/
theorem nonempty_completion_algEquiv_formalUV
    (e₁ : PowerSeries k ≃ₐ[k] Completion D₁) (e₂ : PowerSeries k ≃ₐ[k] Completion D₂)
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A)
    (hinj : ∀ (N : ℕ) (a : A), φ₁ a ∈ maximalIdeal D₁ ^ N → φ₂ a ∈ maximalIdeal D₂ ^ N →
      a ∈ maximalIdeal A ^ N)
    (hsurj : ∀ (N : ℕ) (d₁ : D₁) (d₂ : D₂) (c : k), d₁ - algebraMap k D₁ c ∈ maximalIdeal D₁ →
      d₂ - algebraMap k D₂ c ∈ maximalIdeal D₂ →
      ∃ a : A, φ₁ a - d₁ ∈ maximalIdeal D₁ ^ N ∧ φ₂ a - d₂ ∈ maximalIdeal D₂ ^ N) :
    Nonempty (Completion A ≃ₐ[k] FormalUV k) := by
  let Θ : Completion A →ₐ[k] PowerSeries k × PowerSeries k :=
    (e₁.symm.toAlgHom.comp (completionAlgHom φ₁ hφ₁)).prod
      (e₂.symm.toAlgHom.comp (completionAlgHom φ₂ hφ₂))
  have hΘ : ∀ x, Θ x = (e₁.symm (completionMap φ₁ x), e₂.symm (completionMap φ₂ x)) := fun _ => rfl
  -- the residue of a point of `D̂` at its maximal ideal, through a representative
  have hconst : ∀ {D : Type w} [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra k D]
      (φ : A →+* D) [IsLocalHom φ], (∀ c : k, φ (algebraMap k A c) = algebraMap k D c) →
      ∀ (e : PowerSeries k ≃ₐ[k] Completion D) (x : Completion A) (a : A) (c : k),
      Ideal.Quotient.mk _ a = evalₐ (maximalIdeal A) 1 x → a - algebraMap k A c ∈ maximalIdeal A →
      PowerSeries.constantCoeff (e.symm (completionMap φ x)) = c := by
    intro D _ _ _ _ φ _ hφ e x a c ha hac
    set c' := PowerSeries.constantCoeff (e.symm (completionMap φ x))
    have h1 := sub_algebraMap_constantCoeff_mem e (e.symm (completionMap φ x))
    rw [AlgEquiv.apply_symm_apply, mem_maximalIdeal_iff_evalₐ_one, map_sub,
      evalₐ_completionMap_mk φ 1 x a ha, AdicCompletion.algebraMap_apply, evalₐ_of, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, pow_one] at h1
    have h2 : φ (a - algebraMap k A c) ∈ maximalIdeal D := map_nonunit φ _ hac
    rw [map_sub, hφ] at h2
    have h3 : algebraMap k D (c - c') ∈ maximalIdeal D := by
      have : algebraMap k D (c - c') = (φ a - algebraMap k D c') - (φ a - algebraMap k D c) := by
        rw [map_sub]
        ring
      rw [this]
      exact Ideal.sub_mem _ h1 h2
    by_contra hne
    have hu : IsUnit (algebraMap k D (c - c')) :=
      (isUnit_iff_ne_zero.2 (sub_ne_zero.2 (Ne.symm hne))).map _
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 hu
  -- injectivity
  have hinjΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hΘ, Prod.mk_eq_zero] at hx
    have hx₁ : completionMap φ₁ x = 0 := (map_eq_zero_iff _ e₁.symm.injective).1 hx.1
    have hx₂ : completionMap φ₂ x = 0 := (map_eq_zero_iff _ e₂.symm.injective).1 hx.2
    refine ext_evalₐ fun N => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) N x)
    have h₁ := evalₐ_completionMap_mk φ₁ N x a ha
    have h₂ := evalₐ_completionMap_mk φ₂ N x a ha
    rw [hx₁, _root_.map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h₁
    rw [hx₂, _root_.map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h₂
    rw [_root_.map_zero, ← ha, Ideal.Quotient.eq_zero_iff_mem]
    exact hinj N a h₁ h₂
  -- the image
  have hrange : Θ.range = (branchMap k).range := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) 1 x)
      obtain ⟨c, hc⟩ := hres a
      obtain ⟨y, hy⟩ := exists_branchMap_eq (Θ x) (by
        rw [hΘ]
        exact (hconst φ₁ hφ₁ e₁ x a c ha hc).trans (hconst φ₂ hφ₂ e₂ x a c ha hc).symm)
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      set c := PowerSeries.constantCoeff (branchMap k y).1
      have hc₂ : PowerSeries.constantCoeff (branchMap k y).2 = c :=
        (constantCoeff_branchMap_fst_eq_snd y).symm
      set x₁ := e₁ (branchMap k y).1
      set x₂ := e₂ (branchMap k y).2
      have hx₁ := sub_algebraMap_constantCoeff_mem e₁ (branchMap k y).1
      have hx₂ := sub_algebraMap_constantCoeff_mem e₂ (branchMap k y).2
      rw [hc₂] at hx₂
      -- representatives of `x_i` at every level
      choose d₁ hd₁ using fun N => Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal D₁) N x₁)
      choose d₂ hd₂ using fun N => Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal D₂) N x₂)
      -- compatibility of the representatives
      have hcompat : ∀ {D : Type w} [CommRing D] [IsLocalRing D] (z : Completion D)
          (d : ℕ → D), (∀ N, Ideal.Quotient.mk (maximalIdeal D ^ N) (d N) = evalₐ _ N z) →
          ∀ {M N : ℕ}, M ≤ N → d N - d M ∈ maximalIdeal D ^ M := by
        intro D _ _ z d hd M N hMN
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, hd M,
          ← factorPow_evalₐ (maximalIdeal D) hMN z, ← hd N]
        rfl
      have hres₁ : ∀ N, d₁ (N + 1) - algebraMap k D₁ c ∈ maximalIdeal D₁ := by
        intro N
        have h := hcompat x₁ d₁ hd₁ (Nat.le_add_left 1 N)
        rw [mem_maximalIdeal_iff_evalₐ_one, map_sub, ← hd₁ 1, AdicCompletion.algebraMap_apply,
          evalₐ_of, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, pow_one] at hx₁
        rw [pow_one] at h
        have : d₁ (N + 1) - algebraMap k D₁ c =
            (d₁ (N + 1) - d₁ 1) + (d₁ 1 - algebraMap k D₁ c) := by
          ring
        rw [this]
        exact Ideal.add_mem _ h hx₁
      have hres₂ : ∀ N, d₂ (N + 1) - algebraMap k D₂ c ∈ maximalIdeal D₂ := by
        intro N
        have h := hcompat x₂ d₂ hd₂ (Nat.le_add_left 1 N)
        rw [mem_maximalIdeal_iff_evalₐ_one, map_sub, ← hd₂ 1, AdicCompletion.algebraMap_apply,
          evalₐ_of, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, pow_one] at hx₂
        rw [pow_one] at h
        have : d₂ (N + 1) - algebraMap k D₂ c =
            (d₂ (N + 1) - d₂ 1) + (d₂ 1 - algebraMap k D₂ c) := by
          ring
        rw [this]
        exact Ideal.add_mem _ h hx₂
      -- approximations in `A`
      choose a ha₁ ha₂ using fun N => hsurj (N + 1) (d₁ (N + 1)) (d₂ (N + 1)) c (hres₁ N) (hres₂ N)
      have hstep : ∀ {D : Type w} [CommRing D] [IsLocalRing D] (φ : A →+* D) (d : ℕ → D),
          (∀ {M N : ℕ}, M ≤ N → d N - d M ∈ maximalIdeal D ^ M) →
          (∀ N, φ (a N) - d (N + 1) ∈ maximalIdeal D ^ (N + 1)) →
          ∀ N, φ (a N - a (N + 1)) ∈ maximalIdeal D ^ N := by
        intro D _ _ φ d hd hφa N
        have : φ (a N - a (N + 1)) = (φ (a N) - d (N + 1)) - (φ (a (N + 1)) - d (N + 1 + 1)) -
            (d (N + 1 + 1) - d (N + 1)) := by
          rw [map_sub]
          ring
        rw [this]
        refine Ideal.sub_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
        · exact Ideal.pow_le_pow_right (Nat.le_succ N) (hφa N)
        · exact Ideal.pow_le_pow_right (by omega) (hφa (N + 1))
        · exact Ideal.pow_le_pow_right (Nat.le_succ N) (hd (Nat.le_succ (N + 1)))
      let seq : AdicCauchySequence (maximalIdeal A) A :=
        AdicCauchySequence.mk (maximalIdeal A) A a fun N => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
          exact hinj N _ (hstep φ₁ d₁ (hcompat x₁ d₁ hd₁) ha₁ N)
            (hstep φ₂ d₂ (hcompat x₂ d₂ hd₂) ha₂ N)
      refine ⟨AdicCompletion.mk (maximalIdeal A) A seq, ?_⟩
      change Θ (AdicCompletion.mk (maximalIdeal A) A seq) = branchMap k y
      have hlim : ∀ {D : Type w} [CommRing D] [IsLocalRing D] (φ : A →+* D) [IsLocalHom φ]
          (z : Completion D) (d : ℕ → D),
          (∀ N, Ideal.Quotient.mk (maximalIdeal D ^ N) (d N) = evalₐ _ N z) →
          (∀ N, φ (a N) - d (N + 1) ∈ maximalIdeal D ^ (N + 1)) →
          completionMap φ (AdicCompletion.mk (maximalIdeal A) A seq) = z := by
        intro D _ _ φ _ z d hd hφa
        refine ext_evalₐ fun N => ?_
        rw [evalₐ_completionMap_mk φ N _ (a N) (by rw [evalₐ_mk]; rfl), ← factorPow_evalₐ
          (maximalIdeal D) (Nat.le_succ N) z, ← hd (N + 1)]
        change _ = Ideal.Quotient.mk _ (d (N + 1))
        rw [Ideal.Quotient.eq]
        exact Ideal.pow_le_pow_right (Nat.le_succ N) (hφa N)
      rw [hΘ, hlim φ₁ x₁ d₁ hd₁ ha₁, hlim φ₂ x₂ d₂ hd₂ ha₂, AlgEquiv.symm_apply_apply,
        AlgEquiv.symm_apply_apply]
  exact ⟨(AlgEquiv.ofInjective Θ hinjΘ).trans ((Subalgebra.equivOfEq _ _ hrange).trans
    (AlgEquiv.ofInjective (branchMap k) branchMap_injective).symm)⟩

end Assembly

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryGluing
