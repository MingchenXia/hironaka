/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Algebra.Exact.Basic

/-!
# The algebra of twisted two-term Čech complexes

This file is the algebraic core of the weak Riemann–Roch theorem, Serre vanishing and global
generation for a divisor on a curve covered by two affine opens (blueprint
`sm-curves-fields-cohomology.tex`, `lem:sm-twist-snake`, `thm:sm-weak-rr`,
`lem:sm-serre-vanishing-curve`, `lem:sm-global-generation`; M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), Prop. 4.4.6, lines 3204–3225 of
`references/temkin10-stable-modification/source/semi-stable.tex`).

## Setting

Let `X = U ∪ V` with `U`, `V`, `U ∩ V` affine, `F` quasi-coherent and `D = V(f) ⊆ V` with
`f ∈ Γ(V, 𝒪)` a unit on `U ∩ V`. Write `MU = Γ(U, F)`, `MV = Γ(V, F)`, `MW = Γ(U ∩ V, F)`,
`ρU`, `ρV` for the restrictions, `σ` for multiplication by `f` on `MW` (bijective) and `φ` for
multiplication by `f` on `MV`, so `ρV ∘ φ = σ ∘ ρV`. The twist of `F` by the transition function
`g` (a unit on `U ∩ V`, acting as `γ` on `MW`) has the two-term Čech complex
`MU × MV → MW`, `(a, b) ↦ ρV b - γ (ρU a)` (`twistDiff`); its kernel and cokernel are `H⁰` and `H¹`
of the twisted sheaf. Replacing `γ` by `σ ∘ γ` twists by `D` once more (`F(mD) ↦ F((m+1)D)`).

## Main results

* The snake sequence of `F(mD) → F((m+1)D)` (`stepH0`, `stepQ`, `stepδ`, `stepH1`): for injective
  `φ`, `0 → H⁰(γ) → H⁰(σγ) → MV ⧸ f MV → H¹(γ) → H¹(σγ) → 0` is exact
  (`stepH0_injective`, `exact_stepH0_stepQ`, `exact_stepQ_stepδ`, `exact_stepδ_stepH1`,
  `stepH1_surjective`).
* `euler_step`, `euler_twist`: over a field, `χ(σγ) = χ(γ) + dim (MV ⧸ f MV)`, hence
  `χ(F(mD)) = χ(F) + m · dim (MV ⧸ f MV)` for all `m ∈ ℤ` (**weak Riemann–Roch**).
* `exists_forall_subsingleton_H1`: if `MW = ⋃ₘ σ⁻ᵐ ρV(MV)` (the complement of `D` is `U`) and
  `H¹(γ₀)` is finitely generated, then `H¹(γₘ) = 0` for `m ≫ 0` (**Serre vanishing**).
* `stepQ_surjective_of_subsingleton`: if `H¹(γ) = 0`, every element of `MV ⧸ f MV` is the
  `V`-component of a global section of the next twist (**global generation along `D`**);
  `exists_forall_finrank_H1_eq`, `stepQ_surjective_of_finrank_eq`: over a field this holds for
  `m ≫ 0` with no condition on the complement of `D`.
* `exists_mem_H0_of_limit`: every section over `U` extends to a global section of `F(mD)` for
  `m ≫ 0` (**global generation on `U`**).
-/

open LinearMap Submodule Module

namespace DeJongAlterations.StableModification.CurvesField

universe u₁ u₂ u₃ u₄

variable {R : Type u₁} [CommRing R] {MU : Type u₂} {MV : Type u₃} {MW : Type u₄}
  [AddCommGroup MU] [Module R MU] [AddCommGroup MV] [Module R MV] [AddCommGroup MW]
  [Module R MW] (ρU : MU →ₗ[R] MW) (ρV : MV →ₗ[R] MW)

/-- The differential `(a, b) ↦ ρV b - γ (ρU a)` of the two-term Čech complex of the twist by the
transition function acting as `γ` on `MW`. -/
def twistDiff (γ : MW →ₗ[R] MW) : MU × MV →ₗ[R] MW :=
  ρV ∘ₗ LinearMap.snd R MU MV - (γ ∘ₗ ρU) ∘ₗ LinearMap.fst R MU MV

@[simp]
lemma twistDiff_apply (γ : MW →ₗ[R] MW) (p : MU × MV) :
    twistDiff ρU ρV γ p = ρV p.2 - γ (ρU p.1) :=
  rfl

/-- `H⁰` of the twisted two-term complex: the kernel of `twistDiff`. -/
abbrev H0 (γ : MW →ₗ[R] MW) : Submodule R (MU × MV) := LinearMap.ker (twistDiff ρU ρV γ)

/-- `H¹` of the twisted two-term complex: the cokernel of `twistDiff`. -/
abbrev H1 (γ : MW →ₗ[R] MW) : Type u₄ := MW ⧸ LinearMap.range (twistDiff ρU ρV γ)

section Congr

/-! ### Transport of the twisted complexes along isomorphisms -/

variable {MU' MV' MW' : Type*} [AddCommGroup MU'] [Module R MU'] [AddCommGroup MV'] [Module R MV']
  [AddCommGroup MW'] [Module R MW'] {ρU ρV} {ρU' : MU' →ₗ[R] MW'} {ρV' : MV' →ₗ[R] MW'}
  (eU : MU ≃ₗ[R] MU') (eV : MV ≃ₗ[R] MV') (eW : MW ≃ₗ[R] MW')
  (hU : ∀ a, eW (ρU a) = ρU' (eU a)) (hV : ∀ b, eW (ρV b) = ρV' (eV b))
  {γ : MW →ₗ[R] MW} {γ' : MW' →ₗ[R] MW'} (hγ : ∀ w, eW (γ w) = γ' (eW w))

include hU hV hγ

lemma twistDiff_congr (p : MU × MV) :
    eW (twistDiff ρU ρV γ p) = twistDiff ρU' ρV' γ' (eU.prodCongr eV p) := by
  simp only [twistDiff_apply, map_sub, hV, hγ, hU, LinearEquiv.prodCongr_apply]

/-- Isomorphic data give isomorphic `H⁰`. -/
def H0Congr : H0 ρU ρV γ ≃ₗ[R] H0 ρU' ρV' γ' :=
  (eU.prodCongr eV).ofSubmodules _ _ (by
    ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [LinearEquiv.coe_coe, ← twistDiff_congr eU eV eW hU hV hγ, hp, map_zero]
    · intro hq
      refine ⟨(eU.prodCongr eV).symm q, ?_, by simp⟩
      apply eW.injective
      rw [twistDiff_congr eU eV eW hU hV hγ, LinearEquiv.apply_symm_apply, hq, map_zero])

/-- Isomorphic data give isomorphic `H¹`. -/
def H1Congr : H1 ρU ρV γ ≃ₗ[R] H1 ρU' ρV' γ' :=
  Submodule.Quotient.equiv _ _ eW (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨_, (twistDiff_congr eU eV eW hU hV hγ p).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨_, ⟨(eU.prodCongr eV).symm q, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, twistDiff_congr eU eV eW hU hV hγ, LinearEquiv.apply_symm_apply])

end Congr

section Step

variable (σ : MW ≃ₗ[R] MW) (φ : MV →ₗ[R] MV)
  (hφ : ρV ∘ₗ φ = σ.toLinearMap ∘ₗ ρV) (γ : MW →ₗ[R] MW)

include hφ

lemma ρV_φ (b : MV) : ρV (φ b) = σ (ρV b) := LinearMap.congr_fun hφ b

/-- The inclusion `H⁰(F(mD)) → H⁰(F((m+1)D))`, `(a, b) ↦ (a, f b)`. -/
def stepH0 : H0 ρU ρV γ →ₗ[R] H0 ρU ρV (σ.toLinearMap ∘ₗ γ) :=
  ((LinearMap.id.prodMap φ).comp (H0 ρU ρV γ).subtype).codRestrict _ (by
    intro p
    have hp := p.property
    simp only [LinearMap.mem_ker, twistDiff_apply] at hp ⊢
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.prodMap_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe]
    rw [ρV_φ ρV σ φ hφ, ← map_sub, hp, map_zero])

@[simp]
lemma stepH0_apply (p : H0 ρU ρV γ) :
    (stepH0 ρU ρV σ φ hφ γ p : MU × MV) = ((p : MU × MV).1, φ (p : MU × MV).2) :=
  rfl

omit hφ in
/-- The `V`-component modulo `f`: `H⁰(F((m+1)D)) → MV ⧸ f MV`. -/
def stepQ : H0 ρU ρV (σ.toLinearMap ∘ₗ γ) →ₗ[R] MV ⧸ LinearMap.range φ :=
  (LinearMap.range φ).mkQ ∘ₗ LinearMap.snd R MU MV ∘ₗ (H0 ρU ρV _).subtype

omit hφ in
@[simp]
lemma stepQ_apply (p : H0 ρU ρV (σ.toLinearMap ∘ₗ γ)) :
    stepQ ρU ρV σ φ γ p = (LinearMap.range φ).mkQ (p : MU × MV).2 :=
  rfl

/-- The connecting map `MV ⧸ f MV → H¹(F(mD))`, `[b] ↦ [σ⁻¹ ρV b]`. -/
def stepδ : MV ⧸ LinearMap.range φ →ₗ[R] H1 ρU ρV γ :=
  (LinearMap.range φ).liftQ ((LinearMap.range (twistDiff ρU ρV γ)).mkQ ∘ₗ
    σ.symm.toLinearMap ∘ₗ ρV) (by
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ρV_φ ρV σ φ hφ,
      LinearEquiv.symm_apply_apply]
    exact ⟨(0, b), by simp⟩)

@[simp]
lemma stepδ_mk (b : MV) :
    stepδ ρU ρV σ φ hφ γ (Submodule.Quotient.mk b) = Submodule.Quotient.mk (σ.symm (ρV b)) :=
  rfl

/-- The map `H¹(F(mD)) → H¹(F((m+1)D))`, `[w] ↦ [σ w]`. -/
def stepH1 : H1 ρU ρV γ →ₗ[R] H1 ρU ρV (σ.toLinearMap ∘ₗ γ) :=
  (LinearMap.range (twistDiff ρU ρV γ)).mapQ _ σ.toLinearMap (by
    rintro _ ⟨p, rfl⟩
    refine ⟨(p.1, φ p.2), ?_⟩
    simp only [twistDiff_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ρV_φ ρV σ φ hφ, map_sub])

@[simp]
lemma stepH1_mk (w : MW) :
    stepH1 ρU ρV σ φ hφ γ (Submodule.Quotient.mk w) = Submodule.Quotient.mk (σ w) :=
  rfl

/-- `F(mD) → F((m+1)D)` is injective on `H⁰` when `f` is a nonzerodivisor on `MV`. -/
lemma stepH0_injective (hφinj : Function.Injective φ) :
    Function.Injective (stepH0 ρU ρV σ φ hφ γ) := by
  intro p q h
  have h' := congrArg Subtype.val h
  simp only [stepH0_apply, Prod.mk.injEq] at h'
  exact Subtype.ext (Prod.ext h'.1 (hφinj h'.2))

lemma exact_stepH0_stepQ :
    Function.Exact (stepH0 ρU ρV σ φ hφ γ) (stepQ ρU ρV σ φ γ) := by
  intro p
  constructor
  · intro hp
    simp only [stepQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      LinearMap.mem_range] at hp
    obtain ⟨b, hb⟩ := hp
    have hmem : ((p : MU × MV).1, b) ∈ H0 ρU ρV γ := by
      have hp' := p.property
      simp only [LinearMap.mem_ker, twistDiff_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe] at hp' ⊢
      apply σ.injective
      rw [map_sub, map_zero, ← ρV_φ ρV σ φ hφ, hb, hp']
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    simp only [stepH0_apply, hb]
  · rintro ⟨q, rfl⟩
    simp

lemma exact_stepQ_stepδ : Function.Exact (stepQ ρU ρV σ φ γ) (stepδ ρU ρV σ φ hφ γ) := by
  intro x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro hx
    rw [stepδ_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨⟨a, b'⟩, hab⟩ := hx
    simp only [twistDiff_apply] at hab
    -- `σ⁻¹ ρV b = ρV b' - γ ρU a`, so `(-a, b - φ b')` is a section of the next twist
    have hmem : (-a, b - φ b') ∈ H0 ρU ρV (σ.toLinearMap ∘ₗ γ) := by
      simp only [LinearMap.mem_ker, twistDiff_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        map_sub, map_neg, ρV_φ ρV σ φ hφ]
      have : ρV b = σ (ρV b') - σ (γ (ρU a)) := by
        rw [← map_sub, hab, LinearEquiv.apply_symm_apply]
      rw [this]
      abel
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [stepQ_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    exact ⟨-b', by simp⟩
  · rintro ⟨p, hp⟩
    rw [← hp, stepQ_apply, Submodule.mkQ_apply, stepδ_mk, Submodule.Quotient.mk_eq_zero]
    have hp' := p.property
    simp only [LinearMap.mem_ker, twistDiff_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      sub_eq_zero] at hp'
    refine ⟨(-(p : MU × MV).1, 0), ?_⟩
    simp only [twistDiff_apply, map_zero, map_neg, zero_sub, neg_neg, hp',
      LinearEquiv.symm_apply_apply]

lemma exact_stepδ_stepH1 : Function.Exact (stepδ ρU ρV σ φ hφ γ) (stepH1 ρU ρV σ φ hφ γ) := by
  intro x
  constructor
  · intro hx
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [stepH1_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨⟨a, b⟩, hab⟩ := hx
    simp only [twistDiff_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hab
    refine ⟨Submodule.Quotient.mk b, ?_⟩
    rw [stepδ_mk, Submodule.Quotient.eq]
    refine ⟨(-a, 0), ?_⟩
    apply σ.injective
    simp only [twistDiff_apply, map_zero, zero_sub, map_neg, neg_neg, map_sub,
      LinearEquiv.apply_symm_apply]
    rw [← hab]
    abel
  · rintro ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [stepδ_mk, stepH1_mk, LinearEquiv.apply_symm_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨(0, b), by simp⟩

lemma stepH1_surjective : Function.Surjective (stepH1 ρU ρV σ φ hφ γ) := by
  intro y
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk (σ.symm w), by rw [stepH1_mk, LinearEquiv.apply_symm_apply]⟩

/-- If `H¹(F(mD)) = 0`, every class in `MV ⧸ f MV` is the `V`-component of a global section of
`F((m+1)D)` (**global generation along `D`**). -/
lemma stepQ_surjective_of_subsingleton [Subsingleton (H1 ρU ρV γ)] :
    Function.Surjective (stepQ ρU ρV σ φ γ) := fun x =>
  (exact_stepQ_stepδ ρU ρV σ φ hφ γ x).mp (Subsingleton.elim _ _)

end Step

section Field

variable {K : Type u₁} [Field K] {MU : Type u₂} {MV : Type u₃} {MW : Type u₄}
  [AddCommGroup MU] [Module K MU] [AddCommGroup MV] [Module K MV] [AddCommGroup MW]
  [Module K MW] (ρU : MU →ₗ[K] MW) (ρV : MV →ₗ[K] MW) (σ : MW ≃ₗ[K] MW) (φ : MV →ₗ[K] MV)
  (hφ : ρV ∘ₗ φ = σ.toLinearMap ∘ₗ ρV) (γ : MW →ₗ[K] MW)

/-- The Euler characteristic `dim H⁰ - dim H¹` of the twisted two-term complex. -/
noncomputable def euler (γ : MW →ₗ[K] MW) : ℤ :=
  (finrank K (H0 ρU ρV γ) : ℤ) - finrank K (H1 ρU ρV γ)

include hφ

lemma finiteDimensional_H0_step [FiniteDimensional K (H0 ρU ρV γ)]
    [FiniteDimensional K (MV ⧸ LinearMap.range φ)] :
    FiniteDimensional K (H0 ρU ρV (σ.toLinearMap ∘ₗ γ)) := by
  have hex : Function.Exact (stepH0 ρU ρV σ φ hφ γ) (stepQ ρU ρV σ φ γ).rangeRestrict := by
    intro p
    rw [← exact_stepH0_stepQ ρU ρV σ φ hφ γ p]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact Module.Finite.of_exact hex (LinearMap.surjective_rangeRestrict _)

lemma finiteDimensional_H1_step [FiniteDimensional K (H1 ρU ρV γ)] :
    FiniteDimensional K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ)) :=
  Module.Finite.of_surjective _ (stepH1_surjective ρU ρV σ φ hφ γ)

lemma finiteDimensional_H0_of_step (hφinj : Function.Injective φ)
    [FiniteDimensional K (H0 ρU ρV (σ.toLinearMap ∘ₗ γ))] :
    FiniteDimensional K (H0 ρU ρV γ) :=
  Module.Finite.of_injective _ (stepH0_injective ρU ρV σ φ hφ γ hφinj)

lemma finiteDimensional_H1_of_step [FiniteDimensional K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ))]
    [FiniteDimensional K (MV ⧸ LinearMap.range φ)] :
    FiniteDimensional K (H1 ρU ρV γ) :=
  Module.Finite.of_exact (exact_stepδ_stepH1 ρU ρV σ φ hφ γ) (stepH1_surjective ρU ρV σ φ hφ γ)

/-- The dimension count of the snake sequence: `dim H⁰(σγ) + dim H¹(γ) + (rank of the connecting
map) ... `, in the form `dim H¹(γ) = dim H¹(σγ) + rank stepδ` and
`dim H⁰(σγ) + rank stepδ = dim H⁰(γ) + dim (MV ⧸ f MV)`. -/
lemma finrank_step (hφinj : Function.Injective φ) [FiniteDimensional K (H0 ρU ρV γ)]
    [FiniteDimensional K (H1 ρU ρV γ)] [FiniteDimensional K (MV ⧸ LinearMap.range φ)] :
    finrank K (H1 ρU ρV γ) =
        finrank K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ)) +
          finrank K (LinearMap.range (stepδ ρU ρV σ φ hφ γ)) ∧
      finrank K (H0 ρU ρV (σ.toLinearMap ∘ₗ γ)) +
          finrank K (LinearMap.range (stepδ ρU ρV σ φ hφ γ)) =
        finrank K (H0 ρU ρV γ) + finrank K (MV ⧸ LinearMap.range φ) := by
  have := finiteDimensional_H0_step ρU ρV σ φ hφ γ
  have e1 := LinearMap.finrank_range_add_finrank_ker (stepQ ρU ρV σ φ γ)
  have e2 := LinearMap.finrank_range_add_finrank_ker (stepδ ρU ρV σ φ hφ γ)
  have e3 := LinearMap.finrank_range_add_finrank_ker (stepH1 ρU ρV σ φ hφ γ)
  rw [LinearMap.exact_iff.mp (exact_stepH0_stepQ ρU ρV σ φ hφ γ),
    LinearMap.finrank_range_of_inj (stepH0_injective ρU ρV σ φ hφ γ hφinj)] at e1
  rw [LinearMap.exact_iff.mp (exact_stepQ_stepδ ρU ρV σ φ hφ γ)] at e2
  rw [LinearMap.exact_iff.mp (exact_stepδ_stepH1 ρU ρV σ φ hφ γ),
    LinearMap.range_eq_top.mpr (stepH1_surjective ρU ρV σ φ hφ γ), finrank_top] at e3
  constructor <;> omega

/-- **Euler characteristic of one more twist**: `χ(F((m+1)D)) = χ(F(mD)) + dim (MV ⧸ f MV)`. -/
theorem euler_step (hφinj : Function.Injective φ) [FiniteDimensional K (H0 ρU ρV γ)]
    [FiniteDimensional K (H1 ρU ρV γ)] [FiniteDimensional K (MV ⧸ LinearMap.range φ)] :
    euler ρU ρV (σ.toLinearMap ∘ₗ γ) = euler ρU ρV γ + finrank K (MV ⧸ LinearMap.range φ) := by
  obtain ⟨h1, h2⟩ := finrank_step ρU ρV σ φ hφ γ hφinj
  unfold euler
  omega

/-- `dim H¹` does not increase under one more twist. -/
theorem finrank_H1_step_le [FiniteDimensional K (H1 ρU ρV γ)] :
    finrank K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ)) ≤ finrank K (H1 ρU ρV γ) := by
  have h := LinearMap.finrank_range_le (stepH1 ρU ρV σ φ hφ γ)
  rwa [LinearMap.range_eq_top.mpr (stepH1_surjective ρU ρV σ φ hφ γ), finrank_top] at h

/-- If `dim H¹` does not drop under one more twist, every class in `MV ⧸ f MV` is the
`V`-component of a global section of the next twist (global generation along `D`, over a field,
with no condition on the complement of `D`). -/
theorem stepQ_surjective_of_finrank_eq (hφinj : Function.Injective φ)
    [FiniteDimensional K (H0 ρU ρV γ)] [FiniteDimensional K (H1 ρU ρV γ)]
    [FiniteDimensional K (MV ⧸ LinearMap.range φ)]
    (h : finrank K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ)) = finrank K (H1 ρU ρV γ)) :
    Function.Surjective (stepQ ρU ρV σ φ γ) := by
  obtain ⟨h1, -⟩ := finrank_step ρU ρV σ φ hφ γ hφinj
  have hr : finrank K (LinearMap.range (stepδ ρU ρV σ φ hφ γ)) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hr
  intro x
  exact (exact_stepQ_stepδ ρU ρV σ φ hφ γ x).mp (by
    have : stepδ ρU ρV σ φ hφ γ x ∈ LinearMap.range (stepδ ρU ρV σ φ hφ γ) := ⟨x, rfl⟩
    rw [hr] at this
    exact this)

end Field

section Family

/-! ### The family of twists `F(mD)`, `m ∈ ℤ` -/

variable (σ : MW ≃ₗ[R] MW) (φ : MV →ₗ[R] MV) (hφ : ρV ∘ₗ φ = σ.toLinearMap ∘ₗ ρV)
  (γ : ℤ → MW →ₗ[R] MW) (hγ : ∀ m, γ (m + 1) = σ.toLinearMap ∘ₗ γ m)

include hγ in
lemma family_apply_nat (n : ℕ) (w : MW) : γ n w = σ^[n] (γ 0 w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, Nat.cast_succ, hγ]
    rfl

include hφ in
lemma ρV_iterate (n : ℕ) (b : MV) : ρV (φ^[n] b) = σ^[n] (ρV b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ρV_φ ρV σ φ hφ, ih]

/-- The `n`-th power of `σ` as a linear map. -/
lemma pow_apply_eq_iterate (n : ℕ) (w : MW) : (σ.toLinearMap ^ n) w = σ^[n] w := by
  rw [Module.End.pow_apply]
  rfl

include hφ hγ in
/-- `σⁿ` maps the coboundaries of `F` into those of `F(nD)`. -/
lemma iterate_mem_range (n : ℕ) {w : MW} (hw : w ∈ LinearMap.range (twistDiff ρU ρV (γ 0))) :
    σ^[n] w ∈ LinearMap.range (twistDiff ρU ρV (γ n)) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hw
  refine ⟨(a, φ^[n] b), ?_⟩
  simp only [twistDiff_apply, family_apply_nat σ γ hγ, ρV_iterate ρV σ φ hφ]
  have hlin : ∀ x y : MW, σ^[n] (x - y) = σ^[n] x - σ^[n] y := by
    intro x y
    rw [← pow_apply_eq_iterate, ← pow_apply_eq_iterate, ← pow_apply_eq_iterate, map_sub]
  rw [hlin]

include hφ hγ in
/-- `σ` maps the coboundaries of `F(mD)` into those of `F((m+1)D)`. -/
lemma sigma_mem_range (m : ℤ) {w : MW} (hw : w ∈ LinearMap.range (twistDiff ρU ρV (γ m))) :
    σ w ∈ LinearMap.range (twistDiff ρU ρV (γ (m + 1))) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hw
  refine ⟨(a, φ b), ?_⟩
  simp only [twistDiff_apply, hγ, LinearMap.comp_apply, LinearEquiv.coe_coe, ρV_φ ρV σ φ hφ,
    map_sub]

include hφ hγ in
lemma iterate_mem_range' (j k : ℕ) {w : MW}
    (hw : w ∈ LinearMap.range (twistDiff ρU ρV (γ j))) :
    σ^[k] w ∈ LinearMap.range (twistDiff ρU ρV (γ ((j + k : ℕ) : ℤ))) := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [Function.iterate_succ_apply', show ((j + (k + 1) : ℕ) : ℤ) = ((j + k : ℕ) : ℤ) + 1 by
      push_cast; ring]
    exact sigma_mem_range ρU ρV σ φ hφ γ hγ _ ih

include hφ hγ in
/-- **Serre vanishing for the twists, general form**: if every element of `MW` becomes a
coboundary of some twist `F(nD)` after multiplication by `fⁿ` (this is `H¹(X ∖ D, F) = 0`) and
`H¹(F)` is finitely generated, then `H¹(F(mD)) = 0` for all `m ≫ 0`. -/
theorem exists_forall_subsingleton_H1_of_limit [Module.Finite R (H1 ρU ρV (γ 0))]
    (hlim : ∀ w : MW, ∃ n : ℕ, σ^[n] w ∈ LinearMap.range (twistDiff ρU ρV (γ n))) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Subsingleton (H1 ρU ρV (γ m)) := by
  classical
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := H1 ρU ρV (γ 0))
  choose w hw using fun i => Submodule.Quotient.mk_surjective _ (s i)
  choose n hn using fun i => hlim (w i)
  refine ⟨Finset.univ.sup n, fun m hm => ?_⟩
  -- `T = σ⁻ᵐ(coboundaries of F(mD))` contains the coboundaries of `F` and the lifts `w i`
  let T := Submodule.comap (σ.toLinearMap ^ m) (LinearMap.range (twistDiff ρU ρV (γ m)))
  have hL : LinearMap.range (twistDiff ρU ρV (γ 0)) ≤ T := by
    intro x hx
    rw [Submodule.mem_comap, pow_apply_eq_iterate]
    exact iterate_mem_range ρU ρV σ φ hφ γ hγ m hx
  have hwT : ∀ i, w i ∈ T := by
    intro i
    rw [Submodule.mem_comap]
    have hni : n i ≤ m := (Finset.le_sup (Finset.mem_univ i)).trans hm
    have := iterate_mem_range' ρU ρV σ φ hφ γ hγ (n i) (m - n i) (hn i)
    rw [Nat.add_sub_cancel' hni, ← Function.iterate_add_apply, Nat.sub_add_cancel hni] at this
    rwa [pow_apply_eq_iterate]
  have hmap : Submodule.map (LinearMap.range (twistDiff ρU ρV (γ 0))).mkQ T = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨w i, hwT i, hw i⟩
  have htop : T = ⊤ := by
    have h := Submodule.comap_map_mkQ (LinearMap.range (twistDiff ρU ρV (γ 0))) T
    rw [hmap, Submodule.comap_top, sup_eq_right.mpr hL] at h
    exact h.symm
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (σ.surjective.iterate m) x
  have hy : y ∈ T := by rw [htop]; trivial
  rw [Submodule.mem_comap, pow_apply_eq_iterate] at hy
  exact hy

include hφ hγ in
/-- **Serre vanishing for the twists** (blueprint `lem:sm-serre-vanishing-curve`): if every
element of `MW` becomes a restriction from `MV` after multiplication by a power of `f` (that is,
`U ∩ V = D(f)` in `V`, the complement of `D` is `U`) and `H¹(F)` is finitely generated, then
`H¹(F(mD)) = 0` for all `m ≫ 0`. -/
theorem exists_forall_subsingleton_H1 [Module.Finite R (H1 ρU ρV (γ 0))]
    (hlim : ∀ w : MW, ∃ n : ℕ, σ^[n] w ∈ LinearMap.range ρV) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Subsingleton (H1 ρU ρV (γ m)) :=
  exists_forall_subsingleton_H1_of_limit ρU ρV σ φ hφ γ hγ fun w => by
    obtain ⟨n, b, hb⟩ := hlim w
    exact ⟨n, (0, b), by simp [hb]⟩

include hφ hγ in
/-- **Global generation on `U`**: under the same limit condition, every section `a` over `U` extends
to a global section `(a, b)` of `F(mD)` for all `m ≫ 0`. -/
theorem exists_mem_H0_of_limit (hlim : ∀ w : MW, ∃ n : ℕ, σ^[n] w ∈ LinearMap.range ρV)
    (a : MU) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ b : MV, (a, b) ∈ H0 ρU ρV (γ m) := by
  obtain ⟨n, b, hb⟩ := hlim (γ 0 (ρU a))
  refine ⟨n, fun m hm => ⟨φ^[m - n] b, ?_⟩⟩
  rw [LinearMap.mem_ker, twistDiff_apply, family_apply_nat σ γ hγ, ρV_iterate ρV σ φ hφ, hb,
    ← Function.iterate_add_apply, Nat.sub_add_cancel hm, sub_self]

include hφ hγ in
/-- **Global generation along `D`** for the family: if `H¹(F(mD)) = 0`, every class of
`MV ⧸ f MV` is the `V`-component of a global section of `F((m+1)D)`. -/
theorem stepQ_surjective_family (m : ℤ) [Subsingleton (H1 ρU ρV (γ m))] :
    ∀ x : MV ⧸ LinearMap.range φ, ∃ p ∈ H0 ρU ρV (γ (m + 1)),
      (LinearMap.range φ).mkQ p.2 = x := by
  intro x
  obtain ⟨p, hp⟩ := stepQ_surjective_of_subsingleton ρU ρV σ φ hφ (γ m) x
  refine ⟨p.val, ?_, hp⟩
  rw [hγ m]
  exact p.property

end Family

section FieldFamily

variable {K : Type u₁} [Field K] {MU : Type u₂} {MV : Type u₃} {MW : Type u₄}
  [AddCommGroup MU] [Module K MU] [AddCommGroup MV] [Module K MV] [AddCommGroup MW]
  [Module K MW] (ρU : MU →ₗ[K] MW) (ρV : MV →ₗ[K] MW) (σ : MW ≃ₗ[K] MW) (φ : MV →ₗ[K] MV)
  (hφ : ρV ∘ₗ φ = σ.toLinearMap ∘ₗ ρV) (hφinj : Function.Injective φ)
  (γ : ℤ → MW →ₗ[K] MW) (hγ : ∀ m, γ (m + 1) = σ.toLinearMap ∘ₗ γ m)
  [FiniteDimensional K (MV ⧸ LinearMap.range φ)]

include hφ hφinj hγ

/-- All twists have finite-dimensional cohomology if `F` does. -/
theorem finiteDimensional_family [FiniteDimensional K (H0 ρU ρV (γ 0))]
    [FiniteDimensional K (H1 ρU ρV (γ 0))] (m : ℤ) :
    FiniteDimensional K (H0 ρU ρV (γ m)) ∧ FiniteDimensional K (H1 ρU ρV (γ m)) := by
  induction m using Int.induction_on with
  | zero => exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [hγ]
    exact ⟨finiteDimensional_H0_step ρU ρV σ φ hφ (γ n),
      finiteDimensional_H1_step ρU ρV σ φ hφ (γ n)⟩
  | pred n ih =>
    obtain ⟨h0, h1⟩ := ih
    have e := hγ (-(n : ℤ) - 1)
    rw [sub_add_cancel] at e
    rw [e] at h0 h1
    exact ⟨finiteDimensional_H0_of_step ρU ρV σ φ hφ _ hφinj,
      finiteDimensional_H1_of_step ρU ρV σ φ hφ _⟩

/-- **Weak Riemann–Roch for the twists** (blueprint `thm:sm-weak-rr`):
`χ(F(mD)) = χ(F) + m · dim (MV ⧸ f MV)` for every `m ∈ ℤ`. -/
theorem euler_family [FiniteDimensional K (H0 ρU ρV (γ 0))]
    [FiniteDimensional K (H1 ρU ρV (γ 0))] (m : ℤ) :
    euler ρU ρV (γ m) = euler ρU ρV (γ 0) + m * finrank K (MV ⧸ LinearMap.range φ) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1⟩ := finiteDimensional_family ρU ρV σ φ hφ hφinj γ hγ n
    rw [hγ, euler_step ρU ρV σ φ hφ (γ n) hφinj, ih]
    ring
  | pred n ih =>
    have e := hγ (-(n : ℤ) - 1)
    rw [sub_add_cancel] at e
    obtain ⟨h0, h1⟩ := finiteDimensional_family ρU ρV σ φ hφ hφinj γ hγ (-(n : ℤ) - 1)
    have := euler_step ρU ρV σ φ hφ (γ (-(n : ℤ) - 1)) hφinj
    rw [← e, ih] at this
    linarith

/-- `dim H¹(F(mD))` is non-increasing in `m`. -/
theorem finrank_H1_family_succ_le [FiniteDimensional K (H0 ρU ρV (γ 0))]
    [FiniteDimensional K (H1 ρU ρV (γ 0))] (m : ℤ) :
    finrank K (H1 ρU ρV (γ (m + 1))) ≤ finrank K (H1 ρU ρV (γ m)) := by
  obtain ⟨h0, h1⟩ := finiteDimensional_family ρU ρV σ φ hφ hφinj γ hγ m
  rw [hγ]
  exact finrank_H1_step_le ρU ρV σ φ hφ (γ m)

/-- `dim H¹(F(mD))` is eventually constant. -/
theorem exists_forall_finrank_H1_eq [FiniteDimensional K (H0 ρU ρV (γ 0))]
    [FiniteDimensional K (H1 ρU ρV (γ 0))] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      finrank K (H1 ρU ρV (γ (m + 1))) = finrank K (H1 ρU ρV (γ m)) := by
  classical
  let c : ℕ → ℕ := fun m => finrank K (H1 ρU ρV (γ m))
  have hc : Antitone c := antitone_nat_of_succ_le fun m => by
    have := finrank_H1_family_succ_le ρU ρV σ φ hφ hφinj γ hγ m
    simpa [c] using this
  have hex : ∃ n, ∃ m, c m = n := ⟨c 0, 0, rfl⟩
  obtain ⟨m₀, hm₀⟩ := Nat.find_spec hex
  have hmin : ∀ m, Nat.find hex ≤ c m := fun m => Nat.find_min' hex ⟨m, rfl⟩
  refine ⟨m₀, fun m hm => ?_⟩
  have h1 : c (m + 1) ≤ c m₀ := hc (by omega)
  have h2 : c m ≤ c m₀ := hc hm
  have h3 := hmin (m + 1)
  have h4 := hmin m
  have e : c (m + 1) = c m := by omega
  simpa [c] using e

/-- **Global generation along `D` over a field** (no condition on the complement of `D`): for
`m ≫ 0`, every class of `MV ⧸ f MV` is the `V`-component of a global section of `F((m+1)D)`. -/
theorem exists_forall_surjective_family [FiniteDimensional K (H0 ρU ρV (γ 0))]
    [FiniteDimensional K (H1 ρU ρV (γ 0))] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ x : MV ⧸ LinearMap.range φ,
      ∃ p ∈ H0 ρU ρV (γ (m + 1)), (LinearMap.range φ).mkQ p.2 = x := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_finrank_H1_eq ρU ρV σ φ hφ hφinj γ hγ
  refine ⟨m₀, fun m hm x => ?_⟩
  obtain ⟨h0, h1⟩ := finiteDimensional_family ρU ρV σ φ hφ hφinj γ hγ m
  have he := hm₀ m hm
  rw [hγ] at he
  obtain ⟨p, hp⟩ := stepQ_surjective_of_finrank_eq ρU ρV σ φ hφ (γ m) hφinj he x
  refine ⟨p.val, ?_, hp⟩
  rw [hγ]
  exact p.property

end FieldFamily


end DeJongAlterations.StableModification.CurvesField
