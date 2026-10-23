/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Lifting through a two-term complex (non-flat top-degree base change)

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-two-term` (PLAN-OM3 §3 step 1). Let `A` be a
ring, `𝔪` an ideal, `d : M₀ → M₁` and `e : N₀ → N₁` maps of `A`-modules (the two-term Čech
complexes of `𝓛^m` on two affine opens and on their fibres) and `φₚ : Mₚ → Nₚ` with
`φ₁ ∘ d = e ∘ φ₀`. If `𝔪 N₀ = 0`, `φ₀` and `e` are surjective, `ker φ₁ ⊆ 𝔪 M₁` and `coker d` is
finitely generated, then some `a ∈ 1 + 𝔪` kills `coker d`, and for every `z ∈ ker e` there is
`x ∈ ker d` with `φ₀ x = a • z` (`exists_smul_lift_of_twoTerm`).

This is the algebra behind the statement "if `H¹` of the fibre vanishes, sections of the fibre
lift near the fibre" used for the local-to-global projectivity theorem (Temkin, *Stable
modification of relative curves*, Thm 1.1; our replacement of EGA IV₃ 9.6.5). No flatness is
needed: only the top degree of a two-term complex is used (cokernels commute with base change).
-/

namespace DeJongAlterations.StableModification.Projectivity

variable {A : Type*} [CommRing A] (𝔪 : Ideal A)
  {M₀ M₁ N₀ N₁ : Type*} [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup N₀] [Module A N₀] [AddCommGroup N₁] [Module A N₁]

/-- **Lifting through a two-term complex** (blueprint `lem:sm-ltg-two-term`). -/
theorem exists_smul_lift_of_twoTerm (d : M₀ →ₗ[A] M₁) (e : N₀ →ₗ[A] N₁)
    (φ₀ : M₀ →ₗ[A] N₀) (φ₁ : M₁ →ₗ[A] N₁) (hcomm : ∀ x, φ₁ (d x) = e (φ₀ x))
    (hN : ∀ a ∈ 𝔪, ∀ n : N₀, a • n = 0) (hφ₀ : Function.Surjective φ₀)
    (hφ₁ : LinearMap.ker φ₁ ≤ 𝔪 • ⊤) (he : Function.Surjective e)
    (hfin : (⊤ : Submodule A (M₁ ⧸ LinearMap.range d)).FG) :
    ∃ a : A, a - 1 ∈ 𝔪 ∧ (∀ k : M₁, ∃ w : M₀, d w = a • k) ∧
      ∀ z : N₀, e z = 0 → ∃ x : M₀, d x = 0 ∧ φ₀ x = a • z := by
  -- `coker d = 𝔪 • coker d`
  have hle : (⊤ : Submodule A (M₁ ⧸ LinearMap.range d)) ≤ 𝔪 • ⊤ := by
    rintro q -
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨z, hz⟩ := he (φ₁ k)
    obtain ⟨w, rfl⟩ := hφ₀ z
    have hk : k - d w ∈ LinearMap.ker φ₁ := by
      rw [LinearMap.mem_ker, map_sub, hcomm, hz, sub_self]
    have hmem : k - d w ∈ (𝔪 • ⊤ : Submodule A M₁) := hφ₁ hk
    have hq : (Submodule.Quotient.mk k : M₁ ⧸ LinearMap.range d) =
        Submodule.Quotient.mk (k - d w) := by
      rw [Submodule.Quotient.eq]
      simp
    rw [hq]
    have hmap := Submodule.mem_map_of_mem (f := (LinearMap.range d).mkQ) hmem
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono le_rfl le_top hmap
  obtain ⟨a, ha, hakill⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤
    hfin hle
  have hcok : ∀ k : M₁, ∃ w : M₀, d w = a • k := by
    intro k
    have h0 := hakill (Submodule.Quotient.mk k) trivial
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, hw⟩
  refine ⟨a, ha, hcok, fun z hz => ?_⟩
  obtain ⟨x', rfl⟩ := hφ₀ z
  have hdx : d x' ∈ LinearMap.ker φ₁ := by
    rw [LinearMap.mem_ker, hcomm, hz]
  have hdx' : d x' ∈ (𝔪 • ⊤ : Submodule A M₁) := hφ₁ hdx
  -- write `d x' = ∑ mᵢ kᵢ` and lift `a • kᵢ = d wᵢ`
  have key : ∀ y ∈ (𝔪 • ⊤ : Submodule A M₁), ∃ w : M₀, d w = a • y ∧ φ₀ w = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr k _
      obtain ⟨w, hw⟩ := hcok k
      refine ⟨r • w, ?_, ?_⟩
      · rw [map_smul, hw, smul_comm]
      · rw [map_smul]
        exact hN r hr _
    · rintro y₁ y₂ ⟨w₁, h₁, h₁'⟩ ⟨w₂, h₂, h₂'⟩
      exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, smul_add], by rw [map_add, h₁', h₂', add_zero]⟩
  obtain ⟨w, hw, hw'⟩ := key _ hdx'
  refine ⟨a • x' - w, ?_, ?_⟩
  · rw [map_sub, map_smul, hw, sub_self]
  · rw [map_sub, map_smul, hw', sub_zero]

end DeJongAlterations.StableModification.Projectivity
