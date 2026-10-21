/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualBaseJetDimension
import Hironaka.Analytic.GermOrderProduct
import Mathlib.RingTheory.Filtration

/-! Genuine finite-order principal multiplication on the original holomorphic jets. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPrincipalJetMultiplication
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm HironakaHolomorphicPointJets

variable {n : ℕ}
local notation "R" => HolGerm (ComplexModel n)
local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- The actual Noetherian local ring has no nonzero germ in every positive maximal power. -/
theorem exists_actual_finite_order (f : R) (hf : f ≠ 0) :
    ∃ a : ℕ, f ∉ 𝔪 ^ (a+1) := by
  let := isNoetherianRing_holGerm_euclidean n
  by_contra h
  push Not at h
  have hall : f ∈ ⨅ k : ℕ, 𝔪 ^ k := by
    simp only [Ideal.mem_iInf]
    intro k
    cases k with
    | zero => simp
    | succ k => exact h k
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing 𝔪 (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hall
  exact hf hall

/-- The least genuine failed original maximal power, chosen from the original nonzero germ. -/
def actualGermOrder (f : R) (hf : f ≠ 0) : ℕ := Nat.find (exists_actual_finite_order f hf)

/-- Both actual original order conditions are produced, including order zero for units. -/
theorem actualGermOrder_spec (f : R) (hf : f ≠ 0) :
    f ∈ 𝔪 ^ actualGermOrder f hf ∧ f ∉ 𝔪 ^ (actualGermOrder f hf+1) := by
  refine ⟨?_,Nat.find_spec (exists_actual_finite_order f hf)⟩
  cases h : actualGermOrder f hf with
  | zero => simp
  | succ k =>
    exact not_not.mp (Nat.find_min (exists_actual_finite_order f hf)
      (show k < actualGermOrder f hf by omega))

/-- The genuine two-sided maximal-power conditions determine the original order uniquely. -/
theorem actualGermOrder_unique (f : R) (hf : f ≠ 0) (μ : ℕ)
    (hμ : f ∈ 𝔪 ^ μ) (hμn : f ∉ 𝔪 ^ (μ+1)) : actualGermOrder f hf=μ := by
  obtain ⟨ha,han⟩ := actualGermOrder_spec f hf
  apply Nat.le_antisymm
  · by_contra h
    exact hμn (Ideal.pow_le_pow_right (by omega : μ+1 ≤ actualGermOrder f hf) ha)
  · by_contra h
    exact han (Ideal.pow_le_pow_right (by omega : actualGermOrder f hf+1 ≤ μ) hμ)

/-- Actual analytic point-order cancellation gives BOTH original whole ring membership directions. -/
theorem actual_mul_mem_maximal_pow_iff (f g : R) (μ s : ℕ)
    (hf : f ∈ 𝔪 ^ μ) (hfn : f ∉ 𝔪 ^ (μ+1)) :
    f*g ∈ 𝔪 ^ (s+μ) ↔ g ∈ 𝔪 ^ s := by
  constructor
  · intro h
    obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk f
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    apply (mem_maximalIdeal_pow_iff_point_power hG s).mpr
    apply GermOrderProduct.mem_idealPow_of_mul_mem
      (hG.mono fun _ h => h.mdifferentiableAt) (hF.mono fun _ h => h.mdifferentiableAt)
      (fun hFmem => hfn ((mem_maximalIdeal_pow_iff_point_power hF (μ+1)).mpr hFmem))
    apply (mem_maximalIdeal_pow_iff_point_power (eventually_differentiableAt_mul hG hF) (s+μ)).mp
    change HolGerm.mk G hG * HolGerm.mk F hF ∈ 𝔪 ^ (s+μ)
    simpa only [mul_comm] using h
  · intro hg
    rw [pow_add]
    simpa only [mul_comm] using Ideal.mul_mem_mul hg hf

/-- Multiplication by the same original germ, with its genuine original ring scalar action. -/
def actualPrincipalMulLinear (f : R) : R →ₗ[R] R where
  toFun := fun g => f*g
  map_add' := mul_add f
  map_smul' := by intros; simp only [smul_eq_mul,RingHom.id_apply]; ring

/-- The actual quotient map retains every original germ; no transported scalar action is introduced. -/
def actualPrincipalJetMul (f : R) (μ s : ℕ) (hf : f ∈ 𝔪 ^ μ) :
    (R ⧸ 𝔪 ^ s) →ₗ[R] (R ⧸ 𝔪 ^ (s+μ)) :=
  (𝔪 ^ s).mapQ (𝔪 ^ (s+μ)) (actualPrincipalMulLinear f) (by
    intro g hg
    change f*g ∈ 𝔪 ^ (s+μ)
    rw [pow_add]
    simpa only [mul_comm] using Ideal.mul_mem_mul hg hf)

/-- The genuine induced multiplication formula holds for EVERY original numerator. -/
theorem actualPrincipalJetMul_mk (f : R) (μ s : ℕ) (hf : f ∈ 𝔪 ^ μ) (g : R) :
    actualPrincipalJetMul f μ s hf (Ideal.Quotient.mk (𝔪 ^ s) g) =
      Ideal.Quotient.mk (𝔪 ^ (s+μ)) (f*g) := rfl

/-- The actual multiplication jet map is injective from original analytic cancellation. -/
theorem actualPrincipalJetMul_injective (f : R) (μ s : ℕ)
    (hf : f ∈ 𝔪 ^ μ) (hfn : f ∉ 𝔪 ^ (μ+1)) :
    Function.Injective (actualPrincipalJetMul f μ s hf) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk (𝔪 ^ (s+μ)) (f*g)=0 at hq
  have hg := (actual_mul_mem_maximal_pow_iff f g μ s hf hfn).mp
    ((Ideal.Quotient.eq_zero_iff_mem).mp hq)
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hg

/-- BOTH directions for the entire actual principal image, with original quotient classes. -/
theorem actualPrincipalJetMul_range_iff (f : R) (μ s : ℕ) (hf : f ∈ 𝔪 ^ μ)
    (q : R ⧸ 𝔪 ^ (s+μ)) :
    q ∈ LinearMap.range (actualPrincipalJetMul f μ s hf) ↔
      ∃ h : R, h ∈ Ideal.span ({f} : Set R) ∧ Ideal.Quotient.mk (𝔪 ^ (s+μ)) h=q := by
  constructor
  · rintro ⟨u,rfl⟩
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨f*g,?_,rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rintro ⟨h,hh,rfl⟩
    obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hh
    exact ⟨Ideal.Quotient.mk (𝔪 ^ s) g,rfl⟩
end
end Hironaka.HironakaActualPrincipalJetMultiplication
