/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPrincipalJetMultiplication
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The EXISTING all-order principal Hilbert--Samuel quotient, from actual original jets. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPrincipalHSFormula
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm HironakaHolomorphicPointJets
  HironakaActualPrincipalJetMultiplication HironakaRelativeNormalActualBaseJetDimension
variable {n : ℕ}
local notation "R" => HolGerm (ComplexModel n)
local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- The actual original principal jet projection, with unchanged original complex action. -/
def actualPrincipalJetProjection (f : R) (q : ℕ) :
    (R ⧸ 𝔪 ^ q) →ₗ[ℂ] (R ⧸ (Ideal.span ({f} : Set R) ⊔ 𝔪 ^ q)) :=
  (Ideal.Quotient.factorₐ ℂ (show 𝔪 ^ q ≤ Ideal.span ({f} : Set R) ⊔ 𝔪 ^ q from le_sup_right)).toLinearMap

/-- EVERY original numerator retains its SAME actual class in the original principal quotient. -/
theorem actualPrincipalJetProjection_mk (f : R) (q : ℕ) (g : R) :
    actualPrincipalJetProjection f q (Ideal.Quotient.mk (𝔪 ^ q) g) =
      Ideal.Quotient.mk (Ideal.span ({f} : Set R) ⊔ 𝔪 ^ q) g := rfl

/-- Every actual original principal jet class is in the genuine projection image. -/
theorem actualPrincipalJetProjection_surjective (f : R) (q : ℕ) :
    Function.Surjective (actualPrincipalJetProjection f q) :=
  Ideal.Quotient.factor_surjective le_sup_right

/-- The ENTIRE actual principal projection kernel is the actual original multiplication range. -/
theorem actualPrincipalJetProjection_kernel (f : R) (μ s : ℕ) (hf : f ∈ 𝔪 ^ μ) :
    LinearMap.ker (actualPrincipalJetProjection f (s+μ)) =
      LinearMap.range ((actualPrincipalJetMul f μ s hf).restrictScalars ℂ) := by
  ext u
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective u
  constructor
  · intro hu
    change Ideal.Quotient.mk (Ideal.span ({f} : Set R) ⊔ 𝔪 ^ (s+μ)) g=0 at hu
    obtain ⟨h,hh,k,hk,hg⟩ := Submodule.mem_sup.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hu)
    have heq : Ideal.Quotient.mk (𝔪 ^ (s+μ)) h = Ideal.Quotient.mk (𝔪 ^ (s+μ)) g := by
      rw [← hg,map_add,(Ideal.Quotient.eq_zero_iff_mem).mpr hk,add_zero]
    have him := (actualPrincipalJetMul_range_iff f μ s hf _).mpr ⟨h,hh,heq⟩
    exact him
  · rintro ⟨v,hv⟩
    obtain ⟨h,hh,heq⟩ := (actualPrincipalJetMul_range_iff f μ s hf _).mp ⟨v,hv⟩
    change actualPrincipalJetProjection f (s+μ) (Ideal.Quotient.mk (𝔪 ^ (s+μ)) g)=0
    rw [← heq,actualPrincipalJetProjection_mk]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Submodule.mem_sup_left hh)

/-- Genuine rank-nullity uses the whole original kernel and actual injective multiplication. -/
theorem actualPrincipalJetDimension_add (f : R) (μ s : ℕ)
    (hf : f ∈ 𝔪 ^ μ) (hfn : f ∉ 𝔪 ^ (μ+1)) :
    Module.finrank ℂ (R ⧸ (Ideal.span ({f} : Set R) ⊔ 𝔪 ^ (s+μ))) +
      Module.finrank ℂ (R ⧸ 𝔪 ^ s) = Module.finrank ℂ (R ⧸ 𝔪 ^ (s+μ)) := by
  let := finiteDimensional_quotient_maximalIdeal_pow n s
  let := finiteDimensional_quotient_maximalIdeal_pow n (s+μ)
  have h := (actualPrincipalJetProjection f (s+μ)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (actualPrincipalJetProjection_surjective f (s+μ)),finrank_top,
    actualPrincipalJetProjection_kernel f μ s hf,
    LinearMap.finrank_range_of_inj
      (f := (actualPrincipalJetMul f μ s hf).restrictScalars ℂ)
      (actualPrincipalJetMul_injective f μ s hf hfn)] at h
  exact h

/-- The EXISTING all-order original principal HS is genuinely determined by actual maximal order. -/
theorem hilbertSamuelValue_actual_principal (f : R) (μ : ℕ)
    (hf : f ∈ 𝔪 ^ μ) (hfn : f ∉ 𝔪 ^ (μ+1)) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.span ({f} : Set R)) ℓ =
      Nat.choose (n+ℓ) n - (if μ ≤ ℓ then Nat.choose (n+(ℓ-μ)) n else 0) := by
  by_cases hμ : μ ≤ ℓ
  · rw [if_pos hμ]
    have h := actualPrincipalJetDimension_add f μ (ℓ-μ+1) hf hfn
    have hq : ℓ-μ+1+μ=ℓ+1 := by omega
    rw [hq,actualBaseJetDimension n (ℓ-μ),actualBaseJetDimension n ℓ] at h
    unfold hilbertSamuelValue
    omega
  · rw [if_neg hμ,Nat.sub_zero]
    have hi : Ideal.span ({f} : Set R) ≤ 𝔪 ^ (ℓ+1) := by
      apply Ideal.span_le.mpr
      intro g hg
      have : g=f := Set.mem_singleton_iff.mp hg
      subst g
      exact Ideal.pow_le_pow_right (by omega : ℓ+1 ≤ μ) hf
    unfold hilbertSamuelValue
    rw [sup_eq_right.mpr hi]
    exact actualBaseJetDimension n ℓ

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- A nonzero ORIGINAL germ alone supplies the entire existing principal HS profile. -/
theorem hilbertSamuelValue_actual_principal_order (f : R) (hf : f ≠ 0) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.span ({f} : Set R)) ℓ =
      Nat.choose (n+ℓ) n - (if actualGermOrder f hf ≤ ℓ then
        Nat.choose (n+(ℓ-actualGermOrder f hf)) n else 0) :=
  hilbertSamuelValue_actual_principal f _ (actualGermOrder_spec f hf).1
    (actualGermOrder_spec f hf).2 ℓ
end
end Hironaka.HironakaActualPrincipalHSFormula
