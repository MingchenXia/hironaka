/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalFibreHilbertSamuel

/-! Genuine ambient maximal-ideal powers retain ALL mixed tangent weights.
The whole weighted normal-truncation quotient is the actual ambient jet
quotient, with its original numerator and complex algebra structure. -/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaRelativeNormalMixedTangentPowers
noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalFibreHilbertSamuel
  HironakaHolomorphicPointJets

/-- Every actual whole mixed term survives the ideal binomial expansion. -/
theorem ideal_sup_pow_eq_mixed {R : Type*} [CommRing R] (M J : Ideal R) (s : ℕ) :
    (M ⊔ J) ^ s = ∑ q ∈ Finset.range (s+1), M ^ (s-q) * J ^ q := by
  rw [sup_comm M J, ← Ideal.add_eq_sup, add_pow]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Ideal.natCast_eq_top (Nat.ne_of_gt (Nat.choose_pos (by
    have h := Finset.mem_range.mp hq
    omega))), Ideal.mul_top, mul_comm]

/-- The literal mixed tangent/normal power ideal in the actual original whole ring. -/
def originalMixedTangentPower (d t s : ℕ) : Ideal (HolGerm (ComplexModel (d+t))) :=
  ∑ q ∈ Finset.range (s+1), originalBaseMaximalIdeal d t ^ (s-q) * normalIdeal d t ^ q

/-- Actual relative Hadamard and the whole binomial expansion give the true ambient power. -/
theorem originalMaximalIdeal_power_eq_mixed (d t s : ℕ) :
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s =
      originalMixedTangentPower d t s := by
  rw [← baseMaximalIdeal_sup_normalIdeal d t]
  exact ideal_sup_pow_eq_mixed _ _ s

/-- Every original ambient ideal retains all actual mixed weights in the full maximal-power sum. -/
theorem originalAmbientIdeal_sup_maximal_power_eq_mixed (d t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s =
      I ⊔ originalMixedTangentPower d t s := by
  rw [originalMaximalIdeal_power_eq_mixed]

/-- The actual normal power is the full degree-s term of the original ambient mixed ideal. -/
theorem originalNormalPower_le_mixed (d t s : ℕ) :
    normalIdeal d t ^ s ≤ originalMixedTangentPower d t s := by
  unfold originalMixedTangentPower
  have h := Finset.single_le_sum
    (f := fun q => originalBaseMaximalIdeal d t ^ (s-q) * normalIdeal d t ^ q)
    (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_self s))
  simpa using h

/-- Actual normal truncation of the SAME whole original ideal. -/
abbrev originalNormalTruncation (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (s : ℕ) : Type :=
  HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ s)

/-- The actual mixed weighted ideal in the genuine normal truncation. -/
def originalMixedTruncationIdeal (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (s : ℕ) : Ideal (originalNormalTruncation d t I s) :=
  Ideal.map (Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s)) (originalMixedTangentPower d t s)

/-- The whole actual weighted normal-truncation quotient, not the base-fibre quotient. -/
abbrev originalAmbientMixedTruncation (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (s : ℕ) : Type :=
  originalNormalTruncation d t I s ⧸ originalMixedTruncationIdeal d t I s

/-- True original ideal containment identifies the double-quotient kernel with the full ambient kernel. -/
theorem originalMixedTruncation_kernel_eq (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    (I ⊔ normalIdeal d t ^ s) ⊔ originalMixedTangentPower d t s =
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s := by
  rw [sup_assoc, sup_eq_right.mpr (originalNormalPower_le_mixed d t s),
    originalMaximalIdeal_power_eq_mixed]

/-- The actual weighted normal truncation is the genuine whole ambient jet algebra. -/
def originalAmbientMixedTruncationAlgEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    originalAmbientMixedTruncation d t I s ≃ₐ[ℂ]
      HolGerm (ComplexModel (d+t)) ⧸
        (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ ℂ (I ⊔ normalIdeal d t ^ s)
    (originalMixedTangentPower d t s)).trans
      (Ideal.quotientEquivAlgOfEq ℂ (originalMixedTruncation_kernel_eq d t I s))

/-- Every actual original numerator keeps its SAME whole ambient class under the true algebra dictionary. -/
theorem originalAmbientMixedTruncationAlgEquiv_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    originalAmbientMixedTruncationAlgEquiv d t I s
      (Ideal.Quotient.mk (originalMixedTruncationIdeal d t I s)
        (Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g)) =
      Ideal.Quotient.mk
        (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s) g := by
  exact Ideal.quotientEquivAlgOfEq_mk ℂ (originalMixedTruncation_kernel_eq d t I s) g

/-- Genuine original finite jets internally give finite dimension of every actual weighted quotient. -/
theorem finiteDimensional_originalAmbientMixedTruncation (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    FiniteDimensional ℂ (originalAmbientMixedTruncation d t I s) := by
  let := finiteDimensional_quotient_sup_maximalIdeal_pow (d+t) s I
  exact FiniteDimensional.of_injective (originalAmbientMixedTruncationAlgEquiv d t I s).toLinearMap
    (originalAmbientMixedTruncationAlgEquiv d t I s).injective

/-- The EXISTING genuine whole ambient Hilbert-Samuel value is exactly the mixed weighted quotient dimension. -/
theorem hilbertSamuelValue_eq_originalAmbientMixedTruncation (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ = Module.finrank ℂ (originalAmbientMixedTruncation d t I (ℓ+1)) :=
  (originalAmbientMixedTruncationAlgEquiv d t I (ℓ+1)).toLinearEquiv.finrank_eq.symm

end
end Hironaka.HironakaRelativeNormalMixedTangentPowers
