import Hironaka.Resolution.HironakaHolomorphicRegularSymbolHilbertSamuel

/-! Equality of the actual original Hilbert–Samuel profiles survives regular parameters. -/

set_option autoImplicit false

namespace Hironaka.HironakaHolomorphicParameterValueConstancy

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaHolomorphicRegularSymbolHilbertSamuel

variable {n : ℕ}

/-- A parameter in the original maximal ideal leaves the actual degree-zero quotient unchanged. -/
theorem hilbertSamuelValue_parameter_zero
    (I : Ideal (HolGerm (ComplexModel n))) (v : HolGerm (ComplexModel n))
    (hv : v ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) :
    hilbertSamuelValue (I ⊔ Ideal.span {v}) 0 = hilbertSamuelValue I 0 := by
  have hs : Ideal.span ({v} : Set (HolGerm (ComplexModel n))) ≤
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)
  have hDen : (I ⊔ Ideal.span {v}) ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) =
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
    rw [sup_assoc, sup_eq_right.mpr hs]
  have hDenPow : (I ⊔ Ideal.span {v}) ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ 1 =
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ 1 := by
    simpa only [pow_one] using hDen
  exact congrArg (fun K : Ideal (HolGerm (ComplexModel n)) =>
    Module.finrank ℂ (HolGerm (ComplexModel n) ⧸ K)) hDenPow

/-- Entire original profiles remain equal after eliminating respective regular symbols. -/
theorem hilbertSamuelValue_parameter_eq_of_eq
    (I J : Ideal (HolGerm (ComplexModel n))) (v w : HolGerm (ComplexModel n))
    (hv : v ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))
    (hw : w ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))
    (hI : ∀ r : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r,
      v * b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 2) →
      b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 1))
    (hJ : ∀ r : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r,
      w * b ∈ J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 2) →
      b ∈ J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 1))
    (hvalue : ∀ q : ℕ, hilbertSamuelValue I q = hilbertSamuelValue J q)
    (q : ℕ) :
    hilbertSamuelValue (I ⊔ Ideal.span {v}) q =
      hilbertSamuelValue (J ⊔ Ideal.span {w}) q := by
  cases q with
  | zero => rw [hilbertSamuelValue_parameter_zero I v hv,
      hilbertSamuelValue_parameter_zero J w hw, hvalue 0]
  | succ q =>
    have hLeft := hilbertSamuelValue_parameter_recurrence I v hv hI q
    have hRight := hilbertSamuelValue_parameter_recurrence J w hw hJ q
    rw [hvalue q, hvalue (q + 1)] at hLeft
    exact Nat.add_right_cancel (hLeft.trans hRight.symm)

end Hironaka.HironakaHolomorphicParameterValueConstancy
