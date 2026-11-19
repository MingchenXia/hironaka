import Hironaka.Resolution.HironakaStrictFilteredHilbertSamuel
import Hironaka.Resolution.HironakaHolomorphicPointJets

/-!
# Regular-symbol formulas for the original holomorphic Hilbert–Samuel values

The finite-quotient exact sequence specializes to the actual holomorphic germ ring
and the existing `HironakaHolomorphicPointJets.hilbertSamuelValue`. Finiteness of
every quotient is proved by the original finite-jet theorem. Regularity of the
degree-one symbol remains an explicit hypothesis on the entire original ideal.
-/

set_option autoImplicit false

namespace Hironaka.HironakaHolomorphicRegularSymbolHilbertSamuel

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaStrictFilteredHilbertSamuel

variable {n : ℕ}

/-- The full sequence of original Hilbert–Samuel differences is equivalent to
regularity of the actual degree-one symbol, for the same ideal and germ. -/
theorem regular_symbol_iff_hilbertSamuelValue_parameter_recurrence
    (I : Ideal (HolGerm (ComplexModel n))) (v : HolGerm (ComplexModel n))
    (hv : v ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) :
    (∀ r : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r,
      v * b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 2) →
        b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 1)) ↔
    ∀ q : ℕ,
      hilbertSamuelValue (I ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel n)))) (q + 1) +
        hilbertSamuelValue I q = hilbertSamuelValue I (q + 1) := by
  exact regular_symbol_iff_finrank_quotient_recurrence ℂ I
    (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) v hv
    (fun r => finiteDimensional_quotient_sup_maximalIdeal_pow n (r + 1) I)

/-- Eliminating a regular symbol takes the first difference of the original
holomorphic Hilbert–Samuel values in every positive degree. -/
theorem hilbertSamuelValue_parameter_recurrence
    (I : Ideal (HolGerm (ComplexModel n))) (v : HolGerm (ComplexModel n))
    (hv : v ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))
    (hreg : ∀ r : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r,
      v * b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 2) →
        b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 1))
    (q : ℕ) :
    hilbertSamuelValue (I ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel n)))) (q + 1) +
      hilbertSamuelValue I q = hilbertSamuelValue I (q + 1) := by
  let := finiteDimensional_quotient_sup_maximalIdeal_pow n ((q + 1) + 1) I
  exact finrank_quotient_recurrence ℂ I
    (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) v hv hreg (q + 1)

/-- Every original cumulative value is the finite sum of the original parameter
quotient values; the degree-zero term is included. -/
theorem hilbertSamuelValue_eq_sum_parameter
    (I : Ideal (HolGerm (ComplexModel n))) (v : HolGerm (ComplexModel n))
    (hv : v ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))
    (hreg : ∀ r : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r,
      v * b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 2) →
        b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (r + 1))
    (q : ℕ) :
    hilbertSamuelValue I q =
      ∑ i ∈ Finset.range (q + 1),
        hilbertSamuelValue (I ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel n)))) i := by
  exact finrank_quotient_eq_sum ℂ I
    (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) v hv hreg
    (fun r => finiteDimensional_quotient_sup_maximalIdeal_pow n (r + 1) I) q

end Hironaka.HironakaHolomorphicRegularSymbolHilbertSamuel
