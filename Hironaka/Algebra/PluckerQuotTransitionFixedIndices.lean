import Hironaka.Algebra.PluckerQuotTransitionComplementNormalization
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual original selected indices construct the fixed original pivot permutation

All source coordinates stay in the SAME original ambient sum. Native finite
cardinal equivalences construct the actual row and original complement maps.
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

universe u

variable {ι ν I : Type u} [Fintype ι] [Fintype ν] [Fintype I]
  [DecidableEq ι] [DecidableEq ν] [DecidableEq I]

/-- The actual selected-rank cardinal constructs an actual fixed-original-row equivalence. -/
def originalFixedPivotRowEquiv (hcard : Nat.card I = Fintype.card ι) : ι ≃ I :=
  Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard.symm)

/-- The actual original ambient selected/complement cardinal identity constructs an actual original complementary-column equivalence. -/
def originalFixedPivotComplementEquiv (a : I ↪ (ι ⊕ ν))
    (hcard : Nat.card I = Fintype.card ι) : ν ≃ ((Set.range a)ᶜ : Set (ι ⊕ ν)) := by
  have h := Nat.card_congr (originalPivotComplementEquiv a)
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum] at h
  have hI : Fintype.card I = Fintype.card ι := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact Fintype.equivOfCardEq (by omega)

/-- The SAME original selected columns and complement form an actual permutation of ORIGINAL ambient coordinates. -/
def originalFixedPivotPermutation (a : I ↪ (ι ⊕ ν))
    (hcard : Nat.card I = Fintype.card ι) : (ι ⊕ ν) ≃ (ι ⊕ ν) :=
  (Equiv.sumCongr (originalFixedPivotRowEquiv hcard)
    (originalFixedPivotComplementEquiv a hcard)).trans (originalPivotComplementEquiv a)

omit [DecidableEq I] in
@[simp]
theorem originalFixedPivotPermutation_inl (a : I ↪ (ι ⊕ ν))
    (hcard : Nat.card I = Fintype.card ι) (i : ι) :
    originalFixedPivotPermutation a hcard (Sum.inl i) = a (originalFixedPivotRowEquiv hcard i) := rfl

omit [DecidableEq I] in
@[simp]
theorem originalFixedPivotPermutation_inr (a : I ↪ (ι ⊕ ν))
    (hcard : Nat.card I = Fintype.card ι) (j : ν) :
    originalFixedPivotPermutation a hcard (Sum.inr j) =
      (originalFixedPivotComplementEquiv a hcard j).val := rfl

end Hironaka.Algebra.PluckerQuotTransition
