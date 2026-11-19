import Hironaka.Resolution.HironakaActualCauchyDiagramPartition
import Hironaka.Resolution.HironakaActualFiniteDegLexWeights

/-! The SAME arbitrary supported solution preserves the strict-tail weighted
filtration. No preferred recursive quotient or desired continuity is input.
Blueprint FIRST: hironaka-g10-supported-weighted-filtration.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowSupportedWeightedFiltration
noncomputable section
open HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualFiniteDegLexWeights
variable {n k : ℕ}

/- The following four private pure-partition calculations are literally
reused from HironakaActualSupportedFullJetUniqueness, with zero separate
mathematical credit. The new proof begins with the weight induction. -/
private theorem word_mem_all (heads : Fin k → CoordinateWord n) (j : Fin k) :
    heads j ∈ List.ofFn heads := by
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

private theorem word_mem_earlier (heads : Fin k → CoordinateWord n) {j l : Fin k}
    (hjl : j.val < l.val) : heads j ∈ (List.ofFn heads).take l.val := by
  apply List.mem_iff_getElem.mpr
  refine ⟨j.val, ?_, ?_⟩
  · simp only [List.length_take, List.length_ofFn]
    exact lt_min hjl j.isLt
  · simp only [List.getElem_take, List.getElem_ofFn]

private theorem pure_coefficient_at_owner
    (heads : Fin k → CoordinateWord n) (Q : Fin k → MvPowerSeries (Fin n) ℂ)
    (R : MvPowerSeries (Fin n) ℂ)
    (hQ : ∀ j β, ¬ AvoidsCones ((List.ofFn heads).take j.val)
      (β + wordExponent (heads j)) → MvPowerSeries.coeff β (Q j) = 0)
    (hR : ∀ α, ¬ AvoidsCones (List.ofFn heads) α → MvPowerSeries.coeff α R = 0)
    (j : Fin k) (β : Fin n →₀ ℕ)
    (hβ : AvoidsCones ((List.ofFn heads).take j.val) (β + wordExponent (heads j))) :
    MvPowerSeries.coeff (β + wordExponent (heads j))
      ((∑ l, Q l * MvPowerSeries.monomial (wordExponent (heads l)) 1) + R) =
        MvPowerSeries.coeff β (Q j) := by
  let α := β + wordExponent (heads j)
  have hjle : wordExponent (heads j) ≤ α := by
    intro i
    exact Nat.le_add_left _ _
  have hRzero : MvPowerSeries.coeff α R = 0 := by
    apply hR
    intro h
    exact h (heads j) (word_mem_all heads j) hjle
  have hother (l : Fin k) (hlj : l ≠ j) :
      MvPowerSeries.coeff α (Q l * MvPowerSeries.monomial (wordExponent (heads l)) 1) = 0 := by
    by_cases hle : wordExponent (heads l) ≤ α
    · have hjl : j.val < l.val := by
        by_contra h
        have hlj' : l.val < j.val := by
          have hne : l.val ≠ j.val := fun he => hlj (Fin.ext he)
          omega
        exact hβ (heads l) (word_mem_earlier heads hlj') hle
      have hbad : ¬ AvoidsCones ((List.ofFn heads).take l.val)
          ((α - wordExponent (heads l)) + wordExponent (heads l)) := by
        intro hav
        apply hav (heads j) (word_mem_earlier heads hjl)
        rw [tsub_add_cancel_of_le hle]
        exact hjle
      rw [MvPowerSeries.coeff_mul_monomial, if_pos hle, hQ l _ hbad, zero_mul]
    · rw [MvPowerSeries.coeff_mul_monomial, if_neg hle]
  rw [map_add, map_sum, Finset.sum_eq_single j, hRzero, add_zero]
  · rw [MvPowerSeries.coeff_mul_monomial, if_pos hjle, mul_one]
    change MvPowerSeries.coeff ((β + wordExponent (heads j)) - wordExponent (heads j)) (Q j) = _
    rw [add_tsub_cancel_right]
  · intro l _ hlj
    exact hother l hlj
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private theorem pure_coefficient_at_remainder
    (heads : Fin k → CoordinateWord n) (Q : Fin k → MvPowerSeries (Fin n) ℂ)
    (R : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ)
    (hα : AvoidsCones (List.ofFn heads) α) :
    MvPowerSeries.coeff α
      ((∑ j, Q j * MvPowerSeries.monomial (wordExponent (heads j)) 1) + R) =
        MvPowerSeries.coeff α R := by
  rw [map_add, map_sum]
  have hz (j : Fin k) :
      MvPowerSeries.coeff α (Q j * MvPowerSeries.monomial (wordExponent (heads j)) 1) = 0 := by
    rw [MvPowerSeries.coeff_mul_monomial,
      if_neg (hα (heads j) (word_mem_all heads j))]
  simp only [hz, Finset.sum_const_zero, zero_add]

private theorem weightedDegree_add (W : Fin n → ℕ) (α β : Fin n →₀ ℕ) :
    weightedDegree W (α+β) = weightedDegree W α + weightedDegree W β := by
  simp only [weightedDegree, Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib]

/-- The SAME supported quotient/remainder tuple retains all strict-tail
weight bounds. No preferred recursive solution or desired filtration is input. -/
theorem weighted_filtration_of_supported_division
    (heads : Fin k → CoordinateWord n) (W : Fin n → ℕ)
    (f : MvPowerSeries (Fin n) ℂ) (Q T : Fin k → MvPowerSeries (Fin n) ℂ)
    (R : MvPowerSeries (Fin n) ℂ)
    (hDivision : f = (∑ j, Q j * (MvPowerSeries.monomial (wordExponent (heads j)) 1 + T j)) + R)
    (hQ : ∀ j β, ¬ AvoidsCones ((List.ofFn heads).take j.val)
      (β + wordExponent (heads j)) → MvPowerSeries.coeff β (Q j) = 0)
    (hR : ∀ α, ¬ AvoidsCones (List.ofFn heads) α → MvPowerSeries.coeff α R = 0)
    (hT : ∀ j γ, weightedDegree W γ ≤ weightedDegree W (wordExponent (heads j)) →
      MvPowerSeries.coeff γ (T j) = 0)
    (b : ℕ) (hf : ∀ α, weightedDegree W α < b → MvPowerSeries.coeff α f = 0) :
    (∀ j β, weightedDegree W β + weightedDegree W (wordExponent (heads j)) < b →
      MvPowerSeries.coeff β (Q j) = 0) ∧
    ∀ α, weightedDegree W α < b → MvPowerSeries.coeff α R = 0 := by
  let D := (∑ j, Q j * MvPowerSeries.monomial (wordExponent (heads j)) 1) + R
  have hSplit : f = D + ∑ j, Q j * T j := by
    rw [hDivision]
    dsimp only [D]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hInd : ∀ m : ℕ, m < b →
      (∀ j β, weightedDegree W β + weightedDegree W (wordExponent (heads j)) = m →
        MvPowerSeries.coeff β (Q j) = 0) ∧
      ∀ α, weightedDegree W α = m → MvPowerSeries.coeff α R = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      have hPure : ∀ α, weightedDegree W α = m → MvPowerSeries.coeff α D = 0 := by
        intro α hα
        have hTail : MvPowerSeries.coeff α (∑ j, Q j * T j) = 0 := by
          rw [map_sum]
          apply Finset.sum_eq_zero
          intro j _
          rw [MvPowerSeries.coeff_mul]
          apply Finset.sum_eq_zero
          intro p hp
          by_cases hz : MvPowerSeries.coeff p.2 (T j) = 0
          · rw [hz, mul_zero]
          · have hgt : weightedDegree W (wordExponent (heads j)) < weightedDegree W p.2 := by
              by_contra hn
              exact hz (hT j p.2 (Nat.le_of_not_gt hn))
            have hsum : weightedDegree W p.1 + weightedDegree W p.2 = m := by
              rw [← weightedDegree_add, Finset.mem_antidiagonal.mp hp, hα]
            have hlt : weightedDegree W p.1 + weightedDegree W (wordExponent (heads j)) < m := by
              omega
            rw [(ih _ hlt (lt_trans hlt hm)).1 j p.1 rfl, zero_mul]
        have he := congrArg (MvPowerSeries.coeff α) hSplit
        rw [hf α (by omega), map_add, hTail, add_zero] at he
        exact he.symm
      constructor
      · intro j β hβ
        by_cases hs : AvoidsCones ((List.ofFn heads).take j.val) (β + wordExponent (heads j))
        · have hz := hPure (β + wordExponent (heads j)) (by rw [weightedDegree_add, hβ])
          rw [pure_coefficient_at_owner heads Q R hQ hR j β hs] at hz
          exact hz
        · exact hQ j β hs
      · intro α hα
        by_cases hs : AvoidsCones (List.ofFn heads) α
        · have hz := hPure α hα
          rw [pure_coefficient_at_remainder heads Q R α hs] at hz
          exact hz
        · exact hR α hs
  constructor
  · intro j β hβ
    exact (hInd _ hβ).1 j β rfl
  · intro α hα
    exact (hInd _ hα).2 α rfl

end
end Hironaka.HironakaChowSupportedWeightedFiltration
