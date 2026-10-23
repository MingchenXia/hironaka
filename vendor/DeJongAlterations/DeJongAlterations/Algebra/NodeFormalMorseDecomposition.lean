import DeJongAlterations.Algebra.NilpotentPowerSeriesSubstitution
import Mathlib.Tactic.FinCases

/-!
# Deterministic coefficient decomposition for a split formal node

All ideal assertions are coefficientwise. No equality with an extended ideal
in a formal power series ring is asserted or needed.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

universe u
variable {R : Type u} [CommRing R]

/-- The literal two-variable formal series ring. -/
abbrev Series (R : Type u) := MvPowerSeries (Fin 2) R

/-- All monomials with a positive first exponent, divided by the first variable. -/
def firstPart (H : Series R) : Series R :=
  fun d => coeff (d + Finsupp.single 0 1) H

/-- The remaining positive second-exponent monomials, divided by the second variable. -/
def secondPart (H : Series R) : Series R :=
  fun d => if d 0 = 0 then coeff (d + Finsupp.single 1 1) H else 0

@[simp]
theorem coeff_firstPart (H : Series R) (d : Fin 2 →₀ ℕ) :
    coeff d (firstPart H) = coeff (d + Finsupp.single 0 1) H := rfl

@[simp]
theorem coeff_secondPart (H : Series R) (d : Fin 2 →₀ ℕ) :
    coeff d (secondPart H) =
      if d 0 = 0 then coeff (d + Finsupp.single 1 1) H else 0 := rfl

/-- The deterministic decomposition preserves the exact original constant. -/
theorem decomposition (H : Series R) :
    H = C (constantCoeff H) + X 0 * firstPart H + X 1 * secondPart H := by
  apply MvPowerSeries.ext
  intro d
  rw [map_add, map_add, X, X, coeff_monomial_mul, coeff_monomial_mul]
  by_cases h0 : d 0 = 0
  · have hn0 : ¬ Finsupp.single 0 1 ≤ d := by simp [Finsupp.single_le_iff, h0]
    rw [if_neg hn0]
    by_cases h1 : d 1 = 0
    · have hd : d = 0 := by
        ext i
        fin_cases i
        · exact h0
        · exact h1
      subst d
      simp [coeff_zero_C, coeff_zero_eq_constantCoeff]
    · have hl1 : Finsupp.single 1 1 ≤ d :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h1)
      have hz : (d - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = 0 := by simp [h0]
      rw [if_pos hl1, one_mul, coeff_secondPart, if_pos hz, tsub_add_cancel_of_le hl1]
      have hd : d ≠ 0 := by intro he; subst d; simp at h1
      simp [coeff_C_of_ne_zero hd]
  · have hl0 : Finsupp.single 0 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
    rw [if_pos hl0, one_mul, coeff_firstPart, tsub_add_cancel_of_le hl0]
    have hd : d ≠ 0 := by intro he; subst d; simp at h0
    rw [coeff_C_of_ne_zero hd, zero_add]
    by_cases hl1 : Finsupp.single 1 1 ≤ d
    · simp [hl1, coeff_secondPart, h0]
    · simp [hl1]

/-- Every coefficient selected for the first correction remains in the original ideal. -/
theorem firstPart_coeff_mem (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : ∀ d, coeff d (firstPart H) ∈ J :=
  fun _ => hH _

/-- Every coefficient selected for the second correction remains in the original ideal. -/
theorem secondPart_coeff_mem (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : ∀ d, coeff d (secondPart H) ∈ J := by
  intro d
  rw [coeff_secondPart]
  split_ifs
  · exact hH _
  · exact J.zero_mem

/-- The original constant satisfies the same coefficientwise ideal condition. -/
theorem constantCoeff_mem (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : constantCoeff H ∈ J := hH 0

/-- The native finite product-coefficient formula gives the product of the original ideals. -/
theorem mul_coeff_mem {σ : Type*} (J K : Ideal R) (f g : MvPowerSeries σ R)
    (hf : ∀ d, coeff d f ∈ J) (hg : ∀ d, coeff d g ∈ K) :
    ∀ d, coeff d (f * g) ∈ J * K := by
  classical
  intro d
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_mul (hf p.1) (hg p.2)

end DeJongAlterations.Algebra.NodeFormalMorse
