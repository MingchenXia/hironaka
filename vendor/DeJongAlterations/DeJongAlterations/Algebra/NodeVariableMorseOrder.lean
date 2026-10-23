import DeJongAlterations.Algebra.NodeVariableMorseInverse
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Actual variable-ideal powers and deterministic coefficient parts

Total monomial degree here measures the original variable filtration.
No coefficient ideal is introduced.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- Dividing the original positive-first-coordinate terms lowers variable order by one. -/
theorem firstPart_order {f : Series K} {k : ℕ} (hf : ((k + 1 : ℕ) : ℕ∞) ≤ f.order) :
    (k : ℕ∞) ≤ (firstPart f).order := by
  apply nat_le_order
  intro d hd
  rw [coeff_firstPart]
  apply coeff_of_lt_order
  have hdeg : (d + Finsupp.single 0 1).degree < k + 1 := by
    simp only [map_add, Finsupp.degree_single]
    omega
  exact lt_of_lt_of_le (by exact_mod_cast hdeg) hf

/-- The original remaining second-coordinate part has the same actual order bound. -/
theorem secondPart_order {f : Series K} {k : ℕ} (hf : ((k + 1 : ℕ) : ℕ∞) ≤ f.order) :
    (k : ℕ∞) ≤ (secondPart f).order := by
  apply nat_le_order
  intro d hd
  rw [coeff_secondPart]
  split_ifs
  · apply coeff_of_lt_order
    have hdeg : (d + Finsupp.single 1 1).degree < k + 1 := by
      simp only [map_add, Finsupp.degree_single]
      omega
    exact lt_of_lt_of_le (by exact_mod_cast hdeg) hf
  · rfl

/-- Actual original variable-ideal powers are exactly the original total-degree order bounds. -/
theorem mem_variableIdeal_pow_iff_order (k : ℕ) (f : Series K) :
    f ∈ variableIdeal K ^ k ↔ (k : ℕ∞) ≤ f.order := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    constructor
    · intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun r hr s hs => ?_) (fun x y hx hy => ?_)
      · have hs1 : (1 : ℕ∞) ≤ s.order := by
          rw [one_le_order_iff_constCoeff_eq_zero]
          have hle : variableIdeal K ≤ RingHom.ker (constantCoeff : Series K →+* K) :=
            Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [RingHom.mem_ker])
          exact hle hs
        calc
          ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
          _ ≤ r.order + s.order := add_le_add ((ih r).mp hr) hs1
          _ ≤ (r * s).order := le_order_mul
      · exact le_trans (le_min hx hy) min_order_le_add
    · intro hf
      have hc : constantCoeff f = 0 := by
        rw [← one_le_order_iff_constCoeff_eq_zero]
        exact le_trans (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) hf
      rw [decomposition f, hc, map_zero, zero_add, pow_succ']
      exact Ideal.add_mem _
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨0, rfl⟩) ((ih _).mpr (firstPart_order hf)))
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨1, rfl⟩) ((ih _).mpr (secondPart_order hf)))

/-- The actual first deterministic part loses exactly the one permitted variable order. -/
theorem firstPart_mem_pow {f : Series K} {k : ℕ} (hf : f ∈ variableIdeal K ^ (k + 1)) :
    firstPart f ∈ variableIdeal K ^ k :=
  (mem_variableIdeal_pow_iff_order k _).mpr
    (firstPart_order ((mem_variableIdeal_pow_iff_order (k + 1) f).mp hf))

/-- The actual second deterministic part has the same original variable-ideal bound. -/
theorem secondPart_mem_pow {f : Series K} {k : ℕ} (hf : f ∈ variableIdeal K ^ (k + 1)) :
    secondPart f ∈ variableIdeal K ^ k :=
  (mem_variableIdeal_pow_iff_order k _).mpr
    (secondPart_order ((mem_variableIdeal_pow_iff_order (k + 1) f).mp hf))

end DeJongAlterations.Algebra.NodeVariableMorse
