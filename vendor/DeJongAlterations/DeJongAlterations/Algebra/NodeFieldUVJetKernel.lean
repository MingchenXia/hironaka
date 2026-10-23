import DeJongAlterations.Algebra.NodeVariableMorseOrder

/-! Actual mixed division and the ENTIRE uv finite-jet ideal, over any field. -/

noncomputable section

open MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldUVJetKernel

open NodeFormalMorse NodeVariableMorse

universe u
variable {K : Type u} [Field K]

def mixedExponent : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem mixedExponent_le_iff (d : Fin 2 →₀ ℕ) :
    mixedExponent ≤ d ↔ 1 ≤ d 0 ∧ 1 ≤ d 1 := by
  constructor
  · intro h
    constructor
    · simpa [mixedExponent] using h 0
    · simpa [mixedExponent] using h 1
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simpa [mixedExponent] using h0
    · simpa [mixedExponent] using h1

theorem uv_eq_monomial : (X 0 * X 1 : Series K) = monomial mixedExponent 1 := by
  simp only [X, monomial_mul_monomial, one_mul, mixedExponent]

def axisPart (f : Series K) : Series K :=
  fun d => if d 0 = 0 ∨ d 1 = 0 then coeff d f else 0

def mixedPart (f : Series K) : Series K := fun d => coeff (d + mixedExponent) f

/-- The original coefficient decomposition is an equality of ENTIRE actual series. -/
theorem decomposition (f : Series K) : f = axisPart f + (X 0 * X 1) * mixedPart f := by
  ext d
  rw [map_add, uv_eq_monomial, coeff_monomial_mul]
  by_cases hd : mixedExponent ≤ d
  · have hh := (mixedExponent_le_iff d).mp hd
    have ha : ¬ (d 0 = 0 ∨ d 1 = 0) := by omega
    change coeff d f = (if d 0 = 0 ∨ d 1 = 0 then coeff d f else 0) +
      (if mixedExponent ≤ d then 1 * coeff (d - mixedExponent + mixedExponent) f else 0)
    rw [if_neg ha, if_pos hd, tsub_add_cancel_of_le hd, one_mul, zero_add]
  · have ha : d 0 = 0 ∨ d 1 = 0 := by
      have hh := mt (mixedExponent_le_iff d).mpr hd
      omega
    change coeff d f = (if d 0 = 0 ∨ d 1 = 0 then coeff d f else 0) +
      (if mixedExponent ≤ d then 1 * coeff (d - mixedExponent + mixedExponent) f else 0)
    rw [if_pos ha, if_neg hd, add_zero]

def equationIdeal (K : Type u) [Field K] : Ideal (Series K) := Ideal.span {X 0 * X 1}

def jetIdeal (K : Type u) [Field K] (n : ℕ) : Ideal (Series K) :=
  equationIdeal K ⊔ variableIdeal K ^ n

/-- Principal ideal membership retains vanishing of EVERY actual axis coefficient. -/
theorem axis_coeff_zero_of_mem_equationIdeal {f : Series K}
    (hf : f ∈ equationIdeal K) (d : Fin 2 →₀ ℕ) (hd : d 0 = 0 ∨ d 1 = 0) :
    coeff d f = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
  rw [uv_eq_monomial, coeff_monomial_mul]
  have hh : ¬ mixedExponent ≤ d := by
    intro h
    have he := (mixedExponent_le_iff d).mp h
    omega
  exact if_neg hh

/-- The ENTIRE original uv-plus-power ideal is detected by the actual original axis coefficients. -/
theorem mem_jetIdeal_iff (n : ℕ) (f : Series K) :
    f ∈ jetIdeal K n ↔ ∀ d : Fin 2 →₀ ℕ, d.degree < n →
      (d 0 = 0 ∨ d 1 = 0) → coeff d f = 0 := by
  constructor
  · intro hf d hdeg hd
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hf
    rw [← hab, map_add, axis_coeff_zero_of_mem_equationIdeal ha d hd, zero_add]
    exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hdeg)
      ((mem_variableIdeal_pow_iff_order n b).mp hb))
  · intro hf
    have ha : axisPart f ∈ variableIdeal K ^ n := by
      apply (mem_variableIdeal_pow_iff_order n _).mpr
      apply nat_le_order
      intro d hdeg
      change (if d 0 = 0 ∨ d 1 = 0 then coeff d f else 0) = 0
      split_ifs with hd
      · exact hf d hdeg hd
      · rfl
    rw [decomposition f]
    apply Ideal.add_mem
    · exact Ideal.mem_sup_right ha
    · apply Ideal.mem_sup_left
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

end DeJongAlterations.Algebra.NodeFieldUVJetKernel
