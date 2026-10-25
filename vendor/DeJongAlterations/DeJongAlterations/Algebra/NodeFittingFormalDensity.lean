import DeJongAlterations.Algebra.NodeFormalMorseDecomposition
import DeJongAlterations.Algebra.NodeGeometricCompletionDerivation
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Actual variable-adic density with arbitrary original commutative coefficients

Only native total-degree truncations and the actual original variable ideal are
used. There is no identification with the coefficient ideal. The order proof
extends the elementary coefficient argument from NodeVariableMorseOrder to the
arbitrary commutative coefficients needed for the relative Q-h model.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingFormalDensity

open MvPowerSeries NodeFormalMorse

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- The SAME actual variable ideal, with arbitrary original coefficients. -/
abbrev variableIdeal (R : Type u) [CommRing R] : Ideal (Series R) :=
  Ideal.span (Set.range (X : Fin 2 → Series R))

/-- The actual first coefficient part loses exactly one unit of original variable order. -/
theorem firstPart_order {f : Series R} {k : ℕ} (hf : ((k + 1 : ℕ) : ℕ∞) ≤ f.order) :
    (k : ℕ∞) ≤ (firstPart f).order := by
  apply nat_le_order
  intro d hd
  rw [coeff_firstPart]
  apply coeff_of_lt_order
  have hdeg : (d + Finsupp.single 0 1).degree < k + 1 := by
    simp only [map_add, Finsupp.degree_single]
    omega
  exact lt_of_lt_of_le (by exact_mod_cast hdeg) hf

/-- The actual remaining coefficient part has the same original order bound. -/
theorem secondPart_order {f : Series R} {k : ℕ} (hf : ((k + 1 : ℕ) : ℕ∞) ≤ f.order) :
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

/-- ENTIRE actual variable powers are exactly the original total-degree order bounds. -/
theorem mem_variableIdeal_pow_iff_order (n : ℕ) (f : Series R) :
    f ∈ variableIdeal R ^ n ↔ (n : ℕ∞) ≤ f.order := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    constructor
    · intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · have hb1 : (1 : ℕ∞) ≤ b.order := by
          rw [one_le_order_iff_constCoeff_eq_zero]
          have hle : variableIdeal R ≤ RingHom.ker (constantCoeff : Series R →+* R) :=
            Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [RingHom.mem_ker])
          exact hle hb
        calc
          ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
          _ ≤ a.order + b.order := add_le_add ((ih a).mp ha) hb1
          _ ≤ (a * b).order := le_order_mul
      · exact le_trans (le_min ha hb) min_order_le_add
    · intro hf
      have hc : constantCoeff f = 0 := by
        rw [← one_le_order_iff_constCoeff_eq_zero]
        exact le_trans (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hf
      rw [decomposition f, hc, map_zero, zero_add, pow_succ']
      exact Ideal.add_mem _
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨0, rfl⟩) ((ih _).mpr (firstPart_order hf)))
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨1, rfl⟩) ((ih _).mpr (secondPart_order hf)))

/-- The SAME actual native total-degree polynomial truncation approximates the original series. -/
theorem sub_truncTotal_mem_variableIdeal_pow (n : ℕ) (f : Series R) :
    f - (f.truncTotal n : Series R) ∈ variableIdeal R ^ n := by
  rw [mem_variableIdeal_pow_iff_order]
  apply nat_le_order
  intro d hd
  simp only [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]

section Derivations

variable {M : Type u} [AddCommGroup M] [Module (Series R) M] [Module R M]
  (D E : Derivation R (Series R) M)

/-- Native polynomial induction retains the values of EVERY original polynomial. -/
theorem derivation_coe_polynomial_ext
    (h : ∀ i : Fin 2, D (X i) = E (X i)) (p : MvPolynomial (Fin 2) R) :
    D (p : Series R) = E (p : Series R) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.coe_C]
    change D (algebraMap R (Series R) r) = E (algebraMap R (Series R) r)
    rw [Derivation.map_algebraMap, Derivation.map_algebraMap]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz,
      Derivation.leibniz, hp, h i]

/-- Actual Hausdorffness and native derivation filtration prove equality on ALL original series. -/
theorem derivation_ext_of_coordinate [IsHausdorff (variableIdeal R) M]
    (h : ∀ i : Fin 2, D (X i) = E (X i)) : D = E := by
  apply DFunLike.ext
  intro f
  apply (IsHausdorff.eq_iff_smodEq (I := variableIdeal R)).mpr
  intro n
  rw [SModEq.sub_mem]
  have hf := sub_truncTotal_mem_variableIdeal_pow (n + 1) f
  have hD := NodeGeometricCompletionDerivation.differential_mem_pow_smul
    (variableIdeal R) D n hf
  have hE := NodeGeometricCompletionDerivation.differential_mem_pow_smul
    (variableIdeal R) E n hf
  have hd := Submodule.sub_mem _ hD hE
  rw [map_sub, map_sub, derivation_coe_polynomial_ext D E h] at hd
  convert hd using 1; abel

end Derivations

end DeJongAlterations.Algebra.NodeFittingFormalDensity
