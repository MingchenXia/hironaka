import DeJongAlterations.Algebra.NodeVariableMorseCorrection

/-! # The original variable-adic quadratic contraction and its actual approximations -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

theorem firstPart_sub (f g : Series K) : firstPart (f - g) = firstPart f - firstPart g := by
  ext d
  simp

theorem secondPart_sub (f g : Series K) : secondPart (f - g) = secondPart f - secondPart g := by
  ext d
  by_cases hd : d 0 = 0 <;> simp [coeff_secondPart, hd]

theorem leftCorrection_sub (Q : Quadratic K) (f g : Series K) :
    leftCorrection Q (f - g) = leftCorrection Q f - leftCorrection Q g := by
  unfold leftCorrection
  rw [firstPart_sub, secondPart_sub]
  ring

theorem rightCorrection_sub (Q : Quadratic K) (f g : Series K) :
    rightCorrection Q (f - g) = rightCorrection Q f - rightCorrection Q g := by
  unfold rightCorrection
  rw [firstPart_sub, secondPart_sub]
  ring

/-- The actual quadratic correction raises differences in the original variable filtration. -/
theorem quadraticError_sub_mem_pow (Q : Quadratic K) {U V : Series K} {n : ℕ}
    (hU : U ∈ variableIdeal K ^ 3) (hV : V ∈ variableIdeal K ^ 3)
    (hUV : U - V ∈ variableIdeal K ^ (n + 3)) :
    quadraticError Q U - quadraticError Q V ∈ variableIdeal K ^ (n + 4) := by
  have hpU := leftCorrection_mem_pow Q hU
  have hpV := leftCorrection_mem_pow Q hV
  have hqU := rightCorrection_mem_pow Q hU
  have hqV := rightCorrection_mem_pow Q hV
  have hp : leftCorrection Q U - leftCorrection Q V ∈ variableIdeal K ^ (n + 2) := by
    rw [← leftCorrection_sub]
    exact leftCorrection_mem_pow Q hUV
  have hq : rightCorrection Q U - rightCorrection Q V ∈ variableIdeal K ^ (n + 2) := by
    rw [← rightCorrection_sub]
    exact rightCorrection_mem_pow Q hUV
  have he : quadraticError Q U - quadraticError Q V =
      C Q.a0 * ((leftCorrection Q U - leftCorrection Q V) * leftCorrection Q U +
        (leftCorrection Q U - leftCorrection Q V) * leftCorrection Q V) +
      C Q.a1 * ((leftCorrection Q U - leftCorrection Q V) * rightCorrection Q U +
        (rightCorrection Q U - rightCorrection Q V) * leftCorrection Q V) +
      C Q.a2 * ((rightCorrection Q U - rightCorrection Q V) * rightCorrection Q U +
        (rightCorrection Q U - rightCorrection Q V) * rightCorrection Q V) := by
    unfold quadraticError
    ring
  rw [he, show n + 4 = (n + 2) + 2 by omega, pow_add]
  apply Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
      (Ideal.mul_mem_mul hp hpU) (Ideal.mul_mem_mul hp hpV))
  · exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
      (Ideal.mul_mem_mul hp hqU) (Ideal.mul_mem_mul hq hpV))
  · exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
      (Ideal.mul_mem_mul hq hqU) (Ideal.mul_mem_mul hq hqV))

/-- The actual deterministic original quadratic fixed-point approximations. -/
def approximation (Q : Quadratic K) (H : Series K) : ℕ → Series K
  | 0 => H
  | n + 1 => H + quadraticError Q (approximation Q H n)

/-- All original approximations stay in the original cubic variable ideal. -/
theorem approximation_mem_pow (Q : Quadratic K) (H : Series K)
    (hH : H ∈ variableIdeal K ^ 3) (n : ℕ) :
    approximation Q H n ∈ variableIdeal K ^ 3 := by
  induction n with
  | zero => exact hH
  | succ n ih =>
    exact Ideal.add_mem _ hH (Ideal.pow_le_pow_right (by decide : 3 ≤ 4)
      (quadraticError_mem_pow Q ih))

/-- The original successive differences gain one genuine variable order at every step. -/
theorem approximation_succ_sub (Q : Quadratic K) (H : Series K)
    (hH : H ∈ variableIdeal K ^ 3) (n : ℕ) :
    approximation Q H (n + 1) - approximation Q H n ∈ variableIdeal K ^ (n + 4) := by
  induction n with
  | zero =>
    simpa only [approximation, add_sub_cancel_left] using quadraticError_mem_pow Q hH
  | succ n ih =>
    have hd := quadraticError_sub_mem_pow Q (n := n + 1)
      (approximation_mem_pow Q H hH (n + 1)) (approximation_mem_pow Q H hH n) ih
    simpa only [approximation, add_sub_add_left_eq_sub] using hd

/-- The actual original approximation sequence is Cauchy in the actual variable ideal. -/
theorem approximation_sub_mem (Q : Quadratic K) (H : Series K)
    (hH : H ∈ variableIdeal K ^ 3) {m n : ℕ} (hmn : m ≤ n) :
    approximation Q H n - approximation Q H m ∈ variableIdeal K ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have he : approximation Q H (n + 1) - approximation Q H m =
        (approximation Q H n - approximation Q H m) +
        (approximation Q H (n + 1) - approximation Q H n) := by abel
    rw [he]
    exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right (by omega : m ≤ n + 4)
      (approximation_succ_sub Q H hH n))

/-- Native completeness constructs an actual limit in the original series ring. -/
theorem exists_approximation_limit (Q : Quadratic K) (H : Series K)
    (hH : H ∈ variableIdeal K ^ 3) :
    ∃ L : Series K, ∀ n : ℕ, approximation Q H n - L ∈ variableIdeal K ^ n := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete (variableIdeal K) (Series K))
    (f := approximation Q H) fun {m n} hmn => by
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.neg_mem_iff, neg_sub]
      exact approximation_sub_mem Q H hH hmn
  refine ⟨L, fun n => ?_⟩
  have hn := hL n
  rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at hn

end DeJongAlterations.Algebra.NodeVariableMorse
