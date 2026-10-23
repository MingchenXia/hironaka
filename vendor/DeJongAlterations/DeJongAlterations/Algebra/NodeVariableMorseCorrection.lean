import DeJongAlterations.Algebra.NodeVariableMorseOrder
import DeJongAlterations.Algebra.NodeNonsplitCorrection

/-! # The actual variable-adic inverse-Hessian quadratic correction -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K] (Q : Quadratic K)

/-- The actual inverse-Hessian first correction retains the original variable-order bound. -/
theorem leftCorrection_mem_pow {k : ℕ} {H : Series K}
    (hH : H ∈ variableIdeal K ^ (k + 1)) : leftCorrection Q H ∈ variableIdeal K ^ k := by
  unfold leftCorrection
  exact (variableIdeal K ^ k).mul_mem_left _ ((variableIdeal K ^ k).sub_mem
    ((variableIdeal K ^ k).mul_mem_left _ (secondPart_mem_pow hH))
    ((variableIdeal K ^ k).mul_mem_left _ (firstPart_mem_pow hH)))

/-- The actual second inverse-Hessian correction has the same original bound. -/
theorem rightCorrection_mem_pow {k : ℕ} {H : Series K}
    (hH : H ∈ variableIdeal K ^ (k + 1)) : rightCorrection Q H ∈ variableIdeal K ^ k := by
  unfold rightCorrection
  exact (variableIdeal K ^ k).mul_mem_left _ ((variableIdeal K ^ k).sub_mem
    ((variableIdeal K ^ k).mul_mem_left _ (firstPart_mem_pow hH))
    ((variableIdeal K ^ k).mul_mem_left _ (secondPart_mem_pow hH)))

/-- Positive actual variable order forces the original constant coefficient to vanish. -/
theorem constantCoeff_zero_of_mem_pow {k : ℕ} (hk : 1 ≤ k) {H : Series K}
    (hH : H ∈ variableIdeal K ^ k) : constantCoeff H = 0 := by
  apply one_le_order_iff_constCoeff_eq_zero.mp
  exact le_trans (by exact_mod_cast hk) ((mem_variableIdeal_pow_iff_order k H).mp hH)

/-- The actual correcting coordinates have zero original constants. -/
theorem correctionCoordinates_hasSubst {k : ℕ} (hk : 2 ≤ k) {H : Series K}
    (hH : H ∈ variableIdeal K ^ (k + 1)) : HasSubst (NodeNonsplit.correctionCoordinates Q H) := by
  apply hasSubst_of_constantCoeff_zero
  have hp := constantCoeff_zero_of_mem_pow (by omega : 1 ≤ k) (leftCorrection_mem_pow Q hH)
  have hq := constantCoeff_zero_of_mem_pow (by omega : 1 ≤ k) (rightCorrection_mem_pow Q hH)
  intro i
  fin_cases i
  · simp [NodeNonsplit.correctionCoordinates, hp]
  · simp [NodeNonsplit.correctionCoordinates, hq]

/-- The actual correcting coordinate differences have their original higher variable order. -/
theorem correctionCoordinates_sub_mem {k : ℕ} {H : Series K}
    (hH : H ∈ variableIdeal K ^ (k + 1)) (i : Fin 2) :
    NodeNonsplit.correctionCoordinates Q H i - X i ∈ variableIdeal K ^ k := by
  fin_cases i
  · simpa [NodeNonsplit.correctionCoordinates] using (variableIdeal K ^ k).neg_mem (leftCorrection_mem_pow Q hH)
  · simpa [NodeNonsplit.correctionCoordinates] using (variableIdeal K ^ k).neg_mem (rightCorrection_mem_pow Q hH)

/-- The actual unipotent original substitution, constructed from the original higher-order error. -/
def correctionEquiv {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) : Series K ≃ₐ[K] Series K :=
  unipotentEquiv (NodeNonsplit.correctionCoordinates Q H) (correctionCoordinates_hasSubst Q hk hH)
    (fun i => Ideal.pow_le_pow_right hk (correctionCoordinates_sub_mem Q hH i))

@[simp]
theorem correctionEquiv_X_zero {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) :
    correctionEquiv Q hk H hH (X 0) = X 0 - leftCorrection Q H := by
  change substAlgHom (R := K) (correctionCoordinates_hasSubst Q hk hH) (X 0) = _
  rw [substAlgHom_X]
  simp [NodeNonsplit.correctionCoordinates]

@[simp]
theorem correctionEquiv_X_one {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) :
    correctionEquiv Q hk H hH (X 1) = X 1 - rightCorrection Q H := by
  change substAlgHom (R := K) (correctionCoordinates_hasSubst Q hk hH) (X 1) = _
  rw [substAlgHom_X]
  simp [NodeNonsplit.correctionCoordinates]

@[simp]
theorem correctionEquiv_C {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) (r : K) :
    correctionEquiv Q hk H hH (C r) = C r := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (correctionEquiv Q hk H hH).commutes r

/-- The actual quadratic remainder has doubled original correction order. -/
theorem quadraticError_mem_pow {k : ℕ} {H : Series K}
    (hH : H ∈ variableIdeal K ^ (k + 1)) :
    quadraticError Q H ∈ variableIdeal K ^ (2 * k) := by
  have hp := leftCorrection_mem_pow Q hH
  have hq := rightCorrection_mem_pow Q hH
  rw [show 2 * k = k + k by omega, pow_add]
  unfold quadraticError
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hp hp))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hp hq)))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hq hq))

/-- The actual higher-order residual is constructed using the actual inverse substitution. -/
def correctedError {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) : Series K :=
  (correctionEquiv Q hk H hH).symm (quadraticError Q H)

/-- The actual inverse preserves the full doubled original variable-error order. -/
theorem correctedError_mem_pow {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) :
    correctedError Q hk H hH ∈ variableIdeal K ^ (2 * k) :=
  unipotentEquiv_symm_mem_pow _ _ _ (2 * k) _ (quadraticError_mem_pow Q hH)

/-- The exact original quadratic equation is corrected over the same original field. -/
theorem correctionEquation {k : ℕ} (hk : 2 ≤ k) (H : Series K)
    (hH : H ∈ variableIdeal K ^ (k + 1)) :
    (correctionEquiv Q hk H hH).symm (Q.series - H) =
      Q.series - correctedError Q hk H hH := by
  have hmul : correctionEquiv Q hk H hH Q.series =
      Q.series - X 0 * firstPart H - X 1 * secondPart H + quadraticError Q H := by
    have he := (Q.map C).expansion (X 0) (X 1) (firstPart H) (secondPart H)
    rw [← leftCorrection_eq, ← rightCorrection_eq, ← quadraticError_eq] at he
    change (Q.map C).value (X 0 - leftCorrection Q H) (X 1 - rightCorrection Q H) =
      Q.series - X 0 * firstPart H - X 1 * secondPart H + quadraticError Q H at he
    rw [← he]
    simp only [Quadratic.series, Quadratic.value, Quadratic.map, map_add, map_mul, map_pow,
      correctionEquiv_C, correctionEquiv_X_zero, correctionEquiv_X_one]
  have hc : constantCoeff H = 0 := constantCoeff_zero_of_mem_pow (by omega) hH
  have he : Q.series - H = correctionEquiv Q hk H hH Q.series - quadraticError Q H := by
    rw [hmul]
    conv_lhs => rw [decomposition H, hc, map_zero, zero_add]
    ring
  rw [he, map_sub, AlgEquiv.symm_apply_apply]
  rfl

end DeJongAlterations.Algebra.NodeVariableMorse
