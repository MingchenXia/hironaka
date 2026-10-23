import DeJongAlterations.Algebra.NodeNonsplitQuadratic
import DeJongAlterations.Algebra.NodeFormalMorseNaturality

/-! # Actual nilpotent same-ring correction for the original nonsplit quadratic -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeNonsplit

open MvPowerSeries NodeFormalMorse

universe u
variable {R : Type u} [CommRing R] (Q : Quadratic R)

/-- Literal first coordinate correction with the original inverse discriminant. -/
def leftCorrection (H : Series R) : Series R :=
  C Q.invDiscriminant * (C Q.a1 * secondPart H - C (2 * Q.a2) * firstPart H)

/-- Literal second coordinate correction; no division by two occurs. -/
def rightCorrection (H : Series R) : Series R :=
  C Q.invDiscriminant * (C Q.a1 * firstPart H - C (2 * Q.a0) * secondPart H)

theorem leftCorrection_eq (H : Series R) :
    leftCorrection Q H = (Q.map C).left (firstPart H) (secondPart H) := by
  simp [leftCorrection, Quadratic.left, Quadratic.map, map_mul, map_ofNat]

theorem rightCorrection_eq (H : Series R) :
    rightCorrection Q H = (Q.map C).right (firstPart H) (secondPart H) := by
  simp [rightCorrection, Quadratic.right, Quadratic.map, map_mul, map_ofNat]

theorem leftCorrection_coeff_mem (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (d) : coeff d (leftCorrection Q H) ∈ J := by
  simp only [leftCorrection, coeff_C_mul, map_sub]
  exact J.mul_mem_left _ (J.sub_mem
    (J.mul_mem_left _ (secondPart_coeff_mem J H hH d))
    (J.mul_mem_left _ (firstPart_coeff_mem J H hH d)))

theorem rightCorrection_coeff_mem (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (d) : coeff d (rightCorrection Q H) ∈ J := by
  simp only [rightCorrection, coeff_C_mul, map_sub]
  exact J.mul_mem_left _ (J.sub_mem
    (J.mul_mem_left _ (firstPart_coeff_mem J H hH d))
    (J.mul_mem_left _ (secondPart_coeff_mem J H hH d)))

/-- The literal quadratic remainder in the two actual coordinate corrections. -/
def quadraticError (H : Series R) : Series R :=
  C Q.a0 * (leftCorrection Q H * leftCorrection Q H) +
    C Q.a1 * (leftCorrection Q H * rightCorrection Q H) +
    C Q.a2 * (rightCorrection Q H * rightCorrection Q H)

theorem quadraticError_eq (H : Series R) :
    quadraticError Q H = (Q.map C).value (leftCorrection Q H) (rightCorrection Q H) := by
  unfold quadraticError Quadratic.value Quadratic.map
  ring

theorem quadraticError_coeff_mem (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (d) : coeff d (quadraticError Q H) ∈ J ^ 2 := by
  have hp := leftCorrection_coeff_mem Q J H hH
  have hq := rightCorrection_coeff_mem Q J H hH
  have hpp := mul_coeff_mem J J _ _ hp hp d
  have hpq := mul_coeff_mem J J _ _ hp hq d
  have hqq := mul_coeff_mem J J _ _ hq hq d
  rw [← pow_two] at hpp hpq hqq
  simp only [quadraticError, map_add, coeff_C_mul]
  exact (J ^ 2).add_mem ((J ^ 2).add_mem ((J ^ 2).mul_mem_left _ hpp)
    ((J ^ 2).mul_mem_left _ hpq)) ((J ^ 2).mul_mem_left _ hqq)

/-- The literal correcting coordinate family. Its constants need not vanish. -/
def correctionCoordinates (H : Series R) (i : Fin 2) : Series R :=
  if i = 0 then X 0 - leftCorrection Q H else X 1 - rightCorrection Q H

/-- The required identity reduction is proved from the original error coefficients. -/
theorem correctionCoordinates_reduces (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : NilpotentPowerSeriesSubstitution.ReducesToVariables J (correctionCoordinates Q H) := by
  intro i
  have ha := map_eq_zero_of_coeff_mem J (leftCorrection Q H) (leftCorrection_coeff_mem Q J H hH)
  have hb := map_eq_zero_of_coeff_mem J (rightCorrection Q H) (rightCorrection_coeff_mem Q J H hH)
  fin_cases i <;> simp [correctionCoordinates, ha, hb]

/-- Nilpotence internally constructs the actual correcting algebra automorphism. -/
def correctionEquiv (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : Series R ≃ₐ[R] Series R :=
  NilpotentPowerSeriesSubstitution.equivOfReduction J hJ (correctionCoordinates_reduces Q J H hH)

/-- The actual native admissible substitution is the original forward algebra map. -/
theorem correctionEquiv_toAlgHom (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    (correctionEquiv Q J hJ H hH).toAlgHom =
      MvPowerSeries.substAlgHom (R := R) (S := R)
        (NilpotentPowerSeriesSubstitution.hasSubst J hJ
          (correctionCoordinates_reduces Q J H hH)) := rfl

@[simp]
theorem correctionEquiv_X_zero (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    correctionEquiv Q J hJ H hH (X 0) = X 0 - leftCorrection Q H := by
  simp [correctionEquiv, correctionCoordinates]

@[simp]
theorem correctionEquiv_X_one (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    correctionEquiv Q J hJ H hH (X 1) = X 1 - rightCorrection Q H := by
  simp [correctionEquiv, correctionCoordinates]

@[simp]
theorem correctionEquiv_C (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (r : R) :
    correctionEquiv Q J hJ H hH (C r) = C r := by
  simp [correctionEquiv]

@[simp]
theorem correctionEquiv_symm_C (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (r : R) :
    (correctionEquiv Q J hJ H hH).symm (C r) = C r := by
  apply (correctionEquiv Q J hJ H hH).injective
  simp

/-- The exact forward substitution reduces to the identity on every series. -/
theorem correctionEquiv_reduction (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk J) (correctionEquiv Q J hJ H hH f) =
      MvPowerSeries.map (Ideal.Quotient.mk J) f :=
  NilpotentPowerSeriesSubstitution.map_substAlgHom J
    (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces Q J H hH))
    (correctionCoordinates_reduces Q J H hH) f

/-- The actual inverse fixes coefficient reduction on every original formal series. -/
theorem correctionEquiv_symm_reduction (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk J) ((correctionEquiv Q J hJ H hH).symm f) =
      MvPowerSeries.map (Ideal.Quotient.mk J) f := by
  have he := NilpotentPowerSeriesSubstitution.map_substAlgHom J
    (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces Q J H hH))
    (correctionCoordinates_reduces Q J H hH)
    ((correctionEquiv Q J hJ H hH).symm f)
  change MvPowerSeries.map (Ideal.Quotient.mk J)
      (correctionEquiv Q J hJ H hH ((correctionEquiv Q J hJ H hH).symm f)) = _ at he
  rw [AlgEquiv.apply_symm_apply] at he
  exact he.symm

/-- The actual inverse preserves every coefficient ideal, including squared error ideals. -/
theorem correctionEquiv_symm_coeff_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (K : Ideal R) (f : Series R)
    (hf : ∀ d, coeff d f ∈ K) :
    ∀ d, coeff d ((correctionEquiv Q J hJ H hH).symm f) ∈ K := by
  change ∀ d, coeff d
    ((NilpotentPowerSeriesSubstitution.substAlgEquiv J (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces Q J H hH))
      hJ (correctionCoordinates_reduces Q J H hH)).symm.toAlgHom f) ∈ K
  rw [NilpotentPowerSeriesSubstitution.symm_toAlgHom_eq_substAlgHom]
  exact NilpotentPowerSeriesSubstitution.subst_coeff_mem _ K f hf

/-- The exact new parameter, in the original formal series ring over the original coefficients. -/
def correctedError (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : Series R :=
  C (constantCoeff H) + (correctionEquiv Q J hJ H hH).symm (quadraticError Q H)

/-- The original equation is transformed by the actual inverse coordinate automorphism. -/
theorem correctionEquation (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    (correctionEquiv Q J hJ H hH).symm (Q.series - H) =
      Q.series - correctedError Q J hJ H hH := by
  have hmul : correctionEquiv Q J hJ H hH Q.series =
      Q.series - X 0 * firstPart H - X 1 * secondPart H + quadraticError Q H := by
    have he := (Q.map C).expansion (X 0) (X 1) (firstPart H) (secondPart H)
    rw [← leftCorrection_eq, ← rightCorrection_eq, ← quadraticError_eq] at he
    change (Q.map C).value (X 0 - leftCorrection Q H) (X 1 - rightCorrection Q H) =
      Q.series - X 0 * firstPart H - X 1 * secondPart H + quadraticError Q H at he
    rw [← he]
    simp only [Quadratic.series, Quadratic.value, Quadratic.map, map_add, map_mul, map_pow,
      correctionEquiv_C, correctionEquiv_X_zero, correctionEquiv_X_one]
  have he : Q.series - H = correctionEquiv Q J hJ H hH (Q.series) -
      (C (constantCoeff H) + quadraticError Q H) := by
    rw [hmul]
    conv_lhs => rw [decomposition H]
    ring
  rw [he, map_sub, AlgEquiv.symm_apply_apply, map_add, correctionEquiv_symm_C Q]
  rfl

/-- Every coefficient of the new variable-dependent error is in the square of the original ideal. -/
theorem correctedError_sub_constant_coeff_mem (J : Ideal R) (hJ : IsNilpotent J)
    (H : Series R) (hH : ∀ d, coeff d H ∈ J) :
    ∀ d, coeff d (correctedError Q J hJ H hH - C (constantCoeff H)) ∈ J ^ 2 := by
  unfold correctedError
  rw [add_sub_cancel_left]
  apply correctionEquiv_symm_coeff_mem Q J hJ H hH
  exact quadraticError_coeff_mem Q J H hH

/-- The actual new constant. -/
def correctedConstant (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : R := constantCoeff (correctedError Q J hJ H hH)

/-- The residual error with its actual constant removed. -/
def correctedResidual (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : Series R :=
  correctedError Q J hJ H hH - C (correctedConstant Q J hJ H hH)

@[simp]
theorem correctedResidual_constantCoeff (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : constantCoeff (correctedResidual Q J hJ H hH) = 0 := by
  simp [correctedResidual, correctedConstant]

/-- The exact constant change has the squared error order. -/
theorem correctedConstant_sub_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    correctedConstant Q J hJ H hH - constantCoeff H ∈ J ^ 2 := by
  simpa only [map_sub, coeff_zero_eq_constantCoeff, constantCoeff_C, correctedConstant] using
    correctedError_sub_constant_coeff_mem Q J hJ H hH 0

/-- Removing the actual new constant preserves the squared coefficient order. -/
theorem correctedResidual_coeff_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : ∀ d, coeff d (correctedResidual Q J hJ H hH) ∈ J ^ 2 := by
  intro d
  have he := correctedError_sub_constant_coeff_mem Q J hJ H hH d
  have hc := correctedConstant_sub_mem Q J hJ H hH
  have hdiff : coeff d (C (correctedConstant Q J hJ H hH) - C (constantCoeff H)) ∈ J ^ 2 := by
    rw [← map_sub, coeff_C]
    split_ifs
    · exact hc
    · exact Ideal.zero_mem _
  have hidentity : correctedResidual Q J hJ H hH =
      (correctedError Q J hJ H hH - C (constantCoeff H)) -
        (C (correctedConstant Q J hJ H hH) - C (constantCoeff H)) := by
    unfold correctedResidual
    abel
  rw [hidentity, map_sub]
  exact Ideal.sub_mem _ he hdiff

/-- The internally computed new constant remains in the original error ideal. -/
theorem correctedConstant_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : correctedConstant Q J hJ H hH ∈ J := by
  have hc := Ideal.pow_le_self (I := J) (by decide : (2 : ℕ) ≠ 0)
    (correctedConstant_sub_mem Q J hJ H hH)
  have hh := J.add_mem hc (constantCoeff_mem J H hH)
  simpa only [sub_add_cancel] using hh

/-- An arbitrary original scalar term is preserved and the full new residual is explicit. -/
theorem correctionEquation_with_constant (J : Ideal R) (hJ : IsNilpotent J)
    (h : R) (H : Series R) (hH : ∀ d, coeff d H ∈ J) :
    (correctionEquiv Q J hJ H hH).symm (Q.series - C h - H) =
      Q.series - C (h + correctedConstant Q J hJ H hH) - correctedResidual Q J hJ H hH := by
  have he : Q.series - C h - H = (Q.series - H) - C h := by ring
  rw [he, map_sub, correctionEquation Q, correctionEquiv_symm_C Q]
  unfold correctedResidual
  rw [map_add]
  ring

end DeJongAlterations.Algebra.NodeNonsplit
