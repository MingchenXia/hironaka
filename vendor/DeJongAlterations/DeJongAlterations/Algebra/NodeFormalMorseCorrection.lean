import DeJongAlterations.Algebra.NodeFormalMorseDecomposition
import Mathlib.Tactic.Ring

/-!
# An actual bounded split-node Morse correction

The forward coordinates are literally `u - b` and `v - a`; the original
coefficient maps are fixed. The inverse is the actual native substitution
constructed by nilpotent coefficient reduction. Every ideal condition here is
coefficientwise, with no finite-generation or characteristic assumption.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

universe u
variable {R : Type u} [CommRing R]

/-- Deterministic decomposition commutes with the original coefficient ring map. -/
theorem firstPart_map {S : Type*} [CommRing S] (f : R →+* S) (H : Series R) :
    firstPart (MvPowerSeries.map f H) = MvPowerSeries.map f (firstPart H) := by
  ext d
  simp only [coeff_firstPart, coeff_map]

/-- The second deterministic part also commutes with actual coefficient reduction. -/
theorem secondPart_map {S : Type*} [CommRing S] (f : R →+* S) (H : Series R) :
    secondPart (MvPowerSeries.map f H) = MvPowerSeries.map f (secondPart H) := by
  ext d
  simp only [coeff_secondPart, coeff_map]
  split_ifs <;> simp

/-- Coefficientwise ideal membership gives zero under actual coefficient reduction. -/
theorem map_eq_zero_of_coeff_mem {σ : Type*} (J : Ideal R)
    (f : MvPowerSeries σ R) (hf : ∀ d, coeff d f ∈ J) :
    MvPowerSeries.map (Ideal.Quotient.mk J) f = 0 := by
  ext d
  rw [coeff_map, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf d)

/-- The literal correcting coordinate family. Its constants need not vanish. -/
def correctionCoordinates (H : Series R) (i : Fin 2) : Series R :=
  if i = 0 then X 0 - secondPart H else X 1 - firstPart H

/-- The required identity reduction is proved from the original error coefficients. -/
theorem correctionCoordinates_reduces (J : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : NilpotentPowerSeriesSubstitution.ReducesToVariables J (correctionCoordinates H) := by
  intro i
  have ha := map_eq_zero_of_coeff_mem J (firstPart H) (firstPart_coeff_mem J H hH)
  have hb := map_eq_zero_of_coeff_mem J (secondPart H) (secondPart_coeff_mem J H hH)
  fin_cases i <;> simp [correctionCoordinates, ha, hb]

/-- Nilpotence internally constructs the actual correcting algebra automorphism. -/
def correctionEquiv (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : Series R ≃ₐ[R] Series R :=
  NilpotentPowerSeriesSubstitution.equivOfReduction J hJ (correctionCoordinates_reduces J H hH)

/-- The actual native admissible substitution is the original forward algebra map. -/
theorem correctionEquiv_toAlgHom (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    (correctionEquiv J hJ H hH).toAlgHom =
      MvPowerSeries.substAlgHom (R := R) (S := R)
        (NilpotentPowerSeriesSubstitution.hasSubst J hJ
          (correctionCoordinates_reduces J H hH)) := rfl

@[simp]
theorem correctionEquiv_X_zero (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    correctionEquiv J hJ H hH (X 0) = X 0 - secondPart H := by
  simp [correctionEquiv, correctionCoordinates]

@[simp]
theorem correctionEquiv_X_one (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    correctionEquiv J hJ H hH (X 1) = X 1 - firstPart H := by
  simp [correctionEquiv, correctionCoordinates]

@[simp]
theorem correctionEquiv_C (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (r : R) :
    correctionEquiv J hJ H hH (C r) = C r := by
  simp [correctionEquiv]

@[simp]
theorem correctionEquiv_symm_C (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (r : R) :
    (correctionEquiv J hJ H hH).symm (C r) = C r := by
  apply (correctionEquiv J hJ H hH).injective
  simp

/-- The exact forward substitution reduces to the identity on every series. -/
theorem correctionEquiv_reduction (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk J) (correctionEquiv J hJ H hH f) =
      MvPowerSeries.map (Ideal.Quotient.mk J) f :=
  NilpotentPowerSeriesSubstitution.map_substAlgHom J
    (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces J H hH))
    (correctionCoordinates_reduces J H hH) f

/-- The actual inverse fixes coefficient reduction on every original formal series. -/
theorem correctionEquiv_symm_reduction (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk J) ((correctionEquiv J hJ H hH).symm f) =
      MvPowerSeries.map (Ideal.Quotient.mk J) f := by
  have he := NilpotentPowerSeriesSubstitution.map_substAlgHom J
    (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces J H hH))
    (correctionCoordinates_reduces J H hH)
    ((correctionEquiv J hJ H hH).symm f)
  change MvPowerSeries.map (Ideal.Quotient.mk J)
      (correctionEquiv J hJ H hH ((correctionEquiv J hJ H hH).symm f)) = _ at he
  rw [AlgEquiv.apply_symm_apply] at he
  exact he.symm

/-- The actual inverse preserves every coefficient ideal, including squared error ideals. -/
theorem correctionEquiv_symm_coeff_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (K : Ideal R) (f : Series R)
    (hf : ∀ d, coeff d f ∈ K) :
    ∀ d, coeff d ((correctionEquiv J hJ H hH).symm f) ∈ K := by
  change ∀ d, coeff d
    ((NilpotentPowerSeriesSubstitution.substAlgEquiv J (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces J H hH))
      hJ (correctionCoordinates_reduces J H hH)).symm.toAlgHom f) ∈ K
  rw [NilpotentPowerSeriesSubstitution.symm_toAlgHom_eq_substAlgHom]
  exact NilpotentPowerSeriesSubstitution.subst_coeff_mem _ K f hf

/-- The exact new parameter, in the original formal series ring over the original coefficients. -/
def correctedError (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : Series R :=
  C (constantCoeff H) + (correctionEquiv J hJ H hH).symm (firstPart H * secondPart H)

/-- The original equation is transformed by the actual inverse coordinate automorphism. -/
theorem correctionEquation (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    (correctionEquiv J hJ H hH).symm (X 0 * X 1 - H) =
      X 0 * X 1 - correctedError J hJ H hH := by
  have hmul : correctionEquiv J hJ H hH (X 0 * X 1) =
      X 0 * X 1 - X 0 * firstPart H - X 1 * secondPart H + firstPart H * secondPart H := by
    rw [map_mul, correctionEquiv_X_zero, correctionEquiv_X_one]
    ring
  have he : X 0 * X 1 - H = correctionEquiv J hJ H hH (X 0 * X 1) -
      (C (constantCoeff H) + firstPart H * secondPart H) := by
    rw [hmul]
    conv_lhs => rw [decomposition H]
    ring
  rw [he, map_sub, AlgEquiv.symm_apply_apply, map_add, correctionEquiv_symm_C]
  rfl

/-- Every coefficient of the new variable-dependent error is in the square of the original ideal. -/
theorem correctedError_sub_constant_coeff_mem (J : Ideal R) (hJ : IsNilpotent J)
    (H : Series R) (hH : ∀ d, coeff d H ∈ J) :
    ∀ d, coeff d (correctedError J hJ H hH - C (constantCoeff H)) ∈ J ^ 2 := by
  unfold correctedError
  rw [add_sub_cancel_left]
  apply correctionEquiv_symm_coeff_mem J hJ H hH
  simpa only [pow_two] using
    mul_coeff_mem J J (firstPart H) (secondPart H)
      (firstPart_coeff_mem J H hH) (secondPart_coeff_mem J H hH)

/-- The actual new constant. -/
def correctedConstant (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : R := constantCoeff (correctedError J hJ H hH)

/-- The residual error with its actual constant removed. -/
def correctedResidual (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : Series R :=
  correctedError J hJ H hH - C (correctedConstant J hJ H hH)

@[simp]
theorem correctedResidual_constantCoeff (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : constantCoeff (correctedResidual J hJ H hH) = 0 := by
  simp [correctedResidual, correctedConstant]

/-- The exact constant change has the squared error order. -/
theorem correctedConstant_sub_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) :
    correctedConstant J hJ H hH - constantCoeff H ∈ J ^ 2 := by
  simpa only [map_sub, coeff_zero_eq_constantCoeff, constantCoeff_C, correctedConstant] using
    correctedError_sub_constant_coeff_mem J hJ H hH 0

/-- Removing the actual new constant preserves the squared coefficient order. -/
theorem correctedResidual_coeff_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : ∀ d, coeff d (correctedResidual J hJ H hH) ∈ J ^ 2 := by
  intro d
  have he := correctedError_sub_constant_coeff_mem J hJ H hH d
  have hc := correctedConstant_sub_mem J hJ H hH
  have hdiff : coeff d (C (correctedConstant J hJ H hH) - C (constantCoeff H)) ∈ J ^ 2 := by
    rw [← map_sub, coeff_C]
    split_ifs
    · exact hc
    · exact Ideal.zero_mem _
  have hidentity : correctedResidual J hJ H hH =
      (correctedError J hJ H hH - C (constantCoeff H)) -
        (C (correctedConstant J hJ H hH) - C (constantCoeff H)) := by
    unfold correctedResidual
    abel
  rw [hidentity, map_sub]
  exact Ideal.sub_mem _ he hdiff

/-- The internally computed new constant remains in the original error ideal. -/
theorem correctedConstant_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : correctedConstant J hJ H hH ∈ J := by
  have hc := Ideal.pow_le_self (I := J) (by decide : (2 : ℕ) ≠ 0)
    (correctedConstant_sub_mem J hJ H hH)
  have hh := J.add_mem hc (constantCoeff_mem J H hH)
  simpa only [sub_add_cancel] using hh

/-- An arbitrary original scalar term is preserved and the full new residual is explicit. -/
theorem correctionEquation_with_constant (J : Ideal R) (hJ : IsNilpotent J)
    (h : R) (H : Series R) (hH : ∀ d, coeff d H ∈ J) :
    (correctionEquiv J hJ H hH).symm (X 0 * X 1 - C h - H) =
      X 0 * X 1 - C (h + correctedConstant J hJ H hH) - correctedResidual J hJ H hH := by
  have he : X 0 * X 1 - C h - H = (X 0 * X 1 - H) - C h := by ring
  rw [he, map_sub, correctionEquation, correctionEquiv_symm_C]
  unfold correctedResidual
  rw [map_add]
  ring

end DeJongAlterations.Algebra.NodeFormalMorse
