import DeJongAlterations.Algebra.NodeVariableMorseInverse

/-! # Actual invertible linear substitutions of the original formal series -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- The actual original two linear coordinate forms. -/
def linearCoordinates (a b c d : K) : Fin 2 → Series K :=
  ![C a * X 0 + C b * X 1, C c * X 0 + C d * X 1]

theorem linearCoordinates_hasSubst (a b c d : K) : HasSubst (linearCoordinates a b c d) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [linearCoordinates]

/-- The native actual linear substitution, defined on every original series. -/
def linearSubstitution (a b c d : K) : Series K →ₐ[K] Series K :=
  substAlgHom (linearCoordinates_hasSubst a b c d)

@[simp]
theorem linearSubstitution_X (a b c d : K) (i : Fin 2) :
    linearSubstitution a b c d (X i) = linearCoordinates a b c d i :=
  substAlgHom_X _ _

@[simp]
theorem linearSubstitution_C (a b c d r : K) :
    linearSubstitution a b c d (C r) = C r := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (linearSubstitution a b c d).commutes r

/-- The native substitution composition theorem gives a whole-series inverse from actual coordinates. -/
theorem substitution_leftInverse {a b : Fin 2 → Series K} (ha : HasSubst a) (hb : HasSubst b)
    (h : ∀ i, substAlgHom hb (a i) = X i) :
    Function.LeftInverse (substAlgHom hb) (substAlgHom ha) := by
  intro f
  rw [substAlgHom_comp_substAlgHom_apply, substAlgHom_apply]
  change subst (fun i => substAlgHom hb (a i)) f = f
  rw [funext h, subst_self]
  rfl

/-- Both original linear coordinate substitutions compose to the original variables. -/
theorem linearSubstitution_inverse_coordinates (a b c d : K) (hD : a * d - b * c ≠ 0)
    (i : Fin 2) :
    linearSubstitution ((a * d - b * c)⁻¹ * d) (-(a * d - b * c)⁻¹ * b)
      (-(a * d - b * c)⁻¹ * c) ((a * d - b * c)⁻¹ * a)
      (linearCoordinates a b c d i) = X i := by
  have hInv : (C ((a * d - b * c)⁻¹) : Series K) * C (a * d - b * c) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hD, map_one]
  fin_cases i
  · calc
      _ = (C ((a * d - b * c)⁻¹) * C (a * d - b * c)) * (X 0 : Series K) := by
        simp [linearCoordinates]
        ring
      _ = X 0 := by rw [hInv, one_mul]
  · calc
      _ = (C ((a * d - b * c)⁻¹) * C (a * d - b * c)) * (X 1 : Series K) := by
        simp [linearCoordinates]
        ring
      _ = X 1 := by rw [hInv, one_mul]

/-- The reverse original coordinate composition is also exactly the original variables. -/
theorem linearSubstitution_coordinates_inverse (a b c d : K) (hD : a * d - b * c ≠ 0)
    (i : Fin 2) :
    linearSubstitution a b c d
      (linearCoordinates ((a * d - b * c)⁻¹ * d) (-(a * d - b * c)⁻¹ * b)
        (-(a * d - b * c)⁻¹ * c) ((a * d - b * c)⁻¹ * a) i) = X i := by
  have hInv : (C ((a * d - b * c)⁻¹) : Series K) * C (a * d - b * c) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hD, map_one]
  fin_cases i
  · calc
      _ = (C ((a * d - b * c)⁻¹) * C (a * d - b * c)) * (X 0 : Series K) := by
        simp [linearCoordinates]
        ring
      _ = X 0 := by rw [hInv, one_mul]
  · calc
      _ = (C ((a * d - b * c)⁻¹) * C (a * d - b * c)) * (X 1 : Series K) := by
        simp [linearCoordinates]
        ring
      _ = X 1 := by rw [hInv, one_mul]

/-- The actual invertible linear substitution equivalence with its actual adjugate inverse. -/
def linearEquiv (a b c d : K) (hD : a * d - b * c ≠ 0) : Series K ≃ₐ[K] Series K :=
  AlgEquiv.ofAlgHom (linearSubstitution a b c d)
    (linearSubstitution ((a * d - b * c)⁻¹ * d) (-(a * d - b * c)⁻¹ * b)
      (-(a * d - b * c)⁻¹ * c) ((a * d - b * c)⁻¹ * a))
    (by
      ext1 f
      exact substitution_leftInverse
        (linearCoordinates_hasSubst ((a * d - b * c)⁻¹ * d) (-(a * d - b * c)⁻¹ * b)
          (-(a * d - b * c)⁻¹ * c) ((a * d - b * c)⁻¹ * a))
        (linearCoordinates_hasSubst a b c d) (linearSubstitution_coordinates_inverse a b c d hD) f)
    (by
      ext1 f
      exact substitution_leftInverse (linearCoordinates_hasSubst a b c d)
        (linearCoordinates_hasSubst ((a * d - b * c)⁻¹ * d) (-(a * d - b * c)⁻¹ * b)
          (-(a * d - b * c)⁻¹ * c) ((a * d - b * c)⁻¹ * a))
        (linearSubstitution_inverse_coordinates a b c d hD) f)

@[simp]
theorem linearEquiv_apply (a b c d : K) (hD : a * d - b * c ≠ 0) (f : Series K) :
    linearEquiv a b c d hD f = linearSubstitution a b c d f := rfl

@[simp]
theorem linearEquiv_coefficient (a b c d : K) (hD : a * d - b * c ≠ 0) (r : K) :
    linearEquiv a b c d hD (C r) = C r := linearSubstitution_C _ _ _ _ _

end DeJongAlterations.Algebra.NodeVariableMorse
