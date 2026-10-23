import DeJongAlterations.Algebra.NodeVariableMorseJacobian

/-!
# The original equation and its actual jet under arbitrary field coefficient extension

The extension is the literal native coefficient map of formal series.
Ordinary/completed tensor comparison and original geometric coherent
Fitting-ideal descent are separate.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {K : Type u} {L : Type v} [Field K] [Field L] (ρ : K →+* L)

@[simp]
theorem quadraticCoefficient0_map (f : Series K) :
    quadraticCoefficient0 (MvPowerSeries.map ρ f) = ρ (quadraticCoefficient0 f) := by
  simp [quadraticCoefficient0]

@[simp]
theorem quadraticCoefficient1_map (f : Series K) :
    quadraticCoefficient1 (MvPowerSeries.map ρ f) = ρ (quadraticCoefficient1 f) := by
  simp [quadraticCoefficient1]

@[simp]
theorem quadraticCoefficient2_map (f : Series K) :
    quadraticCoefficient2 (MvPowerSeries.map ρ f) = ρ (quadraticCoefficient2 f) := by
  simp [quadraticCoefficient2]

/-- The original actual quadratic jet is transported by the actual coefficient map. -/
theorem quadraticJet_map (f : Series K) :
    MvPowerSeries.map ρ (quadraticJet f) = quadraticJet (MvPowerSeries.map ρ f) := by
  simp [quadraticJet]

/-- The new actual discriminant is exactly the image of the original actual discriminant. -/
theorem jetDiscriminant_map (f : Series K) :
    jetDiscriminant (MvPowerSeries.map ρ f) = ρ (jetDiscriminant f) := by
  simp [jetDiscriminant, map_ofNat]

/-- Every actual field map preserves the original actual jet nondegeneracy. -/
theorem jetDiscriminant_map_ne_zero (f : Series K) (hΔ : jetDiscriminant f ≠ 0) :
    jetDiscriminant (MvPowerSeries.map ρ f) ≠ 0 := by
  rw [jetDiscriminant_map]
  intro hz
  apply hΔ
  apply RingHom.injective ρ
  simpa only [map_zero] using hz

/-- The original actual vanishing constant persists under every actual field coefficient map. -/
theorem map_constantCoeff_zero (f : Series K) (hc : constantCoeff f = 0) :
    constantCoeff (MvPowerSeries.map ρ f) = 0 := by
  rw [constantCoeff_map, hc, map_zero]

/-- Each original actual vanishing linear coefficient persists. -/
theorem map_linearCoeff_zero (f : Series K) (i : Fin 2)
    (hi : coeff (Finsupp.single i 1) f = 0) :
    coeff (Finsupp.single i 1) (MvPowerSeries.map ρ f) = 0 := by
  rw [coeff_map, hi, map_zero]

/-- The actual normal-form automorphism for the same original coefficient-extended equation. -/
def fieldExtensionNormalFormEquiv (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) : Series L ≃ₐ[L] Series L :=
  equationNormalFormEquiv (MvPowerSeries.map ρ f)
    (map_constantCoeff_zero ρ f hc) (map_linearCoeff_zero ρ f 0 h0)
    (map_linearCoeff_zero ρ f 1 h1) (jetDiscriminant_map_ne_zero ρ f hΔ)

/-- Its actual output is precisely the original quadratic jet's actual coefficient extension. -/
theorem fieldExtensionNormalFormEquiv_equation (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    fieldExtensionNormalFormEquiv ρ f hc h0 h1 hΔ (MvPowerSeries.map ρ f) =
      MvPowerSeries.map ρ (quadraticJet f) := by
  rw [quadraticJet_map]
  exact equationNormalFormEquiv_equation _ _ _ _ _

/-- Every actual original coefficient is fixed through the actual original field map. -/
@[simp]
theorem fieldExtensionNormalFormEquiv_coefficient (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) (a : K) :
    fieldExtensionNormalFormEquiv ρ f hc h0 h1 hΔ (C (ρ a)) = C (ρ a) := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (fieldExtensionNormalFormEquiv ρ f hc h0 h1 hΔ).commutes (ρ a)

/-- The original formal Jacobian theorem persists under every actual field coefficient extension. -/
theorem fieldExtensionJacobianIdeal_eq (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    originalJacobianIdeal (MvPowerSeries.map ρ f) = variableIdeal L :=
  originalJacobianIdeal_eq_variableIdeal _ (map_constantCoeff_zero ρ f hc)
    (map_linearCoeff_zero ρ f 0 h0) (map_linearCoeff_zero ρ f 1 h1)
    (jetDiscriminant_map_ne_zero ρ f hΔ)

/-- The literal extended original hypersurface derivative quotient is the actual extension field. -/
def fieldExtensionJacobianQuotientEquiv (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    (Equation (MvPowerSeries.map ρ f) ⧸ equationDerivativeIdeal (MvPowerSeries.map ρ f)) ≃ₐ[L] L :=
  equationJacobianQuotientEquiv _ (map_constantCoeff_zero ρ f hc)
    (map_linearCoeff_zero ρ f 0 h0) (map_linearCoeff_zero ρ f 1 h1)
    (jetDiscriminant_map_ne_zero ρ f hΔ)

/-- The original actual coefficient triangle remains exact in this actual quotient. -/
@[simp]
theorem fieldExtensionJacobianQuotientEquiv_coefficient (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) (a : K) :
    fieldExtensionJacobianQuotientEquiv ρ f hc h0 h1 hΔ
      (Ideal.Quotient.mk (equationDerivativeIdeal (MvPowerSeries.map ρ f))
        (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ρ f}) (C (ρ a)))) = ρ a := rfl

end DeJongAlterations.Algebra.NodeVariableMorse
