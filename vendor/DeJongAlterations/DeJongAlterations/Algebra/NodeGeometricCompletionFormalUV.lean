import DeJongAlterations.Algebra.NodeGeometricCompletionFormalCoordinates

/-! The literal uv model: the completion of its ORIGINAL polynomial differential module
is the actual two-generator module with the single relation (v,u), retaining both original
coordinate differentials and all actual completed scalar actions. -/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV

open NodeFittingGeneral NodeGeometricCompletionCoherentDifferentials
  NodeGeometricCompletionFormalModel NodeGeometricCompletionFormalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K]

abbrev uvPolynomial : MvPolynomial (Fin 2) K := MvPolynomial.X 0 * MvPolynomial.X 1
abbrev PolynomialUV := PolynomialHypersurface (uvPolynomial K)
abbrev FormalUV := FormalHypersurface (uvPolynomial K)

/-- The actual original formal coordinate class. -/
def coordinate (i : Fin 2) : FormalUV K :=
  Ideal.Quotient.mk (Ideal.span {((uvPolynomial K) : NodeFormalMorse.Series K)}) (MvPowerSeries.X i)

/-- The literal original gradient relation (v,u). -/
def relationVector : Fin 2 → FormalUV K := ![coordinate K 1, coordinate K 0]

/-- The native formal gradient of the SAME original uv equation is exactly (v,u). -/
theorem gradient_uv : gradientCoordinates K (uvPolynomial K) = relationVector K := by
  funext i
  fin_cases i <;>
    simp [gradientCoordinates, uvPolynomial, relationVector, coordinate,
      MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz,
      MvPowerSeries.pderiv_X_of_ne]

/-- The literal finite continuous-differential model module B²/B(v,u). -/
abbrev DifferentialModule :=
  (Fin 2 → FormalUV K) ⧸ Submodule.span (FormalUV K) {relationVector K}

/-- The canonical actual completed ORIGINAL polynomial differential comparison for uv. -/
def completedOmegaEquiv :
    CompletedOmega K (PolynomialUV K) (coordinateIdeal K (uvPolynomial K))
      ≃ₗ[PolynomialUV K] DifferentialModule K :=
  (completedOmegaGradientEquiv K (uvPolynomial K)).trans
    ((Submodule.quotEquivOfEq _ _ (by rw [gradient_uv])).restrictScalars (PolynomialUV K))

/-- The actual completed ORIGINAL coordinate differentials are the literal standard classes. -/
theorem completedOmegaEquiv_coordinate (i : Fin 2) :
    completedOmegaEquiv K
      (AdicCompletion.of (coordinateIdeal K (uvPolynomial K)) (KaehlerDifferential K (PolynomialUV K))
        (KaehlerDifferential.D K (PolynomialUV K)
          (Ideal.Quotient.mk (polynomialIdeal (uvPolynomial K)) (MvPolynomial.X i)))) =
      Submodule.Quotient.mk (Pi.single i 1) := by
  unfold completedOmegaEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [completedOmegaGradientEquiv_coordinate]
  rfl

/-- The completed coherent comparison retains the entire actual completed scalar action. -/
theorem completedOmegaEquiv_smul
    (a : AdicCompletion (coordinateIdeal K (uvPolynomial K)) (PolynomialUV K))
    (ω : CompletedOmega K (PolynomialUV K) (coordinateIdeal K (uvPolynomial K))) :
    completedOmegaEquiv K (a • ω) =
      completionEquiv K (uvPolynomial K) a • completedOmegaEquiv K ω := by
  unfold completedOmegaEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [completedOmegaGradientEquiv_smul, map_smul]

/-- Both actual original coordinate classes of the model ring map to the literal formal coordinates. -/
theorem completionEquiv_coordinate (i : Fin 2) :
    completionEquiv K (uvPolynomial K)
      (algebraMap (PolynomialUV K)
        (AdicCompletion (coordinateIdeal K (uvPolynomial K)) (PolynomialUV K))
          (Ideal.Quotient.mk (polynomialIdeal (uvPolynomial K)) (MvPolynomial.X i))) =
      coordinate K i := by
  rw [completionEquiv_original, polynomialToFormal_coordinate]
  rfl

end DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
