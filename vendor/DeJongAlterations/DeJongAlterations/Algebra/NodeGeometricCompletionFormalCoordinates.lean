import DeJongAlterations.Algebra.NodeGeometricCompletionFormalModel

/-! The actual two-coordinate one-gradient-column cokernel of the completed ORIGINAL
polynomial hypersurface differentials. The formal-model comparison retains the actual
completed original coordinate differentials. -/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.NodeGeometricCompletionFormalCoordinates

open NodeFittingGeneral NodeGeometricCompletionCoherentDifferentials NodeGeometricCompletionFormalModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K] (f : MvPolynomial (Fin 2) K)

/-- Actual finite coordinates of the native original cotangent basis after the canonical formal map. -/
def cotangentCoordinates :
    (FormalHypersurface f ⊗[PolynomialHypersurface f] (polynomialPresentation f).toExtension.CotangentSpace)
      ≃ₗ[FormalHypersurface f] (Fin 2 → FormalHypersurface f) :=
  (formalCotangentBasis f).repr.trans (Finsupp.linearEquivFunOnFinite _ _ _)

/-- The actual native formal derivatives of the SAME original polynomial equation. -/
def gradientCoordinates : Fin 2 → FormalHypersurface f := fun i =>
  Ideal.Quotient.mk (Ideal.span {(f : NodeFormalMorse.Series K)}) (MvPowerSeries.pderiv K i (f : NodeFormalMorse.Series K))

/-- The whole original relation column is exactly the pair of native formal partials. -/
theorem cotangentCoordinates_gradient :
    cotangentCoordinates K f (formalGradientVector f) = gradientCoordinates K f := by
  funext i
  exact formalGradient_coordinate_derivative f i

/-- The literal actual one-gradient-column cokernel over the formal hypersurface. -/
abbrev GradientCokernel :=
  (Fin 2 → FormalHypersurface f) ⧸ Submodule.span (FormalHypersurface f) {gradientCoordinates K f}

/-- Coordinate quotient comparison with the ORIGINAL finitely presented differential module
pulled through the canonical formal map. -/
def gradientCokernelEquiv : GradientCokernel K f ≃ₗ[FormalHypersurface f] FormalModelDifferentials f :=
  (Submodule.Quotient.equiv _ _ (cotangentCoordinates K f) (by
    rw [Submodule.map_span, Set.image_singleton]
    exact congrArg (fun v => Submodule.span (FormalHypersurface f) {v})
      (cotangentCoordinates_gradient K f))).symm.trans
      (formalDifferentialQuotientEquiv f)

/-- The native differential projection on each actual original coordinate basis vector. -/
theorem formalDifferentialMap_basis (i : Fin 2) :
    formalDifferentialMap f (formalCotangentBasis f i) =
      1 ⊗ₜ[PolynomialHypersurface f]
        KaehlerDifferential.D K (PolynomialHypersurface f)
          (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.X i)) := by
  simp only [formalCotangentBasis, Module.Basis.baseChange_apply,
    formalDifferentialMap, LinearMap.baseChange_tmul,
    _root_.Algebra.Generators.toKaehler_cotangentSpaceBasis]
  rfl

/-- The literal standard coordinate class is its actual ORIGINAL polynomial differential. -/
theorem gradientCokernelEquiv_coordinate (i : Fin 2) :
    gradientCokernelEquiv K f (Submodule.Quotient.mk (Pi.single i 1)) =
      1 ⊗ₜ[PolynomialHypersurface f]
        KaehlerDifferential.D K (PolynomialHypersurface f)
          (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.X i)) := by
  have hcoord : cotangentCoordinates K f (formalCotangentBasis f i) = Pi.single i 1 := by
    simp [cotangentCoordinates, Module.Basis.repr_self, Finsupp.linearEquivFunOnFinite_single]
  rw [← hcoord]
  change (formalDifferentialQuotientEquiv f)
    ((Submodule.Quotient.equiv _ _ (cotangentCoordinates K f) _).symm
      (Submodule.Quotient.mk (cotangentCoordinates K f (formalCotangentBasis f i)))) = _
  have hq : Submodule.Quotient.mk (cotangentCoordinates K f (formalCotangentBasis f i)) =
      Submodule.Quotient.equiv
        (Submodule.span (FormalHypersurface f) {formalGradientVector f})
        (Submodule.span (FormalHypersurface f) {gradientCoordinates K f}) (cotangentCoordinates K f)
        (by
          rw [Submodule.map_span, Set.image_singleton]
          exact congrArg (fun v => Submodule.span (FormalHypersurface f) {v})
            (cotangentCoordinates_gradient K f))
        (Submodule.Quotient.mk (formalCotangentBasis f i)) := rfl
  rw [hq, LinearEquiv.symm_apply_apply]
  exact formalDifferentialMap_basis K f i

/-- A literal isomorphism from the completed ORIGINAL coherent module to the actual formal
finite-coordinate cokernel. It is over the ENTIRE original polynomial hypersurface. -/
def completedOmegaGradientEquiv :
    CompletedOmega K (PolynomialHypersurface f) (coordinateIdeal K f)
      ≃ₗ[PolynomialHypersurface f] GradientCokernel K f :=
  (completedOmegaFormalEquiv K f).trans
    ((gradientCokernelEquiv K f).symm.restrictScalars (PolynomialHypersurface f))

/-- The actual completed differential of each original coordinate becomes the literal
standard basis class of the actual two-coordinate gradient cokernel. -/
theorem completedOmegaGradientEquiv_coordinate (i : Fin 2) :
    completedOmegaGradientEquiv K f
      (AdicCompletion.of (coordinateIdeal K f) (KaehlerDifferential K (PolynomialHypersurface f))
        (KaehlerDifferential.D K (PolynomialHypersurface f)
          (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.X i)))) =
      Submodule.Quotient.mk (Pi.single i 1) := by
  apply (gradientCokernelEquiv K f).injective
  change gradientCokernelEquiv K f
    ((gradientCokernelEquiv K f).symm (completedOmegaFormalEquiv K f _)) = _
  rw [LinearEquiv.apply_symm_apply, completedOmegaFormalEquiv_original,
    gradientCokernelEquiv_coordinate]

/-- The whole actual completed scalar action is preserved through the same canonical map. -/
theorem completedOmegaGradientEquiv_smul
    (a : AdicCompletion (coordinateIdeal K f) (PolynomialHypersurface f))
    (ω : CompletedOmega K (PolynomialHypersurface f) (coordinateIdeal K f)) :
    completedOmegaGradientEquiv K f (a • ω) =
      completionEquiv K f a • completedOmegaGradientEquiv K f ω := by
  change (gradientCokernelEquiv K f).symm (completedOmegaFormalEquiv K f (a • ω)) = _
  rw [completedOmegaFormalEquiv_smul, map_smul]
  rfl

end DeJongAlterations.Algebra.NodeGeometricCompletionFormalCoordinates
