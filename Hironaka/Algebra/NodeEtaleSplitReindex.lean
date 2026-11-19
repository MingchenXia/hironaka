import Hironaka.Algebra.NodeGeometricCompletionCoefficientReindex

/-! # Actual coefficient reindexing of the WHOLE split and smoothing-parameter quotients -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleSplitReindex

open MvPowerSeries NodeFormalMorse NodeGeometricCompletionCoefficientReindex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The literal parameter quotient, without a change to its coefficients or equation. -/
abbrev ParameterNode (R : Type*) [CommRing R] (h : R) :=
  Series R ⧸ Ideal.span {(X (0 : Fin 2) : Series R) * X 1 - C h}

/-- The genuine split-node equivalence follows the SAME actual coefficient equivalence. -/
def splitEquiv (χ : R ≃+* S) :
    NodeFlatPresentation.SplitNode R ≃+* NodeFlatPresentation.SplitNode S :=
  Ideal.quotientEquiv _ _ (seriesEquiv χ) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    change (X (0 : Fin 2) : Series S) * X 1 =
      MvPowerSeries.map χ.toRingHom ((X (0 : Fin 2) : Series R) * X 1)
    rw [map_mul, map_X, map_X])

/-- EVERY original series representative follows the actual coefficientwise map. -/
theorem splitEquiv_mk (χ : R ≃+* S) (f : Series R) :
    splitEquiv χ (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (MvPowerSeries.map χ.toRingHom f) := rfl

/-- EVERY coefficient follows precisely the original actual χ. -/
theorem splitEquiv_coefficient (χ : R ≃+* S) (a : R) :
    splitEquiv χ (Ideal.Quotient.mk _ (C a)) = Ideal.Quotient.mk _ (C (χ a)) := by
  rw [splitEquiv_mk, map_C]
  rfl

/-- BOTH original split-node coordinates are retained literally. -/
theorem splitEquiv_coordinate (χ : R ≃+* S) (i : Fin 2) :
    splitEquiv χ (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _ (X i : Series S) := by
  rw [splitEquiv_mk, map_X]

/-- The genuine whole parameter-quotient equivalence retains the SAME actual χ and its actual parameter image. -/
def parameterEquiv (χ : R ≃+* S) (h : R) : ParameterNode R h ≃+* ParameterNode S (χ h) :=
  Ideal.quotientEquiv _ _ (seriesEquiv χ) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    change (X (0 : Fin 2) : Series S) * X 1 - C (χ h) =
      MvPowerSeries.map χ.toRingHom ((X (0 : Fin 2) : Series R) * X 1 - C h)
    rw [map_sub, map_mul, map_X, map_X, map_C]
    rfl)

/-- EVERY original series representative follows the SAME actual coefficientwise parameter map. -/
theorem parameterEquiv_mk (χ : R ≃+* S) (h : R) (f : Series R) :
    parameterEquiv χ h (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (MvPowerSeries.map χ.toRingHom f) := rfl

/-- EVERY actual original parameter-ring coefficient follows precisely the SAME χ. -/
theorem parameterEquiv_coefficient (χ : R ≃+* S) (h a : R) :
    parameterEquiv χ h (Ideal.Quotient.mk _ (C a)) = Ideal.Quotient.mk _ (C (χ a)) := by
  rw [parameterEquiv_mk, map_C]
  rfl

/-- BOTH original coordinates are retained literally in the actual parameter quotient. -/
theorem parameterEquiv_coordinate (χ : R ≃+* S) (h : R) (i : Fin 2) :
    parameterEquiv χ h (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _ (X i : Series S) := by
  rw [parameterEquiv_mk, map_X]

end Hironaka.Algebra.NodeEtaleSplitReindex
