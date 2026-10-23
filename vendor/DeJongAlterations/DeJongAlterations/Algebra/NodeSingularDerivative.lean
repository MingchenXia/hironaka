import DeJongAlterations.Algebra.NodeSingularGradient
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-! # Actual native partial derivatives of the original quadratic node equation -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeSingular

open MvPowerSeries NodeNonsplit NodeFormalMorse

universe u
variable {R : Type u} [CommRing R]

/-- The actual first native partial derivative is the first original gradient. -/
theorem pderiv_zero (Q : Quadratic R) (h : R) :
    MvPowerSeries.pderiv R (0 : Fin 2) (Q.series - C h) =
      leftGradient (Q.map C) (X 0) (X 1) := by
  simp [Quadratic.series, Quadratic.value, Quadratic.map, leftGradient,
    map_add, map_sub, Derivation.leibniz,
    smul_eq_mul]
  ring

/-- The actual second native partial derivative is the second original gradient. -/
theorem pderiv_one (Q : Quadratic R) (h : R) :
    MvPowerSeries.pderiv R (1 : Fin 2) (Q.series - C h) =
      rightGradient (Q.map C) (X 0) (X 1) := by
  simp [Quadratic.series, Quadratic.value, Quadratic.map, rightGradient,
    map_add, map_sub, Derivation.leibniz,
    smul_eq_mul]
  ring

/-- The actual ideal of native partial derivatives is the literal variable ideal. -/
theorem partialDerivativeIdeal_eq (Q : Quadratic R) (h : R) :
    Ideal.span {MvPowerSeries.pderiv R (0 : Fin 2) (Q.series - C h),
      MvPowerSeries.pderiv R (1 : Fin 2) (Q.series - C h)} =
      Ideal.span {(X 0 : Series R), X 1} := by
  rw [pderiv_zero, pderiv_one]
  exact gradientIdeal_eq_coordinateIdeal _ _ _

end DeJongAlterations.Algebra.NodeSingular
