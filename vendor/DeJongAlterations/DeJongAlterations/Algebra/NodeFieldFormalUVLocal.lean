import DeJongAlterations.Algebra.NodeFittingFormalUVQuotient
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Native local structures and literal maximal powers of the SAME actual uv quotient. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldFormalUVLocal

open NodeFormalMorse NodeGeometricCompletionFormalUV NodeFittingFormalUVQuotient

universe u
variable (K : Type u) [Field K]

/-- The actual original coefficient map proves nontriviality of this SAME quotient. -/
instance formalUV_nontrivial : Nontrivial (FormalUV K) :=
  (coefficientMap K).toRingHom.domain_nontrivial

/-- Locality is native on the literal quotient of the original local series ring. -/
instance formalUV_isLocalRing : IsLocalRing (FormalUV K) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The SAME literal original quotient is Noetherian. -/
instance formalUV_noetherian : IsNoetherianRing (FormalUV K) :=
  isNoetherianRing_of_surjective (Series K) _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The native maximal ideal is the ENTIRE actual original coordinate ideal. -/
theorem maximalIdeal_eq_coordinates :
    maximalIdeal (FormalUV K) = singularCoordinateIdeal K :=
  (ker_eq_maximalIdeal (coefficientMap K).toRingHom (coefficientMap_surjective K)).symm.trans
    (coefficientMap_ker K)

/-- The WHOLE original variable ideal has exactly the original maximal ideal as image. -/
theorem maximalIdeal_eq_map_variables :
    maximalIdeal (FormalUV K) = (NodeVariableMorse.variableIdeal K).map
      (Ideal.Quotient.mk (Ideal.span {((uvPolynomial K) : Series K)})) := by
  rw [maximalIdeal_eq_coordinates, NodeVariableMorse.variableIdeal_eq_pair, Ideal.map_span]
  simp only [Set.image_pair]
  rfl

/-- Every native maximal power retains the actual original quotient map. -/
theorem maximalPower_eq_map_variables (n : ℕ) :
    maximalIdeal (FormalUV K) ^ n = (NodeVariableMorse.variableIdeal K ^ n).map
      (Ideal.Quotient.mk (Ideal.span {((uvPolynomial K) : Series K)})) := by
  rw [Ideal.map_pow, maximalIdeal_eq_map_variables]

end DeJongAlterations.Algebra.NodeFieldFormalUVLocal
