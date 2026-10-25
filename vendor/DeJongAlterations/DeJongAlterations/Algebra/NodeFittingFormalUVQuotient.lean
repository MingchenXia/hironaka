import DeJongAlterations.Algebra.NodeFittingModuleOneRelation
import DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
import DeJongAlterations.Algebra.NodeVariableMorseJacobian

/-! # Intrinsic Fitting ideal and actual coefficient quotient of B²/B(v,u) -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingFormalUVQuotient

open NodeGeometricCompletionFormalUV NodeFittingModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K]

/-- The original coordinate ideal in the SAME actual formal uv ring. -/
def singularCoordinateIdeal : Ideal (FormalUV K) :=
  Ideal.span {coordinate K 0, coordinate K 1}

/-- The actual quotient map and full native kernel give the original one-relation presentation. -/
def differentialPresentation : FiniteMatrixPresentation (R := FormalUV K) (DifferentialModule K) :=
  oneRelationPresentation (Pi.basisFun (FormalUV K) (Fin 2)) (relationVector K)
    (Submodule.mkQ (Submodule.span (FormalUV K) {relationVector K}))
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)

instance differential_finitePresentation :
    Module.FinitePresentation (FormalUV K) (DifferentialModule K) :=
  (differentialPresentation K).finitePresentation

/-- The ENTIRE intrinsic ideal is computed from the actual original relation. -/
theorem fittingIdeal_eq_coordinateIdeal :
    fittingIdeal (R := FormalUV K) (M := DifferentialModule K) 1 = singularCoordinateIdeal K := by
  simpa [singularCoordinateIdeal, relationVector, Set.pair_comm] using
    (fittingIdeal_oneRelation (Pi.basisFun (FormalUV K) (Fin 2)) (relationVector K)
      (Submodule.mkQ (Submodule.span (FormalUV K) {relationVector K}))
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _))

theorem uv_constantCoeff :
    MvPowerSeries.constantCoeff ((uvPolynomial K) : NodeFormalMorse.Series K) = 0 := by
  simp [uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X]

/-- Actual constant evaluation on the original formal hypersurface. -/
def coefficientMap : FormalUV K →ₐ[K] K :=
  NodeVariableMorse.equationConstantMap
    ((uvPolynomial K) : NodeFormalMorse.Series K) (uv_constantCoeff K)

theorem coefficientMap_surjective : Function.Surjective (coefficientMap K) :=
  NodeVariableMorse.equationConstantMap_surjective _ (uv_constantCoeff K)

/-- The full kernel preserves all original coefficients, including nilpotent directions. -/
theorem coefficientMap_ker : RingHom.ker (coefficientMap K) = singularCoordinateIdeal K := by
  change RingHom.ker (Ideal.Quotient.lift _
    (NodeVariableMorse.seriesConstantMap (K := K)).toRingHom _) = _
  rw [Ideal.ker_quotient_lift, NodeVariableMorse.seriesConstantMap_kernel]
  unfold NodeVariableMorse.variableIdeal singularCoordinateIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [coordinate]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The actual coefficient quotient of the intrinsic continuous-differential Fitting ideal. -/
def intrinsicQuotientEquiv :
    (FormalUV K ⧸ fittingIdeal (R := FormalUV K) (M := DifferentialModule K) 1) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K
    ((fittingIdeal_eq_coordinateIdeal K).trans (coefficientMap_ker K).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (coefficientMap_surjective K))

@[simp]
theorem intrinsicQuotientEquiv_mk (b : FormalUV K) :
    intrinsicQuotientEquiv K
      (Ideal.Quotient.mk (fittingIdeal (R := FormalUV K) (M := DifferentialModule K) 1) b) =
      coefficientMap K b := by
  simp only [intrinsicQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

@[simp]
theorem intrinsicQuotientEquiv_coefficient (a : K) :
    intrinsicQuotientEquiv K
      (algebraMap K (FormalUV K ⧸ fittingIdeal (R := FormalUV K) (M := DifferentialModule K) 1) a) =
      a :=
  (intrinsicQuotientEquiv K).commutes a

end DeJongAlterations.Algebra.NodeFittingFormalUVQuotient
