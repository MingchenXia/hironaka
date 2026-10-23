import DeJongAlterations.Algebra.NodeCompletionPolynomial

/-! # The actual rational origin of the literal polynomial node -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (K : Type u) [Field K]

/-- The actual origin evaluation on the literal node quotient. -/
def originEvaluation : Node K →ₐ[K] K :=
  Ideal.Quotient.liftₐ (nodeIdeal K) (MvPolynomial.aeval (0 : Fin 2 → K)) (by
    change nodeIdeal K ≤ RingHom.ker (MvPolynomial.aeval (0 : Fin 2 → K)).toRingHom
    apply Ideal.span_le.mpr
    rintro f rfl
    simp)

@[simp]
theorem originEvaluation_mk (f : PolynomialRing K) :
    originEvaluation K (Ideal.Quotient.mk (nodeIdeal K) f) = MvPolynomial.constantCoeff f := by
  simp [originEvaluation]

/-- Every coefficient occurs as an actual value at the origin. -/
theorem originEvaluation_surjective : Function.Surjective (originEvaluation K) := by
  intro k
  refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C k), ?_⟩
  simp

/-- The actual maximal ideal defining the origin is exactly the evaluation kernel. -/
theorem originIdeal_eq_ker :
    originIdeal K = RingHom.ker (originEvaluation K).toRingHom := by
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (nodeIdeal K))
    Ideal.Quotient.mk_surjective
  rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_eq_left.mpr (nodeIdeal_le_idealOfVars K), RingHom.comap_ker]
  have hc : (originEvaluation K).toRingHom.comp (Ideal.Quotient.mk (nodeIdeal K)) =
      MvPolynomial.constantCoeff := by
    apply RingHom.ext
    exact originEvaluation_mk K
  rw [hc]
  exact idealOfVars_eq_ker_constantCoeff K

/-- The rational-origin residue quotient is actually the specified ground field. -/
def originQuotientEquiv : (Node K ⧸ originIdeal K) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (originIdeal_eq_ker K)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (originEvaluation_surjective K))

@[simp]
theorem originQuotientEquiv_mk (a : Node K) :
    originQuotientEquiv K (Ideal.Quotient.mk _ a) = originEvaluation K a := rfl

end DeJongAlterations.Algebra.NodeCompletion
