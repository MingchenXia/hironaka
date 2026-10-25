import DeJongAlterations.Algebra.NodeFittingFormalUVQuotient
import DeJongAlterations.Algebra.NodeFittingModuleSemilinear
import DeJongAlterations.Algebra.NodeSingularQuotientDescent

/-! # The original intrinsic Fitting quotient from an actual formal uv module -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingFormalUVDescent

open NodeGeometricCompletionFormalUV NodeFittingModule NodeFittingFormalUVQuotient
open scoped TensorProduct

universe u v w z
variable {K : Type u} [Field K] {R : Type v} [CommRing R] {C : Type w} [CommRing C]
  [Algebra K R] [Algebra K C] [Algebra R C] [IsScalarTower K R C]
  {N : Type z} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
  (e : C ≃ₐ[K] FormalUV K)

local instance : RingHomInvPair e.toRingEquiv.toRingHom e.toRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv

local instance : RingHomInvPair e.toRingEquiv.symm.toRingHom e.toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e.toRingEquiv

variable (E : (C ⊗[R] N) ≃ₛₗ[e.toRingEquiv.toRingHom] DifferentialModule K)

omit [Algebra K R] [IsScalarTower K R C] in
/-- Whole original Fitting base change followed by the SAME actual semilinear model. -/
theorem extended_fittingIdeal_map
    (E : (C ⊗[R] N) ≃ₛₗ[e.toRingEquiv.toRingHom] DifferentialModule K) :
    ((fittingIdeal (R := R) (M := N) 1).map (algebraMap R C)).map
      e.toRingEquiv.toRingHom =
      fittingIdeal (R := FormalUV K) (M := DifferentialModule K) 1 := by
  rw [fittingIdeal_baseChange (R := R) (M := N) C 1]
  exact fittingIdeal_semilinear e.toRingEquiv E 1

/-- The actual extended intrinsic quotient, with the original K coefficients. -/
def extendedQuotientEquiv :
    (C ⧸ (fittingIdeal (R := R) (M := N) 1).map (algebraMap R C)) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlg _ _ e (extended_fittingIdeal_map e E).symm).trans
    (intrinsicQuotientEquiv K)

omit [Algebra K R] [IsScalarTower K R C] in
@[simp]
theorem extendedQuotientEquiv_mk (c : C) :
    extendedQuotientEquiv e E (Ideal.Quotient.mk _ c) = coefficientMap K (e c) := by
  change intrinsicQuotientEquiv K (Ideal.Quotient.mk _ (e c)) = coefficientMap K (e c)
  exact intrinsicQuotientEquiv_mk K (e c)

/-- Faithful flatness descends the ENTIRE original quotient, including its K action. -/
def originalQuotientEquiv [Module.FaithfullyFlat R C] :
    (R ⧸ fittingIdeal (R := R) (M := N) 1) ≃ₐ[K] K :=
  NodeSingularQuotientDescent.quotientDescentEquiv _ (extendedQuotientEquiv e E)

@[simp]
theorem originalQuotientEquiv_mk [Module.FaithfullyFlat R C] (r : R) :
    originalQuotientEquiv e E (Ideal.Quotient.mk _ r) =
      coefficientMap K (e (algebraMap R C r)) := by
  simp only [originalQuotientEquiv,
    NodeSingularQuotientDescent.quotientDescentEquiv_mk, extendedQuotientEquiv_mk]

@[simp]
theorem originalQuotientEquiv_coefficient [Module.FaithfullyFlat R C] (k : K) :
    originalQuotientEquiv e E
      (algebraMap K (R ⧸ fittingIdeal (R := R) (M := N) 1) k) = k :=
  (originalQuotientEquiv e E).commutes k

end DeJongAlterations.Algebra.NodeFittingFormalUVDescent
