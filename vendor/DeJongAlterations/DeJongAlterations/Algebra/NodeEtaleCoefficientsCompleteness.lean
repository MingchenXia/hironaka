import DeJongAlterations.Algebra.NodeEtaleCoefficientsLift
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Native completeness of the actual finite coefficient algebra -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeEtaleCoefficients

open TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A]
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Base completeness and the native finite-module completion theorem supply an actual equivalence. -/
def finiteCompletionEquiv : M ≃ₗ[A] AdicCompletion I M :=
  (((TensorProduct.lid A M).symm.trans
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv I A) (LinearEquiv.refl A M))).trans
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars A))

@[simp]
theorem finiteCompletionEquiv_apply (x : M) :
    finiteCompletionEquiv I M x = AdicCompletion.of I M x := by
  change AdicCompletion.ofTensorProduct I M
    ((AdicCompletion.ofLinearEquiv I A) 1 ⊗ₜ[A] x) = _
  rw [AdicCompletion.ofLinearEquiv_apply, AdicCompletion.ofTensorProduct_tmul]
  change (1 : AdicCompletion I A) • AdicCompletion.of I M x = _
  exact one_smul _ _

/-- Every finite module over the original complete Noetherian coefficient ring is actually complete. -/
theorem isAdicComplete_finite : IsAdicComplete I M := by
  apply AdicCompletion.of_bijective_iff.mp
  have he : (finiteCompletionEquiv I M : M → AdicCompletion I M) = AdicCompletion.of I M :=
    funext (finiteCompletionEquiv_apply I M)
  rw [← he]
  exact (finiteCompletionEquiv I M).bijective

variable (A) [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (L : Type u) [Field L] [Algebra (IsLocalRing.maximalIdeal A).ResidueField L]
  [FiniteDimensional (IsLocalRing.maximalIdeal A).ResidueField L]
  [Algebra.IsSeparable (IsLocalRing.maximalIdeal A).ResidueField L]

/-- The literal internally constructed local coefficient algebra is complete at its actual maximal ideal. -/
instance coefficients_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal (Coefficients A L)) (Coefficients A L) := by
  rw [← coefficients_map_maximalIdeal A L]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr
    (isAdicComplete_finite (IsLocalRing.maximalIdeal A) (Coefficients A L))

end DeJongAlterations.Algebra.NodeEtaleCoefficients
