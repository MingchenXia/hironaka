import Hironaka.Algebra.NodeGeometricCompletionDiagonalPoint
import Hironaka.Algebra.AdicCompletionEtale
import Hironaka.Algebra.CompletionLocalMap
import Mathlib.RingTheory.Etale.Field

/-! The SAME actual diagonal local map is formally etale and EssFT once the
ORIGINAL residue extension is finite separable. Its ACTUAL completions are isomorphic. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionDiagonalEtale

open NodeGeometricCompletionDiagonalPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K R : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra diagonalPoint_isMaximal
  pointFieldAlgebra originalAlgebra originalMap_isLocalHom

/-- The actual tensor swap is over the ORIGINAL R, with its SAME right-factor action. -/
def tensorCommOverOriginal : (R ⊗[K] ResidueField R) ≃ₐ[R] TensorRing K R :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K R (ResidueField R)).toRingEquiv)
    fun _ => rfl

variable [FiniteDimensional K (ResidueField R)] [Algebra.IsSeparable K (ResidueField R)]

omit [Algebra.IsSeparable K (ResidueField R)] in
/-- Actual native finite type of the SAME original coefficient extension. -/
theorem tensor_finiteType : Algebra.FiniteType R (TensorRing K R) := by
  let : Algebra.FiniteType K (ResidueField R) := inferInstance
  let : Algebra.FiniteType R (R ⊗[K] ResidueField R) := inferInstance
  exact Algebra.FiniteType.of_surjective (tensorCommOverOriginal K R).toAlgHom
    (tensorCommOverOriginal K R).surjective

omit [FiniteDimensional K (ResidueField R)] in
/-- Actual native formal etaleness from the ORIGINAL residue separability only. -/
theorem tensor_formallyEtale : Algebra.FormallyEtale R (TensorRing K R) := by
  let : Algebra.FormallyEtale K (ResidueField R) := Algebra.FormallyEtale.of_isSeparable K _
  let : Algebra.FormallyEtale R (R ⊗[K] ResidueField R) := inferInstance
  exact Algebra.FormallyEtale.of_equiv (tensorCommOverOriginal K R)

attribute [local instance] tensor_finiteType tensor_formallyEtale

omit [Algebra.IsSeparable K (ResidueField R)] in
/-- The SAME actual original local map is internally essentially finite type. -/
theorem original_essFiniteType : Algebra.EssFiniteType R (DiagonalLocal K R) := by
  let : Algebra.EssFiniteType (TensorRing K R) (DiagonalLocal K R) :=
    Algebra.EssFiniteType.of_isLocalization _ (diagonalPoint K R).primeCompl
  exact Algebra.EssFiniteType.comp R (TensorRing K R) (DiagonalLocal K R)

omit [FiniteDimensional K (ResidueField R)] in
/-- The SAME actual original local map is internally formally etale. -/
theorem original_formallyEtale : Algebra.FormallyEtale R (DiagonalLocal K R) := by
  let : Algebra.FormallyEtale (TensorRing K R) (DiagonalLocal K R) := inferInstance
  exact Algebra.FormallyEtale.comp R (TensorRing K R) (DiagonalLocal K R)

attribute [local instance] original_essFiniteType original_formallyEtale

/-- The ACTUAL original completion is identified with the SAME actual diagonal completion. -/
def completedOriginalEquiv : AdicCompletion (maximalIdeal R) R ≃ₐ[R]
    AdicCompletion (maximalIdeal (DiagonalLocal K R)) (DiagonalLocal K R) :=
  AdicCompletionEtale.completedAlgEquiv (originalResidue_bijective K R)

/-- EVERY original coefficient retains its literal actual local-completion image. -/
theorem completedOriginalEquiv_of (r : R) :
    completedOriginalEquiv K R (AdicCompletion.of (maximalIdeal R) R r) =
      AdicCompletion.of (maximalIdeal (DiagonalLocal K R)) (DiagonalLocal K R)
        (algebraMap R (DiagonalLocal K R) r) :=
  AdicCompletionEtale.completedRingEquiv_of (originalResidue_bijective K R) r

/-- The WHOLE forward map is literally the canonical completed original local map. -/
theorem completedOriginalEquiv_toRingHom :
    (completedOriginalEquiv K R).toRingHom =
      CompletionLocalMap.completionMap (algebraMap R (DiagonalLocal K R)) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [CompletionLocalMap.evalₐ_completionMap]
  change
    (Ideal.quotientEquivAlgOfEq (DiagonalLocal K R)
      (by simp : (maximalIdeal (DiagonalLocal K R) ^ n • ⊤ : Ideal (DiagonalLocal K R)) =
        maximalIdeal (DiagonalLocal K R) ^ n))
      (AdicCompletionEtale.quotientEquiv (originalResidue_bijective K R) n (x.val n)) =
    Ideal.quotientMap (maximalIdeal (DiagonalLocal K R) ^ n)
      (algebraMap R (DiagonalLocal K R))
      (CompletionLocalMap.maximalIdeal_pow_le_comap (algebraMap R (DiagonalLocal K R)) n)
      ((Ideal.quotientEquivAlgOfEq R
        (by simp : (maximalIdeal R ^ n • ⊤ : Ideal R) = maximalIdeal R ^ n)) (x.val n))
  induction x.val n using Quotient.inductionOn' with
  | _ r => rfl

end Hironaka.Algebra.NodeGeometricCompletionDiagonalEtale
