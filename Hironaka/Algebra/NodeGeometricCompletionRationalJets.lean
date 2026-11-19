import Hironaka.Algebra.NodeGeometricCompletionLocalizedJets
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Field.Equiv

/-! Actual field-extension finite jets at the actual lift of a rational point.
The residue identification is a natural input; no completed node model is assumed. -/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionRationalJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  {R : Type w} [CommRing R] [Algebra K R] (p : Ideal R)

/-- The literal extended point ideal in the actual affine field base change. -/
def tensorPoint : Ideal (L ⊗[K] R) :=
  p.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* L ⊗[K] R)

/-- The actual residue identification after literal field base change. -/
def tensorResidueEquiv (e : (R ⧸ p) ≃ₐ[K] K) :
    ((L ⊗[K] R) ⧸ tensorPoint K L p) ≃ₐ[L] L :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L R L p).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans
      (Algebra.TensorProduct.rid K L L))

/-- The SAME literal extended ideal is maximal, proved from the actual residue triangle. -/
theorem tensorPoint_isMaximal (e : (R ⧸ p) ≃ₐ[K] K) : (tensorPoint K L p).IsMaximal := by
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
  exact MulEquiv.isField (Field.toIsField L) (tensorResidueEquiv K L p e).toMulEquiv

/-- Native field extension of EVERY original finite jet, before localization. -/
def tensorJetEquiv (n : ℕ) :
    (L ⊗[K] (R ⧸ p ^ n)) ≃ₐ[L] ((L ⊗[K] R) ⧸ tensorPoint K L p ^ n) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L R L (p ^ n)).trans
    (Ideal.quotientEquivAlgOfEq L (Ideal.map_pow _ _ _))

/-- EVERY pure finite-jet representative retains its literal actual tensor image. -/
theorem tensorJetEquiv_tmul (n : ℕ) (l : L) (r : R) :
    tensorJetEquiv K L p n (l ⊗ₜ[K] Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (tensorPoint K L p ^ n) (l ⊗ₜ[K] r) := rfl

section TensorStalk

variable [(tensorPoint K L p).IsPrime]

/-- The actual local ring at the SAME extended point. -/
abbrev TensorStalk := Localization (tensorPoint K L p).primeCompl

/-- Its external L action is literally left tensor inclusion followed by localization. -/
@[instance_reducible]
def tensorStalkFieldAlgebra : Algebra L (TensorStalk K L p) :=
  inferInstance

attribute [local instance] tensorStalkFieldAlgebra

/-- The ENTIRE original field/tensor/localization scalar triangle is literal. -/
theorem tensorStalk_scalarTower : IsScalarTower L (L ⊗[K] R) (TensorStalk K L p) :=
  inferInstance

/-- The WHOLE native external-field map is the original left-factor localization map. -/
theorem tensorStalk_fieldMap :
    algebraMap L (TensorStalk K L p) =
      (algebraMap (L ⊗[K] R) (TensorStalk K L p)).comp (algebraMap L (L ⊗[K] R)) :=
  IsScalarTower.algebraMap_eq L (L ⊗[K] R) (TensorStalk K L p)

attribute [local instance] tensorStalk_scalarTower

end TensorStalk

/-- EVERY native rational-point jet after field extension is the SAME actual stalk jet. -/
def actualTensorStalkJetEquiv (e : (R ⧸ p) ≃ₐ[K] K) (n : ℕ) :
    letI := tensorPoint_isMaximal K L p e
    (L ⊗[K] (R ⧸ p ^ n)) ≃ₐ[L]
      (TensorStalk K L p ⧸ (tensorPoint K L p ^ n).map
        (algebraMap (L ⊗[K] R) (TensorStalk K L p))) := by
  letI := tensorPoint_isMaximal K L p e
  exact (tensorJetEquiv K L p n).trans
    ((NodeGeometricCompletionLocalizedJets.powerQuotientEquiv
      (tensorPoint K L p) (TensorStalk K L p) n).restrictScalars L)

/-- EVERY original scalar and germ retain the actual tensor/projection localization image. -/
theorem actualTensorStalkJetEquiv_tmul (e : (R ⧸ p) ≃ₐ[K] K)
    (n : ℕ) (l : L) (r : R) :
    letI := tensorPoint_isMaximal K L p e
    actualTensorStalkJetEquiv K L p e n (l ⊗ₜ[K] Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk ((tensorPoint K L p ^ n).map
        (algebraMap (L ⊗[K] R) (TensorStalk K L p)))
        (algebraMap (L ⊗[K] R) (TensorStalk K L p) (l ⊗ₜ[K] r)) := by
  let := tensorPoint_isMaximal K L p e
  change NodeGeometricCompletionLocalizedJets.powerQuotientEquiv
    (tensorPoint K L p) (TensorStalk K L p) n
      (tensorJetEquiv K L p n (l ⊗ₜ[K] Ideal.Quotient.mk (p ^ n) r)) = _
  rw [tensorJetEquiv_tmul, NodeGeometricCompletionLocalizedJets.powerQuotientEquiv_mk]

end Hironaka.Algebra.NodeGeometricCompletionRationalJets
