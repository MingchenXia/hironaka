import DeJongAlterations.Algebra.SteinSeparability
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# Actual reduced scalar tensors from a separating transcendence family

The original polynomial subalgebra and its fraction field give a flat
formally etale coefficient map into the ambient field.  Its scalar
change embeds in a formally etale algebra over an actual fraction field.
-/

noncomputable section

open TensorProduct IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace DeJongAlterations.Algebra.SteinTensorReduced

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
  {ι : Type u} {v : ι → F} (hv : AlgebraicIndependent K v)

include hv in
/-- Every actual scalar tensor is reduced; separation is used only over the original rational field. -/
theorem isReduced_tensorProduct
    [Algebra.EssFiniteType K F]
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    IsReduced (F ⊗[K] E) := by
  let A := Algebra.adjoin K (Set.range v)
  let B := IntermediateField.adjoin K (Set.range v)
  let : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallyEtale B F := Algebra.FormallyEtale.of_isSeparable B F
  let : Algebra.FormallyEtale A F := Algebra.FormallyEtale.comp A B F
  let : Module.Flat A B := IsLocalization.flat B (nonZeroDivisors A)
  let : Module.Flat A F := Module.Flat.trans A B F
  let : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_comp K A F
  let C := A ⊗[K] E
  let eC : C ≃ₐ[K] MvPolynomial ι E :=
    (Algebra.TensorProduct.congr hv.aevalEquiv.symm (AlgEquiv.refl (R := K) (A₁ := E))).trans
      ((Algebra.TensorProduct.comm K (MvPolynomial ι K) E).trans
        ((MvPolynomial.algebraTensorAlgEquiv K E).restrictScalars K))
  let : IsDomain C := eC.injective.isDomain
  let G := FractionRing C
  let : Algebra A G := inferInstance
  let : IsScalarTower A C G := inferInstance
  let m := Algebra.TensorProduct.map (AlgHom.id A F) (IsScalarTower.toAlgHom A C G)
  have hm : Function.Injective m :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := F)
      (IsScalarTower.toAlgHom A C G).toLinearMap (IsFractionRing.injective C G)
  let : Algebra G (F ⊗[A] G) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.FormallyEtale G (F ⊗[A] G) :=
    Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.commRight A G F)
  let : Algebra.EssFiniteType G (F ⊗[A] G) :=
    Algebra.EssFiniteType.of_surjective
      (Algebra.TensorProduct.commRight A G F).toAlgHom
      (Algebra.TensorProduct.commRight A G F).surjective
  let : IsReduced (F ⊗[A] G) := Algebra.FormallyUnramified.isReduced_of_field G _
  let e := Algebra.TensorProduct.cancelBaseChange K A A F E
  exact isReduced_of_injective (m.comp e.symm.toAlgHom) (hm.comp e.symm.injective)

end DeJongAlterations.Algebra.SteinTensorReduced
