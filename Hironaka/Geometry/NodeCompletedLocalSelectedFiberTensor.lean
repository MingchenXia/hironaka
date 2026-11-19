import Hironaka.Geometry.NodeCompletedLocalSelectedAffine
import Hironaka.Geometry.NodeCompletedLocalFiberFieldSection
import Hironaka.Algebra.NodeGeometricCompletionFiberTensor

/-! The SAME original closed-fibre coefficients in the literal selected stalk tensor. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalSelectedFiberTensor

open NodeCompletedLocalResiduePoint NodeCompletedLocalSelectedAffine NodeCompletedLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

attribute [local instance] originalAlgebra baseFieldAlgebra originalBaseAlgebra
  originalFiberResidueAlgebra

local notation "A" => S.presheaf.stalk (f x)
local notation "R" => X.presheaf.stalk x
local notation "k" => S.residueField (f x)

/-- The actual original base residue map, exposed as the SAME native stalk algebra. -/
@[instance_reducible]
def baseResidueAlgebra : Algebra A k := (S.residue (f x)).hom.toAlgebra

attribute [local instance] baseResidueAlgebra

/-- The whole actual selected local-base action is the original residue coefficient composite. -/
theorem original_coefficient_triangle :
    algebraMap A L = (algebraMap k L).comp (residue A) := by
  ext c
  change algebraMap (X.residueField x) L ((X.residue x) ((f.stalkMap x) c)) =
    algebraMap (X.residueField x) L ((f.residueFieldMap x) ((S.residue (f x)) c))
  rfl

/-- The actual original base and prescribed residue coefficients form a native scalar tower. -/
theorem original_scalarTower : IsScalarTower A k L :=
  IsScalarTower.of_algebraMap_eq' (original_coefficient_triangle f x L)

attribute [local instance] original_scalarTower

/-- The ORIGINAL closed-fibre quotient is a native residue tensor, over its SAME actual coefficients. -/
def residueTensorEquiv : OriginalFiberRing f x ≃ₐ[k] (k ⊗[A] R) := by
  refine AlgEquiv.ofRingEquiv
    (f := (originalFiberTensorEquiv f x).toRingEquiv.trans
      (Algebra.TensorProduct.comm A R k).toRingEquiv) ?_
  intro c
  obtain ⟨a, rfl⟩ := residue_surjective c
  change (Algebra.TensorProduct.comm A R k)
    (originalFiberTensorEquiv f x (Algebra.NodeGeometricCompletionOriginalFiberSection.baseResidueMap
      A R (residue A a))) = _
  rw [Algebra.NodeGeometricCompletionOriginalFiberSection.baseResidueMap_residue]
  change (1 : k) ⊗ₜ[A] algebraMap A R a = algebraMap A k a ⊗ₜ[A] (1 : R)
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm

/-- Every original local representative retains its literal residue-tensor class. -/
theorem residueTensorEquiv_mk (r : R) :
    residueTensorEquiv f x (Ideal.Quotient.mk (originalFiberIdeal f x) r) =
      (1 : k) ⊗ₜ[A] r := rfl

/-- The whole selected actual closed-fibre tensor is the SAME original local stalk tensor. -/
def fiberTensorEquiv :
    (L ⊗[k] OriginalFiberRing f x) ≃ₐ[L] (L ⊗[A] R) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (residueTensorEquiv f x)).trans
      (Algebra.TensorProduct.cancelBaseChange A k L L R)

/-- Every original local germ and external coefficient have exactly their literal original image. -/
theorem fiberTensorEquiv_tmul (l : L) (r : R) :
    fiberTensorEquiv f x L (l ⊗ₜ[k] Ideal.Quotient.mk (originalFiberIdeal f x) r) =
      l ⊗ₜ[A] r := by
  change Algebra.TensorProduct.cancelBaseChange A k L L R
    (l ⊗ₜ[k] residueTensorEquiv f x (Ideal.Quotient.mk (originalFiberIdeal f x) r)) = _
  rw [residueTensorEquiv_mk, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

/-- The inverse retains EVERY original local representative as well. -/
theorem fiberTensorEquiv_symm_tmul (l : L) (r : R) :
    (fiberTensorEquiv f x L).symm (l ⊗ₜ[A] r) =
      l ⊗ₜ[k] Ideal.Quotient.mk (originalFiberIdeal f x) r := by
  apply (fiberTensorEquiv f x L).injective
  rw [AlgEquiv.apply_symm_apply, fiberTensorEquiv_tmul]

end Hironaka.Geometry.NodeCompletedLocalSelectedFiberTensor
