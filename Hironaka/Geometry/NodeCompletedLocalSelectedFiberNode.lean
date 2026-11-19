import Hironaka.Geometry.NodeCompletedLocalSelectedFiberGeometric
import Hironaka.Geometry.NodeCompletedLocalSpecLocalization
import Hironaka.Geometry.NodeCompletedLocalSelectedTensorNode

/-! The genuine source geometric node on the SAME original closed-fibre and diagonal geometric completion. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalSelectedFiberNode

open NodeCompletedLocalMap NodeCompletedLocalResiduePoint NodeCompletedLocalSelectedAffine
  NodeCompletedLocalSelectedFiberTensor NodeCompletedLocalSelectedFiberGeometric
  NodeCompletedLocalSelectedTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

attribute [local instance] originalAlgebra baseFieldAlgebra originalBaseAlgebra
  originalFiberResidueAlgebra NodeCompletedLocalSelectedFiberTensor.baseResidueAlgebra
  NodeCompletedLocalSelectedFiberTensor.original_scalarTower
  Algebra.TensorProduct.rightAlgebra quotientPoint_isMaximal

local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "k" => S.residueField (f x)
local notation "Q" => OriginalFiberRing f x
local notation "D" => NodeCompletedLocalSelectedTensor.TensorRing f x L
local notation "p" => NodeCompletedLocalSelectedTensor.tensorPoint f x L
local notation "H" => QuotientGeometricStalk f x L
local notation "T" => Localization.AtPrime (p).asIdeal
local notation "tq" => Spec.map (CommRingCat.ofHom (algebraMap L D))

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

local instance quotientGeometricCommRing : CommRing H := inferInstance
local instance tensorGeometricCommRing : CommRing T := inferInstance

local instance actualStalkEquivLocal : IsLocalHom (stalkEquiv f x L).toRingHom :=
  Algebra.CompletionLocalMap.instIsLocalHomRingEquivToRingHom (stalkEquiv f x L).toRingEquiv

/-- Complete the SAME original closed-fibre selected-stalk equivalence over the WHOLE actual external field. -/
def completedStalkEquiv :
    AdicCompletion (maximalIdeal H) H ≃ₐ[L] AdicCompletion (maximalIdeal T) T := by
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv (stalkEquiv f x L).toRingEquiv) ?_
  intro l
  change Algebra.CompletionLocalMap.completionMap (stalkEquiv f x L).toRingHom
    (algebraMap H (AdicCompletion _ _) (algebraMap L H l)) = _
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap T (AdicCompletion (maximalIdeal T) T)) ((stalkEquiv f x L).commutes l)

/-- The WHOLE completed forward map is exactly the native completion of the SAME selected closed-fibre stalk map. -/
theorem completedStalkEquiv_toRingHom :
    (completedStalkEquiv f x L).toRingHom =
      Algebra.CompletionLocalMap.completionMap (stalkEquiv f x L).toRingHom := rfl

/-- EVERY actual original closed-fibre geometric germ retains its SAME completion image. -/
theorem completedStalkEquiv_original (h : H) :
    completedStalkEquiv f x L (algebraMap H (AdicCompletion _ _) h) =
      algebraMap T (AdicCompletion _ _) (stalkEquiv f x L h) :=
  Algebra.CompletionLocalMap.completionMap_algebraMap (stalkEquiv f x L).toRingHom h

variable [IsSemistableCurve f] [IsAlgClosed L]

/-- The genuine SOURCE geometric node on the SAME actual original closed-fibre selected stalk completion. -/
def quotientNodeModel
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    AdicCompletion (maximalIdeal H) H ≃ₐ[L]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV L := by
  letI := Scheme.stalkAlgebra tq p
  letI := Scheme.completedLocalRingAlgebra tq p
  exact (completedStalkEquiv f x L).trans
    ((NodeCompletedLocalSpecLocalization.completedEquiv L D p).symm.trans
      (NodeCompletedLocalSelectedTensorNode.tensorNodeModel f x L hx))

/-- This is exactly the original-Q geometric augmentation-kernel completion used in the actual diagonal comparison. -/
def originalGeometricNodeModel
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    letI := selectedQuotientPointAlgebra f x L
    letI := selectedQuotientPoint_scalarTower f x L
    AdicCompletion
      (maximalIdeal (Algebra.NodeGeometricCompletionDiagonalGeometric.OriginalGeometricStalk k Q L))
      (Algebra.NodeGeometricCompletionDiagonalGeometric.OriginalGeometricStalk k Q L) ≃ₐ[L]
        Algebra.NodeGeometricCompletionFormalUV.FormalUV L := by
  letI := selectedQuotientPointAlgebra f x L
  letI := selectedQuotientPoint_scalarTower f x L
  exact quotientNodeModel f x L hx

/-- The genuine SOURCE node model on the SAME actual diagonal geometric completion, with no model input. -/
def diagonalNodeModel
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    letI := selectedQuotientPointAlgebra f x L
    letI := selectedQuotientPoint_scalarTower f x L
    AdicCompletion
      (maximalIdeal (Algebra.NodeGeometricCompletionDiagonalGeometric.DiagonalGeometricStalk k Q L))
      (Algebra.NodeGeometricCompletionDiagonalGeometric.DiagonalGeometricStalk k Q L) ≃ₐ[L]
        Algebra.NodeGeometricCompletionFormalUV.FormalUV L := by
  letI := selectedQuotientPointAlgebra f x L
  letI := selectedQuotientPoint_scalarTower f x L
  exact (Algebra.NodeGeometricCompletionDiagonalGeometric.completedGeometricStalkEquiv k Q L).symm.trans
    (originalGeometricNodeModel f x L hx)

/-- The ENTIRE actual completed geometric transport triangle, for EVERY completed original-Q geometric germ. -/
theorem diagonalNodeModel_triangle
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support)
    (c : AdicCompletion (maximalIdeal H) H) :
    letI := selectedQuotientPointAlgebra f x L
    letI := selectedQuotientPoint_scalarTower f x L
    diagonalNodeModel f x L hx
      (Algebra.NodeGeometricCompletionDiagonalGeometric.completedGeometricStalkEquiv k Q L c) =
        originalGeometricNodeModel f x L hx c := by
  let := selectedQuotientPointAlgebra f x L
  let := selectedQuotientPoint_scalarTower f x L
  change originalGeometricNodeModel f x L hx
    ((Algebra.NodeGeometricCompletionDiagonalGeometric.completedGeometricStalkEquiv k Q L).symm
      (Algebra.NodeGeometricCompletionDiagonalGeometric.completedGeometricStalkEquiv k Q L c)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- BOTH literal model coordinates have the SAME actual completed geometric preimages. -/
theorem diagonalNodeModel_coordinate
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) (i : Fin 2) :
    letI := selectedQuotientPointAlgebra f x L
    letI := selectedQuotientPoint_scalarTower f x L
    diagonalNodeModel f x L hx
      (Algebra.NodeGeometricCompletionDiagonalGeometric.completedGeometricStalkEquiv k Q L
        ((originalGeometricNodeModel f x L hx).symm
          (Algebra.NodeGeometricCompletionFormalUV.coordinate L i))) =
      Algebra.NodeGeometricCompletionFormalUV.coordinate L i := by
  let := selectedQuotientPointAlgebra f x L
  let := selectedQuotientPoint_scalarTower f x L
  rw [diagonalNodeModel_triangle, AlgEquiv.apply_symm_apply]

end Hironaka.Geometry.NodeCompletedLocalSelectedFiberNode
