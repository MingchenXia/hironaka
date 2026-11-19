import Hironaka.Geometry.NodeCompletedLocalSelectedNode
import Hironaka.Geometry.NodeCompletedLocalSelectedTensor

/-! The genuine source geometric node on the SAME actual original-stalk tensor prime. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeCompletedLocalSelectedTensorNode

open NodeCompletedLocalResiduePoint NodeCompletedLocalSelectedAffine
  NodeCompletedLocalSelectedTensor NodeCompletedLocalSelectedNode

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f] (x : X)
  (L : Type u) [Field L] [IsAlgClosed L] [Algebra (X.residueField x) L]

attribute [local instance] NodeCompletedLocalMap.originalAlgebra baseFieldAlgebra

local notation "z" => affinePoint f x L
local notation "q" => pullback.snd f (selectedBaseMap f x L)
local notation "tq" => Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L)))

omit [IsSemistableCurve f] [IsAlgClosed L] in
/-- The SAME actual tensor point is the actual affine point under the SAME native tensor isomorphism. -/
theorem selectedTensorPoint_eq :
    tensorPoint f x L = (tensorIso f x L).hom (affinePoint f x L) := rfl

/-- The genuine source node model, at precisely the SAME image of the chosen affine point. -/
def geometricModelAtAffinePoint
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
    (SelectedFiber f x L).completedLocalRing (affineMap f x L z) ≃ₐ[L]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV L := by
  let P (y : SelectedFiber f x L) :=
    letI := Scheme.completedLocalRingAlgebra q y
    (SelectedFiber f x L).completedLocalRing y ≃ₐ[L]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV L
  have hP : P (selectedPoint f x L) := selectedNodeModel f x L hx
  exact Eq.mp (congrArg P (affinePoint_geometric f x L).symm) hP

/-- Actual semistability produces the genuine uv model on the SAME original-stalk tensor prime. -/
def tensorNodeModel
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    letI := Scheme.completedLocalRingAlgebra tq (tensorPoint f x L)
    (Spec (.of (TensorRing f x L))).completedLocalRing (tensorPoint f x L) ≃ₐ[L]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV L := by
  letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
  letI := Scheme.completedLocalRingAlgebra tq ((tensorIso f x L).hom z)
  change (Spec (.of (TensorRing f x L))).completedLocalRing ((tensorIso f x L).hom z) ≃ₐ[L] _
  exact (geometricTensorCompletedEquiv f x L z).symm.trans (geometricModelAtAffinePoint f x L hx)

/-- The ENTIRE transported source model triangle holds for EVERY completed geometric germ. -/
theorem tensorNodeModel_triangle
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support)
    (c : (SelectedFiber f x L).completedLocalRing (affineMap f x L z)) :
    letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra tq (tensorPoint f x L)
    tensorNodeModel f x L hx (geometricTensorCompletedEquiv f x L z c) =
      geometricModelAtAffinePoint f x L hx c := by
  let := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
  let := Scheme.completedLocalRingAlgebra tq (tensorPoint f x L)
  let := Scheme.completedLocalRingAlgebra tq ((tensorIso f x L).hom z)
  change geometricModelAtAffinePoint f x L hx
    ((geometricTensorCompletedEquiv f x L z).symm (geometricTensorCompletedEquiv f x L z c)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- BOTH original uv coordinates retain the SAME actual geometric-to-tensor preimages. -/
theorem tensorNodeModel_coordinate
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) (i : Fin 2) :
    letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra tq (tensorPoint f x L)
    tensorNodeModel f x L hx
      (geometricTensorCompletedEquiv f x L z
        ((geometricModelAtAffinePoint f x L hx).symm
          (Algebra.NodeGeometricCompletionFormalUV.coordinate L i))) =
      Algebra.NodeGeometricCompletionFormalUV.coordinate L i := by
  let := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
  let := Scheme.completedLocalRingAlgebra tq (tensorPoint f x L)
  rw [tensorNodeModel_triangle, AlgEquiv.apply_symm_apply]

end Hironaka.Geometry.NodeCompletedLocalSelectedTensorNode
