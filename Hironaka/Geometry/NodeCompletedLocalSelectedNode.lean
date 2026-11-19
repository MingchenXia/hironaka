import Hironaka.Geometry.NodeCompletedLocalResiduePoint
import Hironaka.Geometry.SemistableSingularFinite
import Hironaka.Algebra.NodeFittingSupportPullback

/-! The genuine geometric completed uv node at the SAME prescribed original Sing point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeCompletedLocalSelectedNode

open NodeCompletedLocalResiduePoint NodeCompletedLocalGeometricChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f] (x : X)
  (L : Type u) [Field L] [IsAlgClosed L] [Algebra (X.residueField x) L]

/-- The SAME actual selected point over an ORIGINAL Sing support point is not geometrically smooth. -/
theorem selectedPoint_not_smooth
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    selectedPoint f x L ∉ (pullback.snd f (selectedBaseMap f x L)).smoothLocus := by
  let := originalBaseAlgebra f x L
  have H : ∀ y : SelectedFiber f x L,
      pullback.fst f (selectedBaseMap f x L) y ∈
        (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support →
      y ∉ (pullback.snd f (selectedBaseMap f x L)).smoothLocus := by
    let P (a : Spec (.of L) ⟶ S) : Prop := ∀ y : pullback (C := Scheme.{u}) f a,
      pullback.fst f a y ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support →
        y ∉ (pullback.snd f a).smoothLocus
    have hP : P (originalFieldMap (f x) L) :=
      Algebra.NodeFittingSupportPullback.geometric_not_smooth_of_original_mem_support
        f (f x) L (SemistableCurve.geometricFiber_dimension_le_one f L (originalFieldMap (f x) L))
    exact Eq.mp (congrArg P (selectedBaseMap_eq_originalFieldMap f x L).symm) hP
  apply H
  simpa only [selectedPoint_source] using hx

/-- Actual semistability now forces the geometric uv model at the SAME prescribed original singular point. -/
theorem selectedPoint_ordinaryDoublePoint
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    IsGeometricOrdinaryDoublePoint (pullback.snd f (selectedBaseMap f x L))
      (selectedPoint f x L) := by
  rcases IsSemistableCurve.geometricNodes L (selectedBaseMap f x L) (selectedPoint f x L)
    (selectedPoint_isClosed f x L) with hs | hn
  · exact False.elim (selectedPoint_not_smooth f x L hx hs)
  · exact hn

/-- A genuine actual completed-local model, produced internally at the SAME chosen geometric point. -/
def selectedNodeModel
    (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support) :
    letI := Scheme.completedLocalRingAlgebra (pullback.snd f (selectedBaseMap f x L))
      (selectedPoint f x L)
    (SelectedFiber f x L).completedLocalRing (selectedPoint f x L) ≃ₐ[L]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV L :=
  (selectedPoint_ordinaryDoublePoint f x L hx).some

end Hironaka.Geometry.NodeCompletedLocalSelectedNode
