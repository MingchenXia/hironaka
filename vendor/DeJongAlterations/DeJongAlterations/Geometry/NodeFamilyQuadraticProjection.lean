import DeJongAlterations.Geometry.NodeFamilyFlat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The actual flat quadratic projection of a node

The coefficient variable is literally the sum of the two original node coordinates.
The monic presentation works over every commutative ring and in all characteristics.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace DeJongAlterations.Geometry.NodeFamilyQuadraticProjection

open Algebra.NodeBlowupChart Algebra.NodeFamilyQuadratic

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The literal coefficient map sending the new variable to the sum of node coordinates. -/
def projectionRingHom (t : A) : A[X] →+* Node A t :=
  (quadraticEquiv t).symm.toRingHom.comp (algebraMap A[X] (QuadraticAlgebra t))

/-- Its variable is the actual sum of the original node coordinates. -/
theorem projectionRingHom_X (t : A) :
    projectionRingHom t X = coordinate t 0 + coordinate t 1 := by
  apply (quadraticEquiv t).injective
  change quadraticEquiv t ((quadraticEquiv t).symm
    (algebraMap A[X] (QuadraticAlgebra t) X)) = _
  rw [AlgEquiv.apply_symm_apply, map_add]
  change sumCoordinate t = forward t (coordinate t 0) + forward t (coordinate t 1)
  rw [forward_coordinate0, forward_coordinate1]
  ring

/-- The actual coefficient projection of the original node scheme. -/
def quadraticProjection (t : A) :
    Spec (CommRingCat.of (Node A t)) ⟶ Spec (CommRingCat.of A[X]) :=
  Spec.map (CommRingCat.ofHom (projectionRingHom t))

/-- The genuine spectrum isomorphism induced by the actual monic quadratic presentation. -/
def quadraticSchemeIso (t : A) :
    Spec (CommRingCat.of (Node A t)) ≅ Spec (CommRingCat.of (QuadraticAlgebra t)) :=
  Scheme.Spec.mapIso (quadraticEquiv t).toRingEquiv.toCommRingCatIso.symm.op

/-- The quadratic presentation preserves the literal coefficient projection. -/
theorem quadraticProjection_eq (t : A) :
    quadraticProjection t = (quadraticSchemeIso t).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A[X] (QuadraticAlgebra t))) := by
  change Spec.map (CommRingCat.ofHom (projectionRingHom t)) =
    Spec.map (CommRingCat.ofHom (quadraticEquiv t).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A[X] (QuadraticAlgebra t)))
  rw [← Spec.map_comp]
  rfl

/-- The literal quadratic projection is genuinely flat over every commutative ring. -/
theorem quadraticProjection_flat (t : A) : Flat (quadraticProjection t) := by
  let : Module.Free A[X] (QuadraticAlgebra t) := (quadratic_monic t).free_adjoinRoot
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap A[X] (QuadraticAlgebra t)))) := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  rw [quadraticProjection_eq]
  infer_instance

/-- Its actual finite presentation follows from the single literal quadratic relation. -/
theorem quadraticProjection_locallyOfFinitePresentation (t : A) :
    LocallyOfFinitePresentation (quadraticProjection t) := by
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap A[X] (QuadraticAlgebra t)))) := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  rw [quadraticProjection_eq]
  infer_instance

/-- The actual quadratic projection is open, including for zero parameters and in characteristic two. -/
theorem quadraticProjection_isOpenMap (t : A) : IsOpenMap (quadraticProjection t) := by
  let : Flat (quadraticProjection t) := quadraticProjection_flat t
  let : LocallyOfFinitePresentation (quadraticProjection t) :=
    quadraticProjection_locallyOfFinitePresentation t
  exact (quadraticProjection t).isOpenMap

end DeJongAlterations.Geometry.NodeFamilyQuadraticProjection
