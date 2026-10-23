import DeJongAlterations.Algebra.NodeFamilyBaseChange
import DeJongAlterations.Geometry.NodeFamilySmooth
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! Actual scheme-theoretic node fibres and native geometric reducedness of the coefficient morphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace DeJongAlterations.Geometry.NodeFamilyFibres

open Algebra.NodeBlowupChart Algebra.NodeFamilyBaseChange NodeFamilyFlat

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The actual scheme-theoretic fibre is the literal node over the actual residue field. -/
def nodeFiberIso (t : A) (p : PrimeSpectrum A) :
    (nodeMorphism t).fiber p ≅
      Spec (CommRingCat.of (Node p.asIdeal.ResidueField (algebraMap A p.asIdeal.ResidueField t))) :=
  (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso A (Node A t) p)) ≪≫
    Scheme.Spec.mapIso (nodeBaseChangeEquiv p.asIdeal.ResidueField t).toRingEquiv.toCommRingCatIso.symm.op

/-- The literal node family has geometrically reduced actual fibres over every coefficient base. -/
theorem nodeMorphism_geometricallyReduced (t : A) : GeometricallyReduced (nodeMorphism t) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let : _root_.IsReduced (K ⊗[A] Node A t) := fieldBaseChange_isReduced K t
  let e : pullback (nodeMorphism t) (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≅
      Spec (CommRingCat.of (K ⊗[A] Node A t)) :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso A K (Node A t)
  exact isReduced_of_isOpenImmersion e.hom

/-- Each literal native fibre is reduced, derived from the genuine geometric morphism property. -/
theorem nodeFiber_isReduced (t : A) (p : PrimeSpectrum A) : IsReduced ((nodeMorphism t).fiber p) := by
  let : GeometricallyReduced (nodeMorphism t) := nodeMorphism_geometricallyReduced t
  infer_instance

end DeJongAlterations.Geometry.NodeFamilyFibres
