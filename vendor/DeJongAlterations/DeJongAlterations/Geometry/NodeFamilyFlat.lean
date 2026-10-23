import DeJongAlterations.Algebra.NodeFamilyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! Native family properties of the literal node coefficient morphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NodeFamilyFlat

open Algebra.NodeBlowupChart

universe u

variable {A : Type u} [CommRing A]

/-- The literal coefficient morphism of the actual node quotient. -/
def nodeMorphism (t : A) :
    Spec (CommRingCat.of (Node A t)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Node A t)))

/-- The actual node family is flat over every commutative coefficient ring. -/
theorem nodeMorphism_flat (t : A) : Flat (nodeMorphism t) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (Algebra.NodeFamilyFlat.node_flat t)

/-- The literal node family is locally of finite presentation without any Noetherian hypothesis. -/
theorem nodeMorphism_locallyOfFinitePresentation (t : A) :
    LocallyOfFinitePresentation (nodeMorphism t) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr (Algebra.NodeFamilyFlat.node_finitePresentation t)

/-- These native affine family morphisms are quasi-compact. -/
theorem nodeMorphism_quasiCompact (t : A) : QuasiCompact (nodeMorphism t) := by
  dsimp only [nodeMorphism]
  infer_instance

/-- Genuine flatness and finite presentation of the actual node morphism. -/
theorem nodeMorphism_flat_finitelyPresented (t : A) :
    Flat (nodeMorphism t) ∧ LocallyOfFinitePresentation (nodeMorphism t) ∧
      QuasiCompact (nodeMorphism t) :=
  ⟨nodeMorphism_flat t, nodeMorphism_locallyOfFinitePresentation t, nodeMorphism_quasiCompact t⟩

end DeJongAlterations.Geometry.NodeFamilyFlat
