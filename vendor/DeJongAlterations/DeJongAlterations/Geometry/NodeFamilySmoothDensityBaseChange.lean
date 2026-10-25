import DeJongAlterations.Geometry.NodeFamilySmoothDensity

/-! Actual structure triangles and dense native smooth loci after node field base change. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace DeJongAlterations.Geometry.NodeFamilySmoothDensityBaseChange

open Algebra.NodeBlowupChart Algebra.NodeFamilyBaseChange
open NodeFamilyFlat NodeFamilyGeometricPurity NodeFamilySmoothDensity

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native spectrum isomorphisms of actual algebra equivalences preserve their original coefficient maps. -/
theorem specAlgEquiv_structure {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) :
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R T)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext e.symm.commutes

/-- Equality of actual morphisms identifies their native smooth loci independently of the proof instances. -/
theorem smoothLocus_eq_of_eq {X S : Scheme.{u}} (f g : X ⟶ S)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  subst g
  rfl

variable {A : Type u} [CommRing A] (K : Type u) [Field K] [Algebra A K]

/-- The actual coefficient projection of the genuine field base change. -/
def fieldBaseChangeMorphism (t : A) : nodeFieldBaseChange K t ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (nodeMorphism t) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

/-- The genuine node field-basechange isomorphism preserves the actual field structure map. -/
theorem nodeFieldBaseChangeIso_structure (t : A) :
    (nodeFieldBaseChangeIso K t).hom ≫ nodeMorphism (algebraMap A K t) =
      fieldBaseChangeMorphism K t := by
  have h := specAlgEquiv_structure (R := K) (S := K ⊗[A] Node A t)
    (T := Node K (algebraMap A K t)) (nodeBaseChangeEquiv K t)
  dsimp only [nodeFieldBaseChangeIso, Iso.trans_hom, nodeMorphism, fieldBaseChangeMorphism]
  rw [Category.assoc, Category.assoc, h, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

local instance (t : A) : LocallyOfFinitePresentation (nodeMorphism t) :=
  nodeMorphism_locallyOfFinitePresentation t

instance fieldBaseChangeMorphism_locallyOfFinitePresentation (t : A) :
    LocallyOfFinitePresentation (fieldBaseChangeMorphism K t) := by
  dsimp only [fieldBaseChangeMorphism]
  infer_instance

/-- The actual native field-basechanged coefficient morphism has dense relative smooth locus. -/
theorem fieldBaseChangeMorphism_smoothLocus_dense (t : A) :
    Dense ((fieldBaseChangeMorphism K t).smoothLocus : Set (nodeFieldBaseChange K t)) := by
  let : LocallyOfFinitePresentation (nodeMorphism (algebraMap A K t)) :=
    nodeMorphism_locallyOfFinitePresentation _
  have h := Scheme.Hom.preimage_smoothLocus_eq (nodeFieldBaseChangeIso K t).hom
    (nodeMorphism (algebraMap A K t))
  have heq := h.trans (smoothLocus_eq_of_eq _ _ (nodeFieldBaseChangeIso_structure K t))
  rw [← heq]
  exact (nodeMorphism_smoothLocus_dense K _).preimage
    (nodeFieldBaseChangeIso K t).hom.isOpenEmbedding.isOpenMap

end DeJongAlterations.Geometry.NodeFamilySmoothDensityBaseChange
