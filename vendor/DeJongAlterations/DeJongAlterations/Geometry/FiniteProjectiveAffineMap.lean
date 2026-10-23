import DeJongAlterations.Geometry.UnitIdealBlowup
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingLocal

/-!
# Native projective maps from an affine unit-ideal tuple

The original affine spectrum is identified with its actual unit-ideal Rees
blowup. The genuine generator morphism then gives a projective map. Actual
coefficient naturality and unit-scaling invariance survive this identification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.FiniteProjective

open BlowupProjectiveEmbedding UnitIdealBlowup

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {m : ℕ}

/-- The native projective morphism of an actual tuple generating the unit ideal. -/
def affineTupleMap (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) : Spec (.of A) ⟶ projectiveSpace R m :=
  (unitIdealBlowupIso A).inv ≫ affineProjectiveMap r ⊤ a ha

/-- The actual tuple morphism lies over its original coefficient map. -/
@[reassoc]
theorem affineTupleMap_structure (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    affineTupleMap r a ha ≫ projectiveSpaceStructure R m = Spec.map (CommRingCat.ofHom r) := by
  rw [affineTupleMap, Category.assoc, affineProjectiveMap_structure]
  change (unitIdealBlowupIso A).inv ≫
    (unitIdealBlowupIso A).hom ≫ Spec.map (CommRingCat.ofHom r) = _
  exact (unitIdealBlowupIso A).inv_hom_id_assoc _

/-- Coefficient extension commutes with the literal inverses of the structure isomorphisms. -/
theorem unitIdealBlowupIso_inv_naturality (f : A →+* B) :
    Spec.map (CommRingCat.ofHom f) ≫ (unitIdealBlowupIso A).inv =
      (unitIdealBlowupIso B).inv ≫ affineBlowupMapTo ⊤ ⊤ f (Ideal.map_top f) := by
  apply (cancel_mono (unitIdealBlowupIso A).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  rw [unitIdealBlowupIso_hom, affineBlowupMapTo_structure]
  change Spec.map (CommRingCat.ofHom f) =
    (unitIdealBlowupIso B).inv ≫ (unitIdealBlowupIso B).hom ≫ Spec.map (CommRingCat.ofHom f)
  exact ((unitIdealBlowupIso B).inv_hom_id_assoc _).symm

/-- Actual coefficient extension preserves the native tuple morphism. -/
theorem affineTupleMap_naturality (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (f : A →+* B)
    (hb : Ideal.span (Set.range (fun i => f (a i))) = ⊤) :
    Spec.map (CommRingCat.ofHom f) ≫ affineTupleMap r a ha =
      affineTupleMap (f.comp r) (fun i => f (a i)) hb := by
  rw [affineTupleMap, ← Category.assoc, unitIdealBlowupIso_inv_naturality, Category.assoc]
  congr 1
  exact affineProjectiveMapTo_naturality r ⊤ ⊤ a ha f (Ideal.map_top f) hb

/-- Multiplying the actual tuple by one whole-ring unit preserves its native morphism. -/
theorem affineTupleMap_unit (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (v : Aˣ) :
    affineTupleMap r (fun i => (v : A) * a i) (generator_span_unit ⊤ a ha v) =
      affineTupleMap r a ha := by
  rw [affineTupleMap, affineProjectiveMap_unit]
  rfl

/-- Equality of the actual coefficients and tuple preserves the literal native morphism. -/
theorem affineTupleMap_congr {r s : R →+* A} {a b : Fin (m + 1) → A}
    (hr : r = s) (hab : a = b) (ha : Ideal.span (Set.range a) = ⊤)
    (hb : Ideal.span (Set.range b) = ⊤) : affineTupleMap r a ha = affineTupleMap s b hb := by
  cases hr
  cases hab
  rfl

end DeJongAlterations.Geometry.FiniteProjective
