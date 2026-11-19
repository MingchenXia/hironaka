import Hironaka.Geometry.ProjectiveSpaceBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The scalar projection retains the canonical original scalar source and literal whole triangles
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveSpaceBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The entire actual native projective coefficient map is universally open over every original field. -/
theorem projectiveCoefficientMap_universallyOpen
    (k L : Type u) [Field k] [CommRing L] (φ : k →+* L) (n : ℕ) :
    UniversallyOpen (projectiveCoefficientMap φ n) :=
  MorphismProperty.of_isPullback (isPullback_projectiveCoefficientMap φ n).flip inferInstance

variable (k L : Type u) [CommRing k] [CommRing L] (φ : k →+* L) (n : ℕ)
  {X : Scheme.{u}} (f : X ⟶ projectiveSpace k n) (pX : X ⟶ Spec (CommRingCat.of k))
  (ht : f ≫ projectiveSpaceStructure k n = pX)

include ht

/-- The original whole field triangle pastes the SAME native projection pullback with the actual whole projective coefficient square. -/
theorem originalProjection_scalar_isPullback :
    IsPullback (pullback.fst f (projectiveCoefficientMap φ n))
      (pullback.snd f (projectiveCoefficientMap φ n) ≫ projectiveSpaceStructure L n)
      pX (Spec.map (CommRingCat.ofHom φ)) := by
  have h := (IsPullback.of_hasPullback f (projectiveCoefficientMap φ n)).paste_vert
    (isPullback_projectiveCoefficientMap φ n)
  rwa [ht] at h

/-- The actual native universal property internally supplies the source isomorphism onto the canonical scalar pullback of the SAME original source. -/
def originalProjectionScalarSourceIso :
    pullback f (projectiveCoefficientMap φ n) ≅ pullback pX (Spec.map (CommRingCat.ofHom φ)) :=
  (originalProjection_scalar_isPullback k L φ n f pX ht).isoPullback

/-- The whole original source projection is literally retained. -/
theorem originalProjectionScalarSourceIso_hom_fst :
    (originalProjectionScalarSourceIso k L φ n f pX ht).hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) =
      pullback.fst f (projectiveCoefficientMap φ n) :=
  (originalProjection_scalar_isPullback k L φ n f pX ht).isoPullback_hom_fst

/-- The entire actual new coefficient structure is literally retained. -/
theorem originalProjectionScalarSourceIso_hom_snd :
    (originalProjectionScalarSourceIso k L φ n f pX ht).hom ≫ pullback.snd pX (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd f (projectiveCoefficientMap φ n) ≫ projectiveSpaceStructure L n :=
  (originalProjection_scalar_isPullback k L φ n f pX ht).isoPullback_hom_snd

/-- The actual scalar projection on the canonical scalar pullback of the SAME original source. -/
def originalProjectionScalar : pullback pX (Spec.map (CommRingCat.ofHom φ)) ⟶ projectiveSpace L n :=
  (originalProjectionScalarSourceIso k L φ n f pX ht).inv ≫ pullback.snd f (projectiveCoefficientMap φ n)

/-- The actual original scalar projection retains its literal entire new coefficient triangle. -/
theorem originalProjectionScalar_structure :
    originalProjectionScalar k L φ n f pX ht ≫ projectiveSpaceStructure L n =
      pullback.snd pX (Spec.map (CommRingCat.ofHom φ)) := by
  let e := originalProjectionScalarSourceIso k L φ n f pX ht
  have he := congrArg (fun m => e.inv ≫ m) (originalProjectionScalarSourceIso_hom_snd k L φ n f pX ht)
  change e.inv ≫ (e.hom ≫ pullback.snd pX (Spec.map (CommRingCat.ofHom φ))) =
    e.inv ≫ (pullback.snd f (projectiveCoefficientMap φ n) ≫ projectiveSpaceStructure L n) at he
  change (e.inv ≫ pullback.snd f (projectiveCoefficientMap φ n)) ≫ projectiveSpaceStructure L n = _
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using he.symm

/-- The actual original scalar projection retains the literal entire original projection triangle. -/
theorem originalProjectionScalar_original :
    originalProjectionScalar k L φ n f pX ht ≫ projectiveCoefficientMap φ n =
      pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) ≫ f := by
  let e := originalProjectionScalarSourceIso k L φ n f pX ht
  have he := congrArg (fun m => e.inv ≫ m) (originalProjectionScalarSourceIso_hom_fst k L φ n f pX ht)
  change e.inv ≫ (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom φ))) =
    e.inv ≫ pullback.fst f (projectiveCoefficientMap φ n) at he
  have hi : e.inv ≫ pullback.fst f (projectiveCoefficientMap φ n) =
      pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) := by
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using he.symm
  change (e.inv ≫ pullback.snd f (projectiveCoefficientMap φ n)) ≫ projectiveCoefficientMap φ n = _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hi]

end Hironaka.Geometry.ProjectiveSecant
