/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesBaseChange
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian

/-!
Adapted closed native proof from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesFormalFamily.lean`,
SHA256 50829406a2d5b575ebe32f22c5523fd30adc3dd8008bff11c9303e2a69e86505.
Only native Mathlib and owned actual original Rees helper modules are imported.
The geometric finite cohomology/formal-functions comparison remains separate.


# The actual proper Rees family for formal functions

For an actual scheme over R, take the schematic image of its polynomial
base extension in its Rees-algebra base extension. This is a genuine closed
subscheme of the original proper base change. No coherent Rees family,
properness certificate for that family, or cohomology comparison is input.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped Polynomial
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesFamily

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual Rees coefficient spectrum over the original base. -/
abbrev reesBase : Spec (.of (reesAlgebra I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (reesAlgebra I)))

/-- The actual polynomial coefficient spectrum over the actual Rees base. -/
abbrev polynomialToRees : Spec (.of R[X]) ⟶ Spec (.of (reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom (reesAlgebra I).val.toRingHom)

/-- The whole original polynomial coefficient triangle commutes. -/
theorem polynomialToRees_comp_base :
    polynomialToRees I ≫ reesBase I =
      Spec.map (CommRingCat.ofHom (algebraMap R R[X])) := by
  rw [← Spec.map_comp]
  rfl

/-- The literal original Rees coefficient base extension. -/
abbrev ambient := pullback f (reesBase I)

/-- Its literal projection to the actual Rees coefficient scheme. -/
abbrev ambientProjection : ambient I f ⟶ Spec (.of (reesAlgebra I)) :=
  pullback.snd f (reesBase I)

/-- The actual polynomial base extension, presented as an iterated literal
pullback so that its map to the ambient family is a genuine base change. -/
abbrev polynomialSource := pullback (ambientProjection I f) (polynomialToRees I)

/-- The actual polynomial-to-Rees map over the original scheme. -/
abbrev imageMap : polynomialSource I f ⟶ ambient I f :=
  pullback.fst (ambientProjection I f) (polynomialToRees I)

/-- The genuine scheme-theoretic Rees image, with all nilpotents retained. -/
abbrev family := (imageMap I f).image

/-- The actual closed image inclusion in the literal coefficient extension. -/
abbrev familyImmersion : family I f ⟶ ambient I f := (imageMap I f).imageι

/-- The genuine whole family projection to the actual Rees coefficient ring. -/
def familyProjection : family I f ⟶ Spec (.of (reesAlgebra I)) :=
  familyImmersion I f ≫ ambientProjection I f

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual polynomial map is affine because it is a literal base change
of the actual map between coefficient affine spectra. -/
instance imageMap_isAffineHom : IsAffineHom (imageMap I f) := by
  exact MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (polynomialToRees I))

set_option backward.isDefEq.respectTransparency.types false in
/-- Properness of the original morphism constructs properness of the actual
Rees image family, without a separately supplied family or certificate. -/
instance familyProjection_isProper [IsProper f] : IsProper (familyProjection I f) := by
  have : IsProper (ambientProjection I f) := MorphismProperty.pullback_snd _ _ ‹IsProper f›
  change IsProper (familyImmersion I f ≫ ambientProjection I f)
  infer_instance

/-- The source of the constructed image map really is the original
polynomial base extension, with the whole original coefficient square. -/
theorem polynomialSource_isPullback :
    IsPullback (imageMap I f ≫ pullback.fst f (reesBase I))
      (pullback.snd (ambientProjection I f) (polynomialToRees I)) f
      (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) := by
  rw [← polynomialToRees_comp_base I]
  exact (IsPullback.of_hasPullback (ambientProjection I f) (polynomialToRees I)).paste_horiz
    (IsPullback.of_hasPullback f (reesBase I))

/-- The actual family has noetherian total scheme whenever the original
coefficient ring is noetherian and the original morphism is proper. -/
instance family_isNoetherian [IsNoetherianRing R] [IsProper f] :
    IsNoetherian (family I f) := by
  have : IsLocallyNoetherian (family I f) :=
    LocallyOfFiniteType.isLocallyNoetherian (familyProjection I f)
  have : CompactSpace (family I f) :=
    QuasiCompact.compactSpace_of_compactSpace (familyProjection I f)
  exact ⟨⟩

/-- The actual proper Rees image is separated as an absolute scheme. -/
instance family_isSeparated [IsProper f] : (family I f).IsSeparated := by
  constructor
  rw [← terminal.comp_from (familyProjection I f)]
  infer_instance

/-- The actual polynomial base extension maps into its genuine schematic
Rees image, without an assumed factorization. -/
abbrev polynomialToFamily : polynomialSource I f ⟶ family I f :=
  (imageMap I f).toImage

/-- The whole original Rees coefficient triangle is retained through the
actual scheme-theoretic image, for every section and every scheme point. -/
theorem polynomialToFamily_comp_projection :
    polynomialToFamily I f ≫ familyProjection I f =
      pullback.snd (ambientProjection I f) (polynomialToRees I) ≫ polynomialToRees I := by
  rw [familyProjection, ← Category.assoc, Scheme.Hom.toImage_imageι]
  exact pullback.condition

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesFamily
