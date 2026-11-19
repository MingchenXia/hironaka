import Hironaka.Geometry.ProjectiveSecantProjectionFlatImage
import Hironaka.Geometry.ProjectiveSecantProjectionScalar

/-!
# The actual native scheme image of the SAME canonical-source scalar projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveSpaceBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual whole projective coefficient map is flat by its genuine native field-coefficient Cartesian square. -/
theorem projectiveCoefficientMap_flat
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ) :
    Flat (projectiveCoefficientMap φ n) :=
  MorphismProperty.of_isPullback (isPullback_projectiveCoefficientMap φ n).flip inferInstance

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  {X : Scheme.{u}} (f : X ⟶ projectiveSpace k n) (pX : X ⟶ Spec (CommRingCat.of k))
  (ht : f ≫ projectiveSpaceStructure k n = pX)

/-- The whole actual native source factor on the canonical scalar pullback of the SAME original source. -/
def originalProjectionScalarImageFactor :
    pullback pX (Spec.map (CommRingCat.ofHom φ)) ⟶ pullback (projectiveCoefficientMap φ n) f.imageι :=
  (originalProjectionScalarSourceIso k L φ n f pX ht).inv ≫ baseChangeImageFactor f (projectiveCoefficientMap φ n)

/-- The actual whole scalar projection is exactly this actual source factor followed by the actual pulled-back original image embedding. -/
theorem originalProjectionScalarImageFactor_embedding :
    originalProjectionScalarImageFactor k L φ n f pX ht ≫ pullback.fst (projectiveCoefficientMap φ n) f.imageι =
      originalProjectionScalar k L φ n f pX ht := by
  rw [originalProjectionScalarImageFactor, Category.assoc, baseChangeImageFactor_fst]
  rfl

/-- The entire actual original image factor is schematically dominant after actual scalar extension, without a supplied image or kernel certificate. -/
theorem originalProjectionScalarImageFactor_isSchemeTheoreticallyDominant [QuasiCompact f] :
    IsSchemeTheoreticallyDominant (originalProjectionScalarImageFactor k L φ n f pX ht) := by
  let : Flat (projectiveCoefficientMap φ n) := projectiveCoefficientMap_flat k L φ n
  let := baseChangeImageFactor_isSchemeTheoreticallyDominant f (projectiveCoefficientMap φ n)
  dsimp only [originalProjectionScalarImageFactor]
  infer_instance

/-- The actual native image of the SAME scalar projection on the canonical scalar source is the actual scalar pullback of the SAME original native image embedding. -/
def originalProjectionScalarImageIso [QuasiCompact f] :
    (originalProjectionScalar k L φ n f pX ht).image ≅ pullback (projectiveCoefficientMap φ n) f.imageι := by
  let := originalProjectionScalarImageFactor_isSchemeTheoreticallyDominant k L φ n f pX ht
  exact imageIsoOfClosedFactor (originalProjectionScalar k L φ n f pX ht)
    (pullback.fst (projectiveCoefficientMap φ n) f.imageι)
    (originalProjectionScalarImageFactor k L φ n f pX ht)
    (originalProjectionScalarImageFactor_embedding k L φ n f pX ht)

/-- The actual scalar native-image isomorphism preserves the literal whole original closed embedding after scalar extension. -/
theorem originalProjectionScalarImageIso_hom_embedding [QuasiCompact f] :
    (originalProjectionScalarImageIso k L φ n f pX ht).hom ≫ pullback.fst (projectiveCoefficientMap φ n) f.imageι =
      (originalProjectionScalar k L φ n f pX ht).imageι := by
  let := originalProjectionScalarImageFactor_isSchemeTheoreticallyDominant k L φ n f pX ht
  exact imageIsoOfClosedFactor_hom_embedding (originalProjectionScalar k L φ n f pX ht)
    (pullback.fst (projectiveCoefficientMap φ n) f.imageι)
    (originalProjectionScalarImageFactor k L φ n f pX ht)
    (originalProjectionScalarImageFactor_embedding k L φ n f pX ht)

/-- The actual scalar native-image isomorphism preserves the literal entire original source image factor after scalar extension. -/
theorem toImage_originalProjectionScalarImageIso_hom [QuasiCompact f] :
    (originalProjectionScalar k L φ n f pX ht).toImage ≫
      (originalProjectionScalarImageIso k L φ n f pX ht).hom =
        originalProjectionScalarImageFactor k L φ n f pX ht := by
  let := originalProjectionScalarImageFactor_isSchemeTheoreticallyDominant k L φ n f pX ht
  exact toImage_imageIsoOfClosedFactor_hom (originalProjectionScalar k L φ n f pX ht)
    (pullback.fst (projectiveCoefficientMap φ n) f.imageι)
    (originalProjectionScalarImageFactor k L φ n f pX ht)
    (originalProjectionScalarImageFactor_embedding k L φ n f pX ht)

end Hironaka.Geometry.ProjectiveSecant
