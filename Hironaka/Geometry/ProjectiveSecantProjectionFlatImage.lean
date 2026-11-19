import Hironaka.Geometry.ProjectiveSecantProjectionImageFactorIso

/-!
# Actual native scheme images of the same original quasi-compact morphism commute with flat base change
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The SAME entire original image triangle internally constructs the actual native base-changed source factor through the actual original image pullback. -/
def baseChangeImageFactor : pullback f g ⟶ pullback g f.imageι :=
  pullback.lift (pullback.snd f g) (pullback.fst f g ≫ f.toImage)
    (by rw [Category.assoc, f.toImage_imageι, pullback.condition])

/-- The whole actual original base-changed map is exactly this actual source factor followed by the actual pulled-back closed embedding. -/
theorem baseChangeImageFactor_fst :
    baseChangeImageFactor f g ≫ pullback.fst g f.imageι = pullback.snd f g :=
  pullback.lift_fst _ _ _

/-- The actual original source-to-image coefficient triangle holds on the entire actual native pullback. -/
theorem baseChangeImageFactor_snd :
    baseChangeImageFactor f g ≫ pullback.snd g f.imageι = pullback.fst f g ≫ f.toImage :=
  pullback.lift_snd _ _ _

/-- The actual original native pullback square and original image square internally prove that this actual source factor is the Cartesian base change of the SAME original canonical image factor. -/
theorem baseChangeImageFactor_isPullback :
    IsPullback (pullback.fst f g) (baseChangeImageFactor f g) f.toImage (pullback.snd g f.imageι) := by
  have houter : IsPullback (pullback.fst f g)
      (baseChangeImageFactor f g ≫ pullback.fst g f.imageι) (f.toImage ≫ f.imageι) g := by
    rw [baseChangeImageFactor_fst, f.toImage_imageι]
    exact IsPullback.of_hasPullback f g
  exact houter.of_bot (baseChangeImageFactor_snd f g).symm
    (IsPullback.of_hasPullback g f.imageι).flip

/-- Original quasi-compactness and actual target flatness internally make the entire actual source factor schematically dominant. -/
theorem baseChangeImageFactor_isSchemeTheoreticallyDominant [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant (baseChangeImageFactor f g) := by
  let : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
  exact IsSchemeTheoreticallyDominant.of_isPullback (baseChangeImageFactor_isPullback f g)

/-- The actual native image of the SAME entire original map after actual flat base change is the actual pullback of its SAME original native image embedding. -/
def flatBaseChangeImageIso [QuasiCompact f] [Flat g] :
    (pullback.snd f g).image ≅ pullback g f.imageι := by
  let := baseChangeImageFactor_isSchemeTheoreticallyDominant f g
  exact imageIsoOfClosedFactor (pullback.snd f g) (pullback.fst g f.imageι)
    (baseChangeImageFactor f g) (baseChangeImageFactor_fst f g)

/-- The actual native image isomorphism retains the literal entire pulled-back closed embedding. -/
theorem flatBaseChangeImageIso_hom_embedding [QuasiCompact f] [Flat g] :
    (flatBaseChangeImageIso f g).hom ≫ pullback.fst g f.imageι = (pullback.snd f g).imageι := by
  let := baseChangeImageFactor_isSchemeTheoreticallyDominant f g
  exact imageIsoOfClosedFactor_hom_embedding (pullback.snd f g) (pullback.fst g f.imageι)
    (baseChangeImageFactor f g) (baseChangeImageFactor_fst f g)

/-- The actual native image isomorphism retains the literal entire original source image factor. -/
theorem toImage_flatBaseChangeImageIso_hom [QuasiCompact f] [Flat g] :
    (pullback.snd f g).toImage ≫ (flatBaseChangeImageIso f g).hom = baseChangeImageFactor f g := by
  let := baseChangeImageFactor_isSchemeTheoreticallyDominant f g
  exact toImage_imageIsoOfClosedFactor_hom (pullback.snd f g) (pullback.fst g f.imageι)
    (baseChangeImageFactor f g) (baseChangeImageFactor_fst f g)

end Hironaka.Geometry.ProjectiveSecant
