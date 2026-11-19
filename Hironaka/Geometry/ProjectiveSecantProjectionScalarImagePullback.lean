import Hironaka.Geometry.ProjectiveSecantProjectionScalarImage

/-!
# The SAME canonical scalar projection's actual native image square is Cartesian
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveSpaceBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  {X : Scheme.{u}} (f : X ⟶ projectiveSpace k n) (pX : X ⟶ Spec (CommRingCat.of k))
  (ht : f ≫ projectiveSpaceStructure k n = pX)

/-- The entire actual source-to-image factor on the canonical scalar source is the Cartesian base change of the SAME original native image factor. -/
theorem originalProjectionScalarImageFactor_isPullback :
    IsPullback (pullback.fst pX (Spec.map (CommRingCat.ofHom φ)))
      (originalProjectionScalarImageFactor k L φ n f pX ht) f.toImage
      (pullback.snd (projectiveCoefficientMap φ n) f.imageι) := by
  let e := originalProjectionScalarSourceIso k L φ n f pX ht
  have hi : e.inv ≫ pullback.fst f (projectiveCoefficientMap φ n) =
      pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) := by
    have h := congrArg (fun m => e.inv ≫ m)
      (originalProjectionScalarSourceIso_hom_fst k L φ n f pX ht)
    change e.inv ≫ (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom φ))) =
      e.inv ≫ pullback.fst f (projectiveCoefficientMap φ n) at h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm
  have hleft : IsPullback e.inv (originalProjectionScalarImageFactor k L φ n f pX ht)
      (baseChangeImageFactor f (projectiveCoefficientMap φ n)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [originalProjectionScalarImageFactor, e]⟩
  have h := hleft.paste_horiz (baseChangeImageFactor_isPullback f (projectiveCoefficientMap φ n))
  simpa only [Category.id_comp, hi] using h

/-- The SAME actual native image factor of the canonical scalar projection is the genuine Cartesian base change of the SAME original native image factor, using the internally produced whole image isomorphism. -/
theorem originalProjectionScalar_toImage_isPullback [QuasiCompact f] :
    IsPullback (pullback.fst pX (Spec.map (CommRingCat.ofHom φ)))
      (originalProjectionScalar k L φ n f pX ht).toImage f.toImage
      ((originalProjectionScalarImageIso k L φ n f pX ht).hom ≫
        pullback.snd (projectiveCoefficientMap φ n) f.imageι) := by
  have hleft : IsPullback (𝟙 _) (originalProjectionScalar k L φ n f pX ht).toImage
      (originalProjectionScalarImageFactor k L φ n f pX ht)
      (originalProjectionScalarImageIso k L φ n f pX ht).hom :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.id_comp] using
      (toImage_originalProjectionScalarImageIso_hom k L φ n f pX ht).symm⟩
  simpa only [Category.id_comp] using
    hleft.paste_horiz (originalProjectionScalarImageFactor_isPullback k L φ n f pX ht)

/-- The actual scalar native-image coefficient morphism is universally open, internally from the actual field Cartesian square and entire native-image isomorphism. -/
theorem originalProjectionScalarImage_coefficient_universallyOpen [QuasiCompact f] :
    UniversallyOpen ((originalProjectionScalarImageIso k L φ n f pX ht).hom ≫
      pullback.snd (projectiveCoefficientMap φ n) f.imageι) := by
  let : UniversallyOpen (projectiveCoefficientMap φ n) := projectiveCoefficientMap_universallyOpen k L φ n
  infer_instance

end Hironaka.Geometry.ProjectiveSecant
