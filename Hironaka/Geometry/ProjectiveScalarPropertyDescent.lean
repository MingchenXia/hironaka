import Hironaka.Geometry.FieldScalarPropertyDescent
import Hironaka.Geometry.ProjectiveSecantProjectionScalarImagePullback

/-!
# Actual generic properties of the SAME original scalar projective map descend
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveScalarPropertyDescent

open ProjectiveSecant BlowupProjectiveEmbedding ProjectiveSpaceBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (L K : Type u) [Field L] [Field K] (φ : L →+* K)

/-- ORIGINAL finite-type source geometry gives native source Noetherianity. -/
theorem originalSource_noetherian {X : Scheme.{u}} (pX : X ⟶ Spec (.of L))
    [LocallyOfFiniteType pX] [QuasiCompact pX] : IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
  exact ⟨⟩

/-- The SAME original canonical scalar source is internally native Noetherian. -/
theorem scalarSource_noetherian {X : Scheme.{u}} (pX : X ⟶ Spec (.of L))
    [LocallyOfFiniteType pX] [QuasiCompact pX] :
    IsNoetherian (pullback pX (Spec.map (CommRingCat.ofHom φ))) := by
  exact ⟨⟩

/-- The actual original integral field homomorphism internally gives the SAME projective fpqc integral cover. -/
theorem projectiveCover_properties (hφ : φ.IsIntegral) (n : ℕ) :
    Surjective (projectiveCoefficientMap φ n) ∧ Flat (projectiveCoefficientMap φ n) ∧
      IsIntegralHom (projectiveCoefficientMap φ n) := by
  let : IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) := IsIntegralHom.SpecMap_iff.mpr hφ
  have H := (isPullback_projectiveCoefficientMap φ n).flip
  exact ⟨MorphismProperty.of_isPullback H inferInstance,
    MorphismProperty.of_isPullback H inferInstance,
    MorphismProperty.of_isPullback H inferInstance⟩

variable (n : ℕ) {X : Scheme.{u}} (f : X ⟶ projectiveSpace L n)
    (pX : X ⟶ Spec (.of L)) (ht : f ≫ projectiveSpaceStructure L n = pX)

/-- The actual canonical original scalar map retains the genuine Cartesian square of the SAME original map. -/
theorem scalarProjection_isPullback :
    IsPullback (pullback.fst pX (Spec.map (CommRingCat.ofHom φ)))
      (originalProjectionScalar L K φ n f pX ht) f (projectiveCoefficientMap φ n) := by
  let e := originalProjectionScalarSourceIso L K φ n f pX ht
  have hi : e.inv ≫ pullback.fst f (projectiveCoefficientMap φ n) =
      pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) := by
    have h := congrArg (fun m => e.inv ≫ m)
      (originalProjectionScalarSourceIso_hom_fst L K φ n f pX ht)
    change e.inv ≫ (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom φ))) =
      e.inv ≫ pullback.fst f (projectiveCoefficientMap φ n) at h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm
  have hleft : IsPullback e.inv (originalProjectionScalar L K φ n f pX ht)
      (pullback.snd f (projectiveCoefficientMap φ n)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [originalProjectionScalar, e]⟩
  simpa only [Category.id_comp, hi] using
    hleft.paste_horiz (IsPullback.of_hasPullback f (projectiveCoefficientMap φ n))

/-- Actual generic etaleness of the canonical scalar map descends to the SAME original map. -/
theorem genericallyEtale_descent (hφ : φ.IsIntegral)
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    (hfK : IsGenericallyEtale (originalProjectionScalar L K φ n f pX ht)) : IsGenericallyEtale f := by
  obtain ⟨hs, hfl, hint⟩ := projectiveCover_properties L K φ hφ n
  let := hs
  let := hfl
  let := hint
  let := scalarSource_noetherian L K φ pX
  exact GenericallyEtaleIntegralDescent.of_isPullback
    (scalarProjection_isPullback L K φ n f pX ht) hfK

/-- Native BR of the SAME scalar native image factor descends to the ENTIRE original native image. -/
theorem toImage_birationalOver_descent (hφ : φ.IsIntegral)
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    (hfK : Scheme.BirationalOver (originalProjectionScalar L K φ n f pX ht).toImage (𝟙 _)) :
    Scheme.BirationalOver f.toImage (𝟙 f.image) := by
  let := originalSource_noetherian L pX
  let := scalarSource_noetherian L K φ pX
  obtain ⟨hs, hfl, hint⟩ := projectiveCover_properties L K φ hφ n
  let := hs
  let := hfl
  let := hint
  let E := originalProjectionScalarImageIso L K φ n f pX ht
  let b := E.hom ≫ pullback.snd (projectiveCoefficientMap φ n) f.imageι
  let : Surjective b := inferInstance
  let : Flat b := inferInstance
  let : IsIntegralHom b := inferInstance
  exact BirationalIntegralDescent.of_isPullback
    (originalProjectionScalar_toImage_isPullback L K φ n f pX ht) hfK

end Hironaka.Geometry.ProjectiveScalarPropertyDescent
