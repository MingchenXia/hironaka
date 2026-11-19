/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesAffineScheme

/-!
Closed native proof adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesFormalRestriction.lean`,
SHA256 03441f8ac9af6a7dfc3f0305abb129f54be75ef1ee03181cb9a834414cffa248.
Only Mathlib and the actual owned Rees-family/affine-image cone are imported.
No image-base-change, affine chart, range or coefficient output is assumed.


# Actual restriction of the schematic Rees family to open subschemes

The genuine polynomial-to-Rees image construction commutes with actual
open-immersion restriction. This gives the actual affine Rees charts of the
proper global Rees family, retaining the whole coefficient maps.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Polynomial
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesRestriction

section Image

variable {X Y U V : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ V)
variable (j : U ⟶ X) (i : V ⟶ Y) [IsOpenImmersion i] [QuasiCompact f]
variable (h : IsPullback g j i f)

include h in
/-- The actual kernel ideal sheaf commutes with genuine open pullback. -/
theorem ker_eq_comap_of_open_pullback : g.ker = f.ker.comap i := by
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f g j i h W,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

include h in
/-- The actual pullback square constructs the genuine map of schematic
images, retaining their original closed immersions. -/
def imageRestrictionMap : g.image ⟶ f.image :=
  IsClosedImmersion.lift f.imageι (g.imageι ≫ i) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.map_ker, h.w]
    exact j.le_ker_comp f)

/-- The actual schematic image commutes with open restriction as a TRUE
pullback of its original closed immersion, with all nilpotents retained. -/
theorem isPullback_imageRestriction :
    IsPullback g.imageι (imageRestrictionMap f g j i h) i f.imageι := by
  apply isPullback_of_isClosedImmersion
  · exact (IsClosedImmersion.lift_fac _ _ _).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    exact (ker_eq_comap_of_open_pullback f g j i h).symm

end Image

section Rees

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X U : Scheme.{u}} (f : X ⟶ Spec (.of R)) (i : U ⟶ X)

/-- The actual original open map induces the whole literal Rees coefficient
base-change map, without a supplied family comparison. -/
def ambientMap : ReesFamily.ambient I (i ≫ f) ⟶ ReesFamily.ambient I f :=
  pullback.map (i ≫ f) (ReesFamily.reesBase I) f (ReesFamily.reesBase I)
    i (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The whole original Rees coefficient projection is retained. -/
theorem ambientMap_projection :
    ambientMap I f i ≫ ReesFamily.ambientProjection I f =
      ReesFamily.ambientProjection I (i ≫ f) := by
  simp only [ambientMap, ReesFamily.ambientProjection, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Every actual open immersion induces an actual open immersion of the
literal ambient Rees coefficient families. -/
instance ambientMap_isOpenImmersion [IsOpenImmersion i] :
    IsOpenImmersion (ambientMap I f i) := by
  unfold ambientMap
  infer_instance

/-- The actual original map induces the whole polynomial source map of the
literal iterated coefficient pullbacks. -/
def polynomialSourceMap : ReesFamily.polynomialSource I (i ≫ f) ⟶
    ReesFamily.polynomialSource I f :=
  pullback.map (ReesFamily.ambientProjection I (i ≫ f))
    (ReesFamily.polynomialToRees I)
    (ReesFamily.ambientProjection I f) (ReesFamily.polynomialToRees I)
    (ambientMap I f i) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (ambientMap_projection I f i).symm)
    (by simp)

/-- The original image maps commute with the whole constructed restriction
map, before passing to any schematic image. -/
theorem polynomialSourceMap_imageMap :
    polynomialSourceMap I f i ≫ ReesFamily.imageMap I f =
      ReesFamily.imageMap I (i ≫ f) ≫ ambientMap I f i := by
  simp only [polynomialSourceMap, ReesFamily.imageMap, pullback.map,
    pullback.lift_fst]

/-- The entire polynomial coefficient map is retained by restriction. -/
theorem polynomialSourceMap_snd :
    polynomialSourceMap I f i ≫
      pullback.snd (ReesFamily.ambientProjection I f)
        (ReesFamily.polynomialToRees I) =
      pullback.snd (ReesFamily.ambientProjection I (i ≫ f))
        (ReesFamily.polynomialToRees I) := by
  simp only [polynomialSourceMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The original polynomial-to-Rees arrow above an actual restriction is
its genuine pullback, rather than merely a commuting comparison. -/
theorem polynomialSourceMap_isPullback :
    IsPullback (ReesFamily.imageMap I (i ≫ f)) (polynomialSourceMap I f i)
      (ambientMap I f i) (ReesFamily.imageMap I f) := by
  have houter : IsPullback
      (polynomialSourceMap I f i ≫
        pullback.snd (ReesFamily.ambientProjection I f)
          (ReesFamily.polynomialToRees I))
      (ReesFamily.imageMap I (i ≫ f))
      (ReesFamily.polynomialToRees I)
      (ambientMap I f i ≫ ReesFamily.ambientProjection I f) := by
    rw [polynomialSourceMap_snd, ambientMap_projection]
    exact (IsPullback.of_hasPullback (ReesFamily.ambientProjection I (i ≫ f))
      (ReesFamily.polynomialToRees I)).flip
  exact (houter.of_right (polynomialSourceMap_imageMap I f i)
    (IsPullback.of_hasPullback (ReesFamily.ambientProjection I f)
      (ReesFamily.polynomialToRees I)).flip).flip

/-- The actual open restriction constructs the map of the literal schematic
Rees image families. -/
def familyMap [IsOpenImmersion i] : ReesFamily.family I (i ≫ f) ⟶
    ReesFamily.family I f :=
  imageRestrictionMap (ReesFamily.imageMap I f)
    (ReesFamily.imageMap I (i ≫ f)) (polynomialSourceMap I f i)
    (ambientMap I f i) (polynomialSourceMap_isPullback I f i)

/-- The closed immersion of the actual restricted family is the genuine
pullback of the original closed immersion. -/
theorem familyMap_isPullback [IsOpenImmersion i] :
    IsPullback (ReesFamily.familyImmersion I (i ≫ f)) (familyMap I f i)
      (ambientMap I f i) (ReesFamily.familyImmersion I f) :=
  isPullback_imageRestriction (ReesFamily.imageMap I f)
    (ReesFamily.imageMap I (i ≫ f)) (polynomialSourceMap I f i)
    (ambientMap I f i) (polynomialSourceMap_isPullback I f i)

/-- Every original open immersion gives an actual open immersion between the
constructed schematic Rees image families. -/
instance familyMap_isOpenImmersion [IsOpenImmersion i] :
    IsOpenImmersion (familyMap I f i) :=
  MorphismProperty.of_isPullback (familyMap_isPullback I f i) inferInstance

/-- The whole original-scheme projection is retained in the ambient family. -/
theorem ambientMap_fst :
    ambientMap I f i ≫ pullback.fst f (ReesFamily.reesBase I) =
      pullback.fst (i ≫ f) (ReesFamily.reesBase I) ≫ i := by
  simp only [ambientMap, pullback.map, pullback.lift_fst]

/-- The literal ambient family restricts by true base change over the original
scheme. -/
theorem ambientMap_isPullback :
    IsPullback (pullback.fst (i ≫ f) (ReesFamily.reesBase I))
      (ambientMap I f i) i (pullback.fst f (ReesFamily.reesBase I)) := by
  apply IsPullback.of_bot (v₂₁ := ReesFamily.ambientProjection I f)
    (v₂₂ := f) ?_ (ambientMap_fst I f i).symm
    (IsPullback.of_hasPullback f (ReesFamily.reesBase I))
  rw [ambientMap_projection]
  exact IsPullback.of_hasPullback (i ≫ f) (ReesFamily.reesBase I)

/-- The entire constructed schematic family restricts by actual open base
change above the original scheme, before choosing any affine chart. -/
theorem familyMap_isPullback_over_original [IsOpenImmersion i] :
    IsPullback
      (ReesFamily.familyImmersion I (i ≫ f) ≫
        pullback.fst (i ≫ f) (ReesFamily.reesBase I))
      (familyMap I f i) i
      (ReesFamily.familyImmersion I f ≫
        pullback.fst f (ReesFamily.reesBase I)) :=
  (familyMap_isPullback I f i).paste_horiz (ambientMap_isPullback I f i)

/-- Open restriction retains the whole genuine Rees coefficient projection. -/
theorem familyMap_projection [IsOpenImmersion i] :
    familyMap I f i ≫ ReesFamily.familyProjection I f =
      ReesFamily.familyProjection I (i ≫ f) := by
  rw [ReesFamily.familyProjection, ← Category.assoc,
    ← (familyMap_isPullback I f i).w, Category.assoc, ambientMap_projection]
  rfl

end Rees

section AffineProjection

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (I : Ideal R)

/-- The actual affine family identification retains its entire original
Spec A projection. -/
theorem affineFamilyIso_comp_original :
    (ReesAffineScheme.familyIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (reesAlgebra (I.map (algebraMap R A))))) =
      ReesFamily.familyImmersion I (ReesAffineScheme.affineBase R A) ≫
        pullback.fst (ReesAffineScheme.affineBase R A)
          (ReesFamily.reesBase I) := by
  have hcoeff :
      Spec.map (CommRingCat.ofHom (ReesBaseChange.baseChangeMap (A := A) I).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] reesAlgebra I))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap A (reesAlgebra (I.map (algebraMap R A))))) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (ReesBaseChange.baseChangeMap_comp_algebraMap I)
  rw [← hcoeff, ← Category.assoc,
    ReesAffineScheme.familyIso_comp_immersion, Category.assoc]
  exact congrArg (fun m =>
      ReesFamily.familyImmersion I (ReesAffineScheme.affineBase R A) ≫ m)
    (pullbackSpecIso_hom_fst' R A (reesAlgebra I))

end AffineProjection

section AffineChart

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens} (hU : IsAffineOpen U)

/-- The coefficient homomorphism is derived from the actual original
morphism on the actual affine chart. -/
def chartCoefficient : R →+* Γ(X, U) :=
  (Spec.preimage (hU.fromSpec ≫ f)).hom

/-- The actual chart coefficient homomorphism gives its algebra structure. -/
abbrev chartAlgebra : Algebra R Γ(X, U) := (chartCoefficient f hU).toAlgebra

/-- The affine coefficient morphism for the constructed chart algebra is
literally the original chart morphism to the original base. -/
theorem affineBase_eq_chart :
    letI := chartAlgebra f hU
    ReesAffineScheme.affineBase R Γ(X, U) = hU.fromSpec ≫ f := by
  let := chartAlgebra f hU
  exact Spec.map_preimage (hU.fromSpec ≫ f)

/-- The actual family over an original affine chart is the spectrum of the
Rees algebra of the actual extended ideal, with no comparison assumed. -/
def chartFamilyIso : ReesFamily.family I (hU.fromSpec ≫ f) ≅
    Spec (.of (reesAlgebra (I.map (chartCoefficient f hU)))) :=
  letI := chartAlgebra f hU
  (eqToIso (congrArg (ReesFamily.family I) (affineBase_eq_chart f hU))).symm ≪≫
    ReesAffineScheme.familyIso R Γ(X, U) I

/-- The canonical chart comparison retains the entire original Rees
coefficient morphism, including its scalar structure. -/
theorem chartFamilyIso_comp_projection :
    letI := chartAlgebra f hU
    (chartFamilyIso I f hU).hom ≫
        Spec.map (CommRingCat.ofHom
          (ReesBaseChange.reesMap (A := Γ(X, U)) I).toRingHom) =
      ReesFamily.familyProjection I (hU.fromSpec ≫ f) := by
  let := chartAlgebra f hU
  have transport (g : Spec Γ(X, U) ⟶ Spec (.of R))
      (h : ReesAffineScheme.affineBase R Γ(X, U) = g) :
      ((eqToIso (congrArg (ReesFamily.family I) h)).symm ≪≫
          ReesAffineScheme.familyIso R Γ(X, U) I).hom ≫
          Spec.map (CommRingCat.ofHom
            (ReesBaseChange.reesMap (A := Γ(X, U)) I).toRingHom) =
        ReesFamily.familyProjection I g := by
    cases h
    simpa using ReesAffineScheme.familyIso_comp_projection R Γ(X, U) I
  exact transport _ (affineBase_eq_chart f hU)

/-- The actual affine Rees chart maps into the original global schematic
family by the inverse canonical chart comparison and genuine open restriction. -/
def chartMap : Spec (.of (reesAlgebra (I.map (chartCoefficient f hU)))) ⟶
    ReesFamily.family I f :=
  (chartFamilyIso I f hU).inv ≫ familyMap I f hU.fromSpec

/-- Each actual affine Rees chart is an actual open subscheme of the original
schematic family. -/
instance chartMap_isOpenImmersion : IsOpenImmersion (chartMap I f hU) := by
  unfold chartMap
  infer_instance

/-- The actual affine Rees open chart preserves the whole original Rees
coefficient morphism, rather than only selected functions. -/
theorem chartMap_projection :
    letI := chartAlgebra f hU
    chartMap I f hU ≫ ReesFamily.familyProjection I f =
      Spec.map (CommRingCat.ofHom
        (ReesBaseChange.reesMap (A := Γ(X, U)) I).toRingHom) := by
  let := chartAlgebra f hU
  rw [chartMap, Category.assoc, familyMap_projection,
    ← chartFamilyIso_comp_projection I f hU, Iso.inv_hom_id_assoc]

/-- The canonical chart comparison retains the original affine chart
coefficient morphism on all functions. -/
theorem chartFamilyIso_comp_original :
    (chartFamilyIso I f hU).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U) (reesAlgebra (I.map (chartCoefficient f hU))))) =
      ReesFamily.familyImmersion I (hU.fromSpec ≫ f) ≫
        pullback.fst (hU.fromSpec ≫ f) (ReesFamily.reesBase I) := by
  let := chartAlgebra f hU
  have transport (g : Spec Γ(X, U) ⟶ Spec (.of R))
      (h : ReesAffineScheme.affineBase R Γ(X, U) = g) :
      ((eqToIso (congrArg (ReesFamily.family I) h)).symm ≪≫
          ReesAffineScheme.familyIso R Γ(X, U) I).hom ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, U) (reesAlgebra (I.map (chartCoefficient f hU))))) =
        ReesFamily.familyImmersion I g ≫
          pullback.fst g (ReesFamily.reesBase I) := by
    cases h
    simpa using affineFamilyIso_comp_original R Γ(X, U) I
  exact transport _ (affineBase_eq_chart f hU)

/-- The constructed affine Rees chart is the whole inverse image of the
original affine chart in the global schematic family. -/
theorem chartMap_isPullback_over_original :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (reesAlgebra (I.map (chartCoefficient f hU))))))
      (chartMap I f hU) hU.fromSpec
      (ReesFamily.familyImmersion I f ≫
        pullback.fst f (ReesFamily.reesBase I)) := by
  apply (familyMap_isPullback_over_original I f hU.fromSpec).of_iso
    (chartFamilyIso I f hU) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa using (chartFamilyIso_comp_original I f hU).symm
  · simp [chartMap]
  · simp
  · simp

/-- The actual affine Rees open chart has exactly the original affine chart
as its inverse-image range. In particular these charts cover the entire
constructed global family. -/
theorem chartMap_opensRange :
    (chartMap I f hU).opensRange =
      (ReesFamily.familyImmersion I f ≫
        pullback.fst f (ReesFamily.reesBase I)) ⁻¹ᵁ U := by
  simpa only [TopologicalSpace.Opens.map_top, Scheme.Hom.image_top_eq_opensRange,
    hU.opensRange_fromSpec] using
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (chartMap_isPullback_over_original I f hU) ⊤

end AffineChart

section Cover

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual affine Rees charts form an actual affine open cover of the
whole original schematic family. All rings are the Rees algebras of the
actual original chart ideals. -/
def affineChartCover : (ReesFamily.family I f).AffineOpenCover where
  I₀ := X.affineCover.I₀
  X j := .of (reesAlgebra (I.map
    (chartCoefficient f (isAffineOpen_opensRange (X.affineCover.f j)))))
  f j := chartMap I f (isAffineOpen_opensRange (X.affineCover.f j))
  idx z := X.affineCover.idx
    ((ReesFamily.familyImmersion I f ≫
      pullback.fst f (ReesFamily.reesBase I)) z)
  covers z := by
    change z ∈ (chartMap I f (isAffineOpen_opensRange
      (X.affineCover.f (X.affineCover.idx
        ((ReesFamily.familyImmersion I f ≫
          pullback.fst f (ReesFamily.reesBase I)) z))))).opensRange
    rw [chartMap_opensRange]
    exact X.affineCover.covers _

end Cover

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesRestriction
