/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesAffineImage
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
Adapted closed native proof from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesFormalAffineScheme.lean`,
SHA256 af1ecad18a601cca2200f57c8b086afce29aa64198ac5a4b72a3a5c55d6a29d2.
Only native Mathlib and owned actual original Rees helper modules are imported.
The geometric finite cohomology/formal-functions comparison remains separate.


# Literal affine-base identification of the schematic Rees family

The actual global schematic-image family for Spec A is compared with the
affine scheme of the Rees algebra of the actual extended ideal.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Polynomial
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesAffineScheme

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (I : Ideal R)

/-- The literal original affine coefficient morphism. -/
abbrev affineBase : Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The actual Rees coefficient base extension of Spec A has the literal
tensor coefficient ring. -/
def ambientIso : ReesFamily.ambient I (affineBase R A) ≅
    Spec (.of (A ⊗[R] reesAlgebra I)) :=
  pullbackSpecIso R A (reesAlgebra I)

/-- Actual pullback pasting and the literal tensor comparison identify the
polynomial source with the tensor polynomial coefficient scheme. -/
def polynomialSourceIso : ReesFamily.polynomialSource I (affineBase R A) ≅
    Spec (.of (A ⊗[R] R[X])) :=
  (ReesFamily.polynomialSource_isPullback I (affineBase R A)).isoPullback ≪≫
    pullbackSpecIso R A R[X]

/-- The whole original affine coefficient projection is retained by the
actual polynomial-source tensor isomorphism. -/
theorem polynomialSourceIso_hom_fst :
    (polynomialSourceIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] R[X]))) =
      ReesFamily.imageMap I (affineBase R A) ≫
        pullback.fst (affineBase R A) (ReesFamily.reesBase I) := by
  rw [polynomialSourceIso, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst',
    IsPullback.isoPullback_hom_fst]

/-- The whole original polynomial coefficient projection is retained. -/
theorem polynomialSourceIso_hom_snd :
    (polynomialSourceIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R[X])).toRingHom) =
      pullback.snd (ReesFamily.ambientProjection I (affineBase R A))
        (ReesFamily.polynomialToRees I) := by
  let h := ReesFamily.polynomialSource_isPullback I (affineBase R A)
  change (h.isoPullback.hom ≫ (pullbackSpecIso R A R[X]).hom) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg (fun m => h.isoPullback.hom ≫ m)
    (pullbackSpecIso_hom_snd R A R[X])).trans h.isoPullback_hom_snd

/-- The actual tensor polynomial map retains the entire original affine
coefficient projection. -/
theorem spec_tensorInclusion_fst :
    Spec.map (CommRingCat.ofHom (ReesAffineImage.tensorInclusion R A I).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] reesAlgebra I))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] R[X]))) := by
  rw [← Spec.map_comp]
  congr 1

/-- The actual tensor polynomial map retains the whole original Rees
coefficient map, through the literal polynomial inclusion. -/
theorem spec_tensorInclusion_snd :
    Spec.map (CommRingCat.ofHom (ReesAffineImage.tensorInclusion R A I).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := reesAlgebra I)).toRingHom) =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R[X])).toRingHom) ≫
        ReesFamily.polynomialToRees I := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The ENTIRE actual global polynomial-to-Rees map over Spec A is exactly
the genuine tensor inclusion under the constructed source and target isomorphisms. -/
theorem imageMap_comp_ambientIso :
    ReesFamily.imageMap I (affineBase R A) ≫ (ambientIso R A I).hom =
      (polynomialSourceIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom (ReesAffineImage.tensorInclusion R A I).toRingHom) := by
  apply (cancel_mono (ambientIso R A I).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, ambientIso, pullbackSpecIso_inv_fst']
    rw [spec_tensorInclusion_fst, polynomialSourceIso_hom_fst]
  · simp only [Category.assoc, ambientIso, pullbackSpecIso_inv_snd]
    refine pullback.condition.trans ?_
    have h := (congrArg (fun m => (polynomialSourceIso R A I).hom ≫ m)
      (spec_tensorInclusion_snd R A I)).symm
    rw [← Category.assoc, polynomialSourceIso_hom_snd] at h
    exact h

/-- Genuine isomorphisms of the whole source and target arrow construct
isomorphic actual schematic images, with every nilpotent retained. -/
def imageIsoOfArrowIso {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (h : f ≫ eY.hom = eX.hom ≫ g) :
    f.image ≅ g.image := by
  let i := f.imageι ≫ eY.hom
  have : IsClosedImmersion i := by dsimp only [i]; infer_instance
  have hker : i.ker = g.imageι.ker := by
    change (f.imageι ≫ eY.hom).ker = g.imageι.ker
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.map_ker, h,
      Scheme.Hom.ker_comp_of_isIso]
  have := IsClosedImmersion.isIso_lift g.imageι i hker.symm
  exact asIso (IsClosedImmersion.lift g.imageι i hker.symm.le)

/-- The image isomorphism preserves the ENTIRE original closed immersion
and target isomorphism. -/
theorem imageIsoOfArrowIso_comp {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (h : f ≫ eY.hom = eX.hom ≫ g) :
    (imageIsoOfArrowIso f g eX eY h).hom ≫ g.imageι = f.imageι ≫ eY.hom :=
  IsClosedImmersion.lift_fac _ _ _

/-- The LITERAL original schematic Rees family over Spec A is the affine
scheme of the ACTUAL extended ideal Rees algebra. All constructions and
whole arrow identifications are derived from the original coefficients. -/
def familyIso : ReesFamily.family I (affineBase R A) ≅
    Spec (.of (reesAlgebra (I.map (algebraMap R A)))) :=
  imageIsoOfArrowIso (ReesFamily.imageMap I (affineBase R A))
      (Spec.map (CommRingCat.ofHom (ReesAffineImage.tensorInclusion R A I).toRingHom))
      (polynomialSourceIso R A I) (ambientIso R A I) (imageMap_comp_ambientIso R A I) ≪≫
    ReesAffineImage.affineImageSchemeIso R A I

/-- The literal family isomorphism retains its ENTIRE actual closed
immersion in the original Rees coefficient base extension. -/
theorem familyIso_comp_immersion :
    (familyIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom (ReesBaseChange.baseChangeMap (A := A) I).toRingHom) =
      ReesFamily.familyImmersion I (affineBase R A) ≫ (ambientIso R A I).hom := by
  rw [familyIso, Iso.trans_hom, Category.assoc,
    ReesAffineImage.affineImageSchemeIso_comp_immersion, imageIsoOfArrowIso_comp]

/-- The literal family identification retains the WHOLE original Rees
coefficient projection as a genuine scheme-morphism equality. -/
theorem familyIso_comp_projection :
    (familyIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom (ReesBaseChange.reesMap (A := A) I).toRingHom) =
      ReesFamily.familyProjection I (affineBase R A) := by
  have hcoeff :
      Spec.map (CommRingCat.ofHom (ReesBaseChange.baseChangeMap (A := A) I).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := reesAlgebra I)).toRingHom) =
        Spec.map (CommRingCat.ofHom (ReesBaseChange.reesMap (A := A) I).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact DFunLike.congr_fun (ReesBaseChange.baseChangeMap_comp_includeRight (A := A) I) p
  rw [← hcoeff, ← Category.assoc, familyIso_comp_immersion, Category.assoc]
  exact congrArg (fun m => ReesFamily.familyImmersion I (affineBase R A) ≫ m)
    (pullbackSpecIso_hom_snd R A (reesAlgebra I))

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesAffineScheme
