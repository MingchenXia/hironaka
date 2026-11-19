import Hironaka.Geometry.QuotGrassmannPivotAffineFreeScalarCoordinates

/-!
# WHOLE ORIGINAL native affine free-coordinate scalar triangle

Native extension adjunction and ORIGINAL finite coordinate basis extensionality
upgrade internally produced exact EVERY-basis readback to WHOLE native maps.
No source or quotient coefficient compatibility is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalFiniteScalarHom_ext {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {I : Type u} [Finite I] [DecidableEq I] {N : ModuleCat B}
    {p q : (ModuleCat.extendScalars φ).obj (ModuleCat.of A (I → A)) ⟶ N}
    (h : ∀ i : I, p ((ModuleCat.extendRestrictScalarsAdj φ).unit.app
      (ModuleCat.of A (I → A)) (Pi.single i (1 : A))) =
      q ((ModuleCat.extendRestrictScalarsAdj φ).unit.app
        (ModuleCat.of A (I → A)) (Pi.single i (1 : A)))) : p = q := by
  let : Fintype I := Fintype.ofFinite I
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply (Pi.basisFun A I).ext
  intro i
  simp only [Pi.basisFun_apply]
  exact h i

/-- The actual native original source scalar map uses SAME original coordinate frame, native affine pullback sections and canonical free-pullback frame. -/
def originalAffineFreeSectionScalarMap {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : Type u) [Finite I] :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A (I → A)) ⟶
      moduleSpecΓFunctor.obj (SheafOfModules.free (R := (Spec B).ringCatSheaf) I) :=
  (ModuleCat.extendScalars φ.hom).map (originalAffineFreeSectionsCoordinateIso A I).hom ≫
    (originalSpecPullbackSectionsIso φ
      (SheafOfModules.free (R := (Spec A).ringCatSheaf) I)).hom ≫
      moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ) I).hom

/-- EVERY ORIGINAL source coordinate basis has its SAME native target free-section coordinate under actual scalar pullback. -/
theorem originalAffineFreeSectionScalarMap_basis {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : Type u) [Finite I] [DecidableEq I] (i : I) :
    originalAffineFreeSectionScalarMap φ I
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ModuleCat.of A (I → A))
        (Pi.single i (1 : A))) =
      (originalAffineFreeSectionsCoordinateIso B I).hom (Pi.single i (1 : B)) := by
  have hη := ConcreteCategory.congr_hom
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.naturality
      (originalAffineFreeSectionsCoordinateIso A I).hom) (Pi.single i (1 : A))
  have h := congrArg (fun v => moduleSpecΓFunctor.map
      (originalPullbackFreeIso (Spec.map φ) I).hom
        ((originalSpecPullbackSectionsIso φ
          (SheafOfModules.free (R := (Spec A).ringCatSheaf) I)).hom v)) hη.symm
  exact h.trans (originalSpecPullbackFreeSections_basis φ I i)

/-- The WHOLE actual original affine free-section scalar map is the ORIGINAL canonical coordinate scalar isomorphism followed by SAME original target coordinate frame. -/
theorem originalAffineFreeSectionScalarMap_eq_coordinate {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : Type u) [Finite I] :
    originalAffineFreeSectionScalarMap φ I =
      (originalAffineFreeScalarCoordinateIso φ I).hom ≫
        (originalAffineFreeSectionsCoordinateIso B I).hom := by
  classical
  apply originalFiniteScalarHom_ext φ.hom
  intro i
  exact (originalAffineFreeSectionScalarMap_basis φ I i).trans
    (congrArg (originalAffineFreeSectionsCoordinateIso B I).hom
      (originalAffineFreeScalarCoordinateIso_basis φ I i).symm)

end Hironaka.Geometry.QuotGrassmann
