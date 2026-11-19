import Hironaka.Geometry.QuotGrassmannPivotAffineCompositeSections
import Hironaka.Geometry.QuotGrassmannPivotAffinePullbackProjectivity

/-!
# SAME original global quotient has WHOLE native actual affine base-change square

Both actual module targets and the original quotient maps are preserved. Their
quasicoherence is produced by SAME original native pullback generators. No
quotient comparison, original scalar compatibility or free frame is an input.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι] {A B : CommRingCat.{u}}

/-- Actual section scalar extension of SAME original quotient has SAME native composed-pullback target, with BOTH whole maps produced. -/
def originalGlobalAffineImageSectionsBaseChangeIso (φ : A ⟶ B)
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj
      ((pullback f).obj (originalGlobalImageQuotient R ι ν))) ≅
    moduleSpecΓFunctor.obj
      ((pullback (Spec.map φ ≫ f)).obj (originalGlobalImageQuotient R ι ν)) :=
  originalCompositeSpecPullbackSectionsIso φ f (originalGlobalImageQuotient R ι ν)

/-- SAME actual native original free source has its internally produced native affine-section base-change isomorphism. -/
def originalGlobalAffineSourceSectionsBaseChangeIso (φ : A ⟶ B)
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj
      ((pullback f).obj (SheafOfModules.free
        (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)))) ≅
    moduleSpecΓFunctor.obj ((pullback (Spec.map φ ≫ f)).obj
      (SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν))) := by
  let S := SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)
  let : ((pullback f).obj S).IsLocallyFree := originalSchemePullback_isLocallyFree f S
  exact originalCompositeSpecPullbackSectionsIso φ f S

/-- The WHOLE SAME actual native original quotient commutes with its produced ORIGINAL affine section base-change maps. -/
theorem originalGlobalAffineQuotientSections_baseChange (φ : A ⟶ B)
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (ModuleCat.extendScalars φ.hom).map
        (moduleSpecΓFunctor.map ((pullback f).map (originalGlobalQuotient R ι ν))) ≫
      (originalGlobalAffineImageSectionsBaseChangeIso R ι ν φ f).hom =
    (originalGlobalAffineSourceSectionsBaseChangeIso R ι ν φ f).hom ≫
      moduleSpecΓFunctor.map ((pullback (Spec.map φ ≫ f)).map
        (originalGlobalQuotient R ι ν)) := by
  let S := SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)
  let : ((pullback f).obj S).IsLocallyFree := originalSchemePullback_isLocallyFree f S
  exact originalCompositeSpecPullbackSectionsIso_naturality φ f (originalGlobalQuotient R ι ν)

end Hironaka.Geometry.QuotGrassmann
