import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackSections
import Hironaka.Geometry.QuotGrassmannPivotOverSchemePullback
import Hironaka.Geometry.QuotGrassmannPivotGlobalLocalFrames

/-!
# Actual unframed native pullback of the SAME global image on its ORIGINAL polynomial pivot

Every frame below is internally produced from the SAME original global image
frame and the actual native composite-pullback comparison. No frame is input.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The actual original over-site/open-scheme/native-pullback functor on the original polynomial pivot. -/
def originalPivotOverPullbackFunctor :
    SheafOfModules.{u}
      ((projectiveModel R ι ν).ringCatSheaf.over
        (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))) ⥤
      (affineChart R ι κ).Modules :=
  (Scheme.Modules.overEquiv (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))).functor ⋙
    Scheme.Modules.pullback (pivotMatrixSchemeIso R e).inv

/-- Its actual native free comparison retains each original source or target index. -/
def originalPivotOverPullbackFreeIso (J : Type u) :
    (originalPivotOverPullbackFunctor R e).obj (SheafOfModules.free
      (R := (projectiveModel R ι ν).ringCatSheaf.over
        (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))) J) ≅
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) J :=
  (Scheme.Modules.pullback (pivotMatrixSchemeIso R e).inv).mapIso
    (originalOverEquivFreeIso (projectiveModel R ι ν)
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)) J).symm ≪≫
    originalPullbackFreeIso (pivotMatrixSchemeIso R e).inv J

/-- The actual SAME native pulled-back image object has its internally produced original free frame. -/
def originalGlobalImagePivotTruePullbackFrame :
    (Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
      (originalGlobalImageQuotient R ι ν) ≅
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι :=
  ((originalOverCompositePullbackIso
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
      (pivotMatrixSchemeIso R e).inv).app (originalGlobalImageQuotient R ι ν)).symm ≪≫
    (originalPivotOverPullbackFunctor R e).mapIso (originalGlobalImagePivotFrame R e) ≪≫
      originalPivotOverPullbackFreeIso R e ι

/-- The actual SAME native pulled-back original source has its internally produced original free frame. -/
def originalGlobalSourcePivotTruePullbackFrame :
    (Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
      (SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)) ≅
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) (ι ⊕ ν) :=
  ((originalOverCompositePullbackIso
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
      (pivotMatrixSchemeIso R e).inv).app
        (SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν))).symm ≪≫
    (originalPivotOverPullbackFunctor R e).mapIso
      (originalOverFreeIso (projectiveModel R ι ν)
        (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)) (ι ⊕ ν)).symm ≪≫
      originalPivotOverPullbackFreeIso R e (ι ⊕ ν)

/-- The actual ORIGINAL global quotient itself, framed only by the preceding internally produced comparisons. -/
def originalGlobalImagePivotFramedQuotient :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) (ι ⊕ ν) ⟶
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι :=
  (originalGlobalSourcePivotTruePullbackFrame R e).inv ≫
    (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν) ≫
      (originalGlobalImagePivotTruePullbackFrame R e).hom

end Hironaka.Geometry.QuotGrassmann
