import Hironaka.Geometry.QuotGrassmannPivotGlobalLocalFrames
import Hironaka.Geometry.QuotGrassmannPivotOverSections

/-!
# Native local rank of the SAME actual original global image quotient

Every module is obtained by actual evaluation of the SAME original global
image on the SAME original pivot over-site. Its actual native frame produces
the actual finite function-module equivalence and native rank at every prime.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- Actual original global-image sections have their internally produced native finite function basis. -/
def originalGlobalImagePivotSectionsIso (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    (SheafOfModules.evaluation
      ((projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j))
      (.op (originalOverTop (projectiveModel R ι ν) (coordinateOpen R ι ν j)))).obj
        ((originalGlobalImageQuotient R ι ν).over (coordinateOpen R ι ν j)) ≅
      ModuleCat.of Γ(projectiveModel R ι ν, coordinateOpen R ι ν j)
        (ι → Γ(projectiveModel R ι ν, coordinateOpen R ι ν j)) :=
  (SheafOfModules.evaluation
    ((projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j))
    (.op (originalOverTop (projectiveModel R ι ν) (coordinateOpen R ι ν j)))).mapIso
      (actualOriginalGlobalImageFrame R ι ν j hj) ≪≫
    originalOverFreeSectionsIso (projectiveModel R ι ν) (coordinateOpen R ι ν j) ι

/-- Native rank at every actual prime of every original pivot section ring is the SAME original rank. -/
theorem originalGlobalImagePivotSections_rankAtStalk (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    Module.rankAtStalk (R := Γ(projectiveModel R ι ν, coordinateOpen R ι ν j))
      ((SheafOfModules.evaluation
        ((projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j))
        (.op (originalOverTop (projectiveModel R ι ν) (coordinateOpen R ι ν j)))).obj
          ((originalGlobalImageQuotient R ι ν).over (coordinateOpen R ι ν j))) =
      fun (_ : PrimeSpectrum Γ(projectiveModel R ι ν, coordinateOpen R ι ν j)) => Fintype.card ι := by
  let F := SheafOfModules.evaluation
    ((projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j))
    (.op (originalOverTop (projectiveModel R ι ν) (coordinateOpen R ι ν j)))
  let e := (F.mapIso (actualOriginalGlobalImageFrame R ι ν j hj)).toLinearEquiv
  exact (Module.rankAtStalk_eq_of_equiv
    (R := Γ(projectiveModel R ι ν, coordinateOpen R ι ν j)) e).trans
    (originalOverFreeSections_rankAtStalk (projectiveModel R ι ν) (coordinateOpen R ι ν j) ι)

end Hironaka.Geometry.QuotGrassmann
