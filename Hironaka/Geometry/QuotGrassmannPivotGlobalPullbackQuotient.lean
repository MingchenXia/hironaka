import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackFrame
import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackCoefficients
import Hironaka.Geometry.QuotGrassmannPivotOverSchemeMatrices
import Hironaka.Geometry.QuotGrassmannPivotOriginalPullback

/-!
# The actual original over-site quotient on the ORIGINAL polynomial pivot

The map is transported by the native open-scheme equivalence and the true
native Scheme.Modules pullback. Every coefficient comes from the SAME
original global contraction and its proved whole-ring polynomial identity.
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

/-- The actual original quotient on its original over-site, retaining its SAME original source basis. -/
def originalPivotOverFreeQuotient :
    SheafOfModules.free
      (R := (projectiveModel R ι ν).ringCatSheaf.over
        (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))) (ι ⊕ ν) ⟶
    SheafOfModules.free
      (R := (projectiveModel R ι ν).ringCatSheaf.over
        (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))) ι :=
  (originalOverFreeIso (projectiveModel R ι ν)
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)) (ι ⊕ ν)).hom ≫
      originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e)

/-- Its actual true native transport to the SAME original polynomial-pivot scheme. -/
def originalPivotLocalTrueQuotient :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) (ι ⊕ ν) ⟶
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι :=
  originalPullbackFreeHom (pivotMatrixSchemeIso R e).inv
    (originalOverEquivFreeHom (projectiveModel R ι ν)
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
      (originalPivotOverFreeQuotient R e))

/-- Every whole actual native transported quotient coefficient is its SAME original contraction coefficient. -/
theorem originalPivotLocalTrueQuotient_coefficient (a : ι ⊕ ν) (i : ι) :
    originalFreeHomCoefficient (originalPivotLocalTrueQuotient R e) a i =
      originalPullbackUnitEnd (pivotMatrixSchemeIso R e).inv
        (originalOverEquivUnitEnd (projectiveModel R ι ν)
          (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
          (originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
            a (coordinateSelector ι ν (pivotIndex (coordinateSelector ι ν) e), i))) := by
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  have hb : SheafOfModules.ιFree a ≫ originalPivotOverFreeQuotient R e ≫
      originalOverFreeProjection X U i =
      originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
        a (coordinateSelector ι ν (pivotIndex (coordinateSelector ι ν) e), i) := by
    change SheafOfModules.ιFree a ≫ (originalOverFreeIso X U (ι ⊕ ν)).hom ≫
      originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e) ≫
        originalOverFreeProjection X U i = _
    rw [← Category.assoc (SheafOfModules.ιFree a), originalOverFreeIso_inclusion]
    exact originalOverPivotQuotient_coefficient R ι ν _ a i
  exact (originalOverSchemePullbackFreeHom_coefficient U (pivotMatrixSchemeIso R e).inv
    (originalPivotOverFreeQuotient R e) a i).trans
      (congrArg (fun b => originalPullbackUnitEnd (pivotMatrixSchemeIso R e).inv
        (originalOverEquivUnitEnd X U b)) hb)

/-- The WHOLE actual native transported quotient is the SAME original normalized polynomial matrix map. -/
theorem originalPivotLocalTrueQuotient_eq_matrix :
    originalPivotLocalTrueQuotient R e =
      originalMatrixQuotientSheaf (ChartRing R ι κ) (pivotUniversalMatrix R e) := by
  classical
  apply originalFreeHomCoefficient_ext_top (affineChart R ι κ)
  intro a i
  have hc := congrArg (fun b : End (SheafOfModules.unit (affineChart R ι κ).ringCatSheaf) =>
      b.val.app (.op ⊤) (1 : Γ(affineChart R ι κ, ⊤)))
    (originalPivotLocalTrueQuotient_coefficient R e a i)
  have hp := originalOverContractionEntry_truePullback_one_top R e a
    (coordinateSelector ι ν (pivotIndex (coordinateSelector ι ν) e), i)
  have hm : originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν)) (pivotUniversalMatrix R e)
      (coordinateSelector ι ν (pivotIndex (coordinateSelector ι ν) e), i) a =
      pivotUniversalMatrix R e i a := by
    have ht := congrArg (fun M => M i a)
      (originalContractionMatrix_pivot_rows (Equiv.refl (ι → ι ⊕ ν)) e (universalMatrix R ι κ))
    simp only [Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      pivotIndex, Equiv.apply_symm_apply, pivotUniversalMatrix, id_eq] at ht ⊢
    exact ht
  exact hc.trans (hp.trans ((congrArg (originalAffineCoefficientMap (ChartRing R ι κ) ⊤) hm).trans
    (originalMatrixQuotientSheaf_coefficient_one (ChartRing R ι κ) (pivotUniversalMatrix R e) i a ⊤).symm))

end Hironaka.Geometry.QuotGrassmann
