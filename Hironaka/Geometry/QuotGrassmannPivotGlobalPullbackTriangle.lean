import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackQuotient
import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackComparison

/-!
# BOTH original quotient triangles on the ACTUAL unframed native pivot pullback target

The map pulled back is the SAME original global quotient. The affine map is
the originally frozen tilde-constructed normalized quotient. All source and
target comparisons are the preceding internally produced actual native isos.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalReverseNativeQuotientTriangle {C : Type*} [Category C]
    {S M A : C} (q : S ⟶ M) (a : M ≅ A) (r : S ⟶ A) (h : q ≫ a.hom = r) :
    r ≫ a.inv = q :=
  (congrArg (fun z => z ≫ a.inv) h.symm).trans
    ((Category.assoc q a.hom a.inv).trans
      ((congrArg (fun z => q ≫ z) a.hom_inv_id).trans (Category.comp_id q)))

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The entire SAME original global quotient under ACTUAL native pivot pullback is its original matrix map. -/
theorem originalGlobalImagePivotFramedQuotient_eq_originalMatrix :
    originalGlobalImagePivotFramedQuotient R e =
      originalMatrixQuotientSheaf (ChartRing R ι κ) (pivotUniversalMatrix R e) :=
  (originalGlobalImagePivotFramedQuotient_eq_transport R e).trans
    (originalPivotLocalTrueQuotient_eq_matrix R e)

/-- Original reindexing identifies that SAME entire native pullback map with the originally frozen tilde quotient. -/
theorem originalGlobalImagePivotFramedQuotient_eq_originalQuotient :
    SheafOfModules.freeMap e ≫ originalGlobalImagePivotFramedQuotient R e =
      universalQuotient R ι κ := by
  classical
  have hm : (pivotUniversalMatrix R e).submatrix id e =
      normalizedMatrix (universalMatrix R ι κ) := by
    ext i a
    simp only [Matrix.submatrix_apply, pivotUniversalMatrix, splitNormalizedMatrix,
      Equiv.symm_apply_apply, id_eq]
    rfl
  calc
    _ = SheafOfModules.freeMap e ≫
        originalMatrixQuotientSheaf (ChartRing R ι κ) (pivotUniversalMatrix R e) :=
      congrArg (fun q => SheafOfModules.freeMap e ≫ q)
        (originalGlobalImagePivotFramedQuotient_eq_originalMatrix R e)
    _ = originalMatrixQuotientSheaf (ChartRing R ι κ)
        ((pivotUniversalMatrix R e).submatrix id e) :=
      originalMatrixQuotientSheaf_reindex (ChartRing R ι κ) e (pivotUniversalMatrix R e)
    _ = originalMatrixQuotientSheaf (ChartRing R ι κ)
        (normalizedMatrix (universalMatrix R ι κ)) :=
      congrArg (originalMatrixQuotientSheaf (ChartRing R ι κ)) hm
    _ = universalQuotient R ι κ := (originalUniversalQuotient_eq_matrix R ι κ).symm

/-- The FIRST exact original quotient triangle retains the ACTUAL unframed native pulled-back global target. -/
theorem originalGlobalImagePivotTruePullback_quotient_triangle :
    (SheafOfModules.freeMap e ≫ (originalGlobalSourcePivotTruePullbackFrame R e).inv ≫
      (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν)) ≫
        (originalGlobalImagePivotTruePullbackFrame R e).hom = universalQuotient R ι κ := by
  simp only [Category.assoc]
  exact originalGlobalImagePivotFramedQuotient_eq_originalQuotient R e

/-- The SECOND exact original quotient triangle lands in that SAME ACTUAL unframed native pulled-back global target. -/
theorem originalGlobalImagePivotTruePullback_quotient_triangle_inv :
    universalQuotient R ι κ ≫ (originalGlobalImagePivotTruePullbackFrame R e).inv =
      SheafOfModules.freeMap e ≫ (originalGlobalSourcePivotTruePullbackFrame R e).inv ≫
        (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν) :=
  originalReverseNativeQuotientTriangle _ (originalGlobalImagePivotTruePullbackFrame R e) _
    (originalGlobalImagePivotTruePullback_quotient_triangle R e)

end Hironaka.Geometry.QuotGrassmann
