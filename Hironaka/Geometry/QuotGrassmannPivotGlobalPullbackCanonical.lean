import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackTriangle
import Hironaka.Geometry.QuotGrassmannPivotCompositeFreeCoherence

/-!
# BOTH original quotient triangles with the canonical ORIGINAL native source frame

The source comparison is exactly the originally frozen canonical native
free-pullback frame. The target is the SAME actual unframed pullback of Q.
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

/-- The actual original source frame is EXACTLY the canonical ORIGINAL native free-pullback comparison. -/
theorem originalGlobalSourcePivotTruePullbackFrame_eq_originalPullbackFreeIso :
    originalGlobalSourcePivotTruePullbackFrame R e =
      originalPullbackFreeIso (originalPivotModelMorphism R e) (ι ⊕ ν) := by
  have h := congrArg Iso.hom (originalOverCompositeFreeIso_eq_originalPullbackFreeIso
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
    (pivotMatrixSchemeIso R e).inv (ι ⊕ ν))
  apply Iso.ext
  simp only [originalGlobalSourcePivotTruePullbackFrame, originalOverCompositeFreeIso,
    originalOverOpenPullbackFreeIso, originalPivotOverPullbackFunctor,
    originalPivotOverPullbackFreeIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom] at h ⊢
  exact h

/-- The FIRST exact original quotient triangle uses the canonical ORIGINAL native source frame
and the SAME ACTUAL unframed native pullback of the ORIGINAL global image Q. -/
theorem originalGlobalImagePivotTruePullback_canonical_quotient_triangle :
    (SheafOfModules.freeMap e ≫ (originalPullbackFreeIso (originalPivotModelMorphism R e) (ι ⊕ ν)).inv ≫
      (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν)) ≫
        (originalGlobalImagePivotTruePullbackFrame R e).hom = universalQuotient R ι κ := by
  have hs := congrArg Iso.inv
    (originalGlobalSourcePivotTruePullbackFrame_eq_originalPullbackFreeIso R e)
  exact (congrArg (fun v => (SheafOfModules.freeMap e ≫ v ≫
    (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν)) ≫
      (originalGlobalImagePivotTruePullbackFrame R e).hom) hs.symm).trans
        (originalGlobalImagePivotTruePullback_quotient_triangle R e)

/-- The SECOND exact original quotient triangle lands in the SAME ACTUAL unframed native pullback Q,
again retaining the canonical ORIGINAL native source comparison. -/
theorem originalGlobalImagePivotTruePullback_canonical_quotient_triangle_inv :
    universalQuotient R ι κ ≫ (originalGlobalImagePivotTruePullbackFrame R e).inv =
      SheafOfModules.freeMap e ≫ (originalPullbackFreeIso (originalPivotModelMorphism R e) (ι ⊕ ν)).inv ≫
        (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν) := by
  have hs := congrArg Iso.inv
    (originalGlobalSourcePivotTruePullbackFrame_eq_originalPullbackFreeIso R e)
  exact (originalGlobalImagePivotTruePullback_quotient_triangle_inv R e).trans
    (congrArg (fun v => SheafOfModules.freeMap e ≫ v ≫
      (Scheme.Modules.pullback (originalPivotModelMorphism R e)).map (originalGlobalQuotient R ι ν)) hs)

end Hironaka.Geometry.QuotGrassmann
