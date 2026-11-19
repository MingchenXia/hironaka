import Hironaka.Geometry.QuotGrassmannPivotAffinePolynomialSections
import Hironaka.Geometry.QuotGrassmannPivotAffineTensorPoint

/-!
# Actual original Grassmannian classifier on normalized polynomial pivots

The entire native coordinate and tensor kernels retain every ORIGINAL matrix
coefficient and ambient coordinate. The original standard pivot gives the
already constructed native matrix point itself.
-/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot



universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalKernel_eq_of_targetLinearEquiv
    {A V M N : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (q : V →ₗ[A] M) (m : V →ₗ[A] N)
    (e : M ≃ₗ[A] N) (h : e.toLinearMap.comp q = m) : q.ker = m.ker :=
  (LinearEquiv.ker_comp e q).symm.trans (congrArg LinearMap.ker h)

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The WHOLE original linear quotient on SAME actual polynomial pivot has EXACTLY its original normalized polynomial matrix under the actual produced target isomorphism. -/
theorem originalGlobalAffinePivotQuotient_coordinates :
    (originalGlobalAffinePivotSectionsTargetIso R e).hom.hom.comp
        (originalGlobalAffinePullbackQuotientSections R ι ν (originalPivotModelMorphism R e)) =
      (pivotUniversalMatrix R e).mulVecLin :=
  congrArg ModuleCat.Hom.hom (originalGlobalAffinePivotSectionsTargetIso_quotient R e)

/-- The ENTIRE actual original native coordinate point on SAME original polynomial pivot is the kernel of its original normalized pivot matrix. -/
theorem originalGlobalAffinePivotGrassmannianPoint_toSubmodule :
    (originalGlobalAffineGrassmannianPoint R ι ν (originalPivotModelMorphism R e)).toSubmodule =
      (pivotUniversalMatrix R e).mulVecLin.ker := by
  let : Module (CommRingCat.of (ChartRing R ι κ))
      Γ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
        (originalGlobalImageQuotient R ι ν), ⊤) :=
    inferInstanceAs (Module (CommRingCat.of (ChartRing R ι κ))
      ((moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))).obj
        ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
          (originalGlobalImageQuotient R ι ν))))
  have h : (originalGlobalAffinePivotSectionsTargetIso R e).toLinearEquiv.toLinearMap.comp
        (originalGlobalAffinePullbackQuotientSections R ι ν (originalPivotModelMorphism R e)) =
      (pivotUniversalMatrix R e).mulVecLin :=
    originalGlobalAffinePivotQuotient_coordinates R e
  exact originalKernel_eq_of_targetLinearEquiv _ _
    (originalGlobalAffinePivotSectionsTargetIso R e).toLinearEquiv h

/-- The WHOLE SAME original tensor quotient on the actual polynomial pivot has its ORIGINAL normalized matrix and genuine original tensor coordinates. -/
theorem originalGlobalAffinePivotTensorQuotient_coordinates :
    (originalGlobalAffinePivotSectionsTargetIso R e).hom.hom.comp
        (originalGlobalAffineTensorQuotient R ι ν (originalPivotModelMorphism R e)) =
      (pivotUniversalMatrix R e).mulVecLin.comp
        (TensorProduct.piScalarRight R (ChartRing R ι κ) (ChartRing R ι κ) (ι ⊕ ν)).toLinearMap := by
  let π := (TensorProduct.piScalarRight R (ChartRing R ι κ) (ChartRing R ι κ) (ι ⊕ ν)).toLinearMap
  have h : (originalGlobalAffinePivotSectionsTargetIso R e).hom.hom.comp
        (originalGlobalAffinePullbackQuotientSections R ι ν (originalPivotModelMorphism R e)) =
      (pivotUniversalMatrix R e).mulVecLin :=
    originalGlobalAffinePivotQuotient_coordinates R e
  have hc := congrArg (fun q => q.comp π) h
  change (originalGlobalAffinePivotSectionsTargetIso R e).hom.hom.comp
      ((originalGlobalAffinePullbackQuotientSections R ι ν
        (originalPivotModelMorphism R e)).comp π) = _
  simpa only [LinearMap.comp_assoc, π] using hc

/-- The ENTIRE original native tensor point retains SAME normalized pivot matrix kernel, with its original tensor ambient unchanged. -/
theorem originalGlobalAffinePivotGrassmannianTensorPoint_toSubmodule :
    (originalGlobalAffineGrassmannianTensorPoint R ι ν
      (originalPivotModelMorphism R e)).toSubmodule =
      ((pivotUniversalMatrix R e).mulVecLin.comp
        (TensorProduct.piScalarRight R (ChartRing R ι κ) (ChartRing R ι κ) (ι ⊕ ν)).toLinearMap).ker := by
  let : Module (CommRingCat.of (ChartRing R ι κ))
      Γ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
        (originalGlobalImageQuotient R ι ν), ⊤) :=
    inferInstanceAs (Module (CommRingCat.of (ChartRing R ι κ))
      ((moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))).obj
        ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
          (originalGlobalImageQuotient R ι ν))))
  have h : (originalGlobalAffinePivotSectionsTargetIso R e).toLinearEquiv.toLinearMap.comp
        (originalGlobalAffineTensorQuotient R ι ν (originalPivotModelMorphism R e)) =
      (pivotUniversalMatrix R e).mulVecLin.comp
        (TensorProduct.piScalarRight R (ChartRing R ι κ) (ChartRing R ι κ) (ι ⊕ ν)).toLinearMap :=
    originalGlobalAffinePivotTensorQuotient_coordinates R e
  exact originalKernel_eq_of_targetLinearEquiv _ _
    (originalGlobalAffinePivotSectionsTargetIso R e).toLinearEquiv h

/-- On the ORIGINAL standard polynomial pivot the actual native coordinate classifier is exactly the ORIGINAL matrix point. -/
theorem originalGlobalAffineGrassmannianPoint_standardPivot :
    originalGlobalAffineGrassmannianPoint R ι ν
        (originalPivotModelMorphism R (Equiv.refl (ι ⊕ ν))) =
      matrixPoint (universalMatrix R ι ν) := by
  apply Module.Grassmannian.ext
  have h := originalGlobalAffinePivotGrassmannianPoint_toSubmodule R (Equiv.refl (ι ⊕ ν))
  have hm : pivotUniversalMatrix R (Equiv.refl (ι ⊕ ν)) =
      normalizedMatrix (universalMatrix R ι ν) := rfl
  change (originalGlobalAffineGrassmannianPoint R ι ν
    (originalPivotModelMorphism R (Equiv.refl (ι ⊕ ν)))).toSubmodule =
      (matrixQuotient (universalMatrix R ι ν)).ker
  simpa only [hm, normalizedMatrix_mulVecLin] using h

end Hironaka.Geometry.QuotGrassmann
