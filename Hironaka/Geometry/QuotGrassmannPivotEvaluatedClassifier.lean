import Hironaka.Geometry.QuotGrassmannPivotEvaluatedMorphism
import Hironaka.Geometry.QuotGrassmannPivotAffinePolynomialPoint
import Hironaka.Geometry.QuotGrassmannPivotAffineClassifierNaturality
import Hironaka.Algebra.PluckerQuotTransitionSplitTensor
import Hironaka.Algebra.PluckerQuotTransitionMatrixTensorChange

/-!
# SAME actual evaluated original pivot has its original native quotient classifier

The actual polynomial spectrum morphism, original pivot and every original
coefficient determine the entire native kernel. No classifier comparison is
an input; all scalar and original tensor-source maps are retained.
-/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalMappedQuotientKernel
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {V : Type v} [AddCommGroup V] [Module R V]
    {M : Type w} [AddCommGroup M] [Module A M] {r : ℕ}
    (φ : A →ₐ[R] B) (N : Module.Grassmannian A (A ⊗[R] V) r)
    (q : A ⊗[R] V →ₗ[A] M) (hq : Function.Surjective q) (hN : N.toSubmodule = q.ker) :
    letI : Algebra A B := φ.toAlgebra
    letI : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
    (Module.Grassmannian.map φ N).toSubmodule =
      (Algebra.GrassmannQuotientKernel.changedQuotient (B := B) q).ker := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
  rw [Module.Grassmannian.map_toSubmodule, hN,
    Algebra.GrassmannQuotientKernel.changedQuotient_factor q hq, LinearEquiv.ker_comp]

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A)

/-- The ENTIRE native original quotient classifier of SAME actual evaluated polynomial pivot is the original split normalized matrix tensor kernel, with unchanged original ambient and all original coefficient values. -/
theorem originalMatrixEvaluatedPivotClassifier_toSubmodule :
    (originalGlobalAffineGrassmannianTensorPoint R ι ν
      (originalMatrixEvaluatedPivotMorphism R p C)).toSubmodule =
      ((splitNormalizedMatrix p C).mulVecLin.comp
        (TensorProduct.piScalarRight R A A (ι ⊕ ν)).toLinearMap).ker := by
  let φ := originalMatrixCoefficientEvaluation R C
  let : Algebra (ChartRing R ι ν) A := φ.toAlgebra
  let : IsScalarTower R (ChartRing R ι ν) A :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
  let q := (pivotUniversalMatrix R p).mulVecLin.comp
    (TensorProduct.piScalarRight R (ChartRing R ι ν) (ChartRing R ι ν) (ι ⊕ ν)).toLinearMap
  have hq : Function.Surjective q :=
    originalSplitNormalizedMatrix_tensor_surjective p (universalMatrix R ι ν) R
  have hN := originalGlobalAffinePivotGrassmannianTensorPoint_toSubmodule R p
  have hk := originalMappedQuotientKernel φ
    (originalGlobalAffineGrassmannianTensorPoint R ι ν (originalPivotModelMorphism R p)) q hq hN
  have heval : (pivotUniversalMatrix R p).map (algebraMap (ChartRing R ι ν) A) =
      splitNormalizedMatrix p C := originalMatrixCoefficientEvaluation_pivotMatrix R p C
  have ht := originalMatrixTensorQuotient_baseChange_triangle R (ChartRing R ι ν) A
    (pivotUniversalMatrix R p)
  rw [heval] at ht
  have hkernel : (Algebra.GrassmannQuotientKernel.changedQuotient (B := A) q).ker =
      ((splitNormalizedMatrix p C).mulVecLin.comp
        (TensorProduct.piScalarRight R A A (ι ⊕ ν)).toLinearMap).ker :=
    (LinearEquiv.ker_comp (TensorProduct.piScalarRight (ChartRing R ι ν) A A ι)
      (Algebra.GrassmannQuotientKernel.changedQuotient (B := A) q)).symm.trans
        (congrArg LinearMap.ker ht)
  have hnat := originalGlobalAffineGrassmannianTensorPoint_map R ι ν
    (A := CommRingCat.of (ChartRing R ι ν)) (B := CommRingCat.of A) φ (originalPivotModelMorphism R p)
  exact (congrArg Module.Grassmannian.toSubmodule hnat.symm).trans (hk.trans hkernel)

end Hironaka.Geometry.QuotGrassmann
