import Hironaka.Geometry.QuotGrassmannPivotAffineGlobalSourceTriangle
import Hironaka.Geometry.QuotGrassmannPivotAffineTensorPoint
import Hironaka.Algebra.PluckerQuotTransitionTensorCoordinates

/-!
# SAME actual original tensor quotient under native affine base change

The canonical source triangle and original tensor cancellation derive the
WHOLE original quotient equality with the SAME actual section target map.
No original scalar or quotient compatibility is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]
  {A B : CommRingCat.{u}} [Algebra R A] [Algebra R B]

/-- WHOLE SAME actual original tensor quotient is the native changed quotient followed by the actual affine-section target isomorphism. -/
theorem originalGlobalAffineTensorQuotient_baseChange (φ : A →ₐ[R] B)
    (f : Spec A ⟶ projectiveModel R ι ν) :
    letI : Algebra A B := φ.toAlgebra
    letI : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
    originalGlobalAffineTensorQuotient R ι ν (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f) =
      (originalGlobalAffineImageSectionsBaseChangeIso R ι ν
        (CommRingCat.ofHom φ.toRingHom) f).hom.hom.comp
          (Algebra.GrassmannQuotientKernel.changedQuotient
            (originalGlobalAffineTensorQuotient R ι ν f)) := by
  classical
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
  let φr : A ⟶ B := CommRingCat.ofHom φ.toRingHom
  let qA := originalGlobalAffinePullbackQuotientSections R ι ν f
  let qB := originalGlobalAffinePullbackQuotientSections R ι ν (Spec.map φr ≫ f)
  let e := originalGlobalAffineImageSectionsBaseChangeIso R ι ν φr f
  let πA := (TensorProduct.piScalarRight R A A (ι ⊕ ν)).toLinearMap
  let πB := (TensorProduct.piScalarRight R B B (ι ⊕ ν)).toLinearMap
  let πAB := (TensorProduct.piScalarRight A B B (ι ⊕ ν)).toLinearMap
  let c := (AlgebraTensorModule.cancelBaseChange R A B B ((ι ⊕ ν) → R)).symm.toLinearMap
  have hs := originalGlobalAffineQuotientSections_scalar_square R ι ν φr f
  have hb : e.hom.hom.comp (qA.baseChange B) = qB.comp πAB := by
    exact congrArg ModuleCat.Hom.hom hs
  have ht : (πAB.comp (πA.baseChange B)).comp c = πB :=
    Algebra.PluckerQuotTransition.originalTensorCoordinate_cancelBaseChange R A B (ι ⊕ ν)
  calc
    _ = qB.comp πB := rfl
    _ = qB.comp ((πAB.comp (πA.baseChange B)).comp c) := congrArg (fun k => qB.comp k) ht.symm
    _ = ((qB.comp πAB).comp (πA.baseChange B)).comp c := by
      simp only [LinearMap.comp_assoc]
    _ = ((e.hom.hom.comp (qA.baseChange B)).comp (πA.baseChange B)).comp c :=
      congrArg (fun k => (k.comp (πA.baseChange B)).comp c) hb.symm
    _ = _ := by
      simp only [Algebra.GrassmannQuotientKernel.changedQuotient,
        originalGlobalAffineTensorQuotient, LinearMap.baseChange_comp, LinearMap.comp_assoc,
        e, φr, qA, πA, c]

end Hironaka.Geometry.QuotGrassmann
