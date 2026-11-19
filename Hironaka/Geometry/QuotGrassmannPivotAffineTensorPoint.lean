import Hironaka.Geometry.QuotGrassmannPivotAffineNativePoint
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Actual original tensor ambient gives the native Grassmannian functor value

The canonical native original finite-coordinate tensor isomorphism supplies
SAME whole original source, without an ambient comparison certificate.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι] {A : CommRingCat.{u}} [Algebra R A]

/-- SAME actual original affine quotient on its ORIGINAL canonical tensor ambient. -/
def originalGlobalAffineTensorQuotient (f : Spec A ⟶ projectiveModel R ι ν) :
    (A ⊗[R] ((ι ⊕ ν) → R)) →ₗ[A]
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) := by
  classical
  exact (originalGlobalAffinePullbackQuotientSections R ι ν f).comp
    (TensorProduct.piScalarRight R A A (ι ⊕ ν)).toLinearMap

/-- Actual tensor ambient quotient is surjective by its native source isomorphism and SAME original quotient. -/
theorem originalGlobalAffineTensorQuotient_surjective
    (f : Spec A ⟶ projectiveModel R ι ν) :
    Function.Surjective (originalGlobalAffineTensorQuotient R ι ν f) := by
  classical
  exact (originalGlobalAffinePullbackQuotientSections_surjective R ι ν f).comp
    (TensorProduct.piScalarRight R A A (ι ⊕ ν)).surjective

/-- EVERY original pure tensor reads back through SAME original scalar finite coordinates and actual quotient. -/
theorem originalGlobalAffineTensorQuotient_tmul
    (f : Spec A ⟶ projectiveModel R ι ν) (a : A) (v : (ι ⊕ ν) → R) :
    originalGlobalAffineTensorQuotient R ι ν f (a ⊗ₜ[R] v) =
      originalGlobalAffinePullbackQuotientSections R ι ν f (fun i => v i • a) := by
  classical
  simp only [originalGlobalAffineTensorQuotient, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

/-- EVERY original affine test gives a genuine value of native Module.Grassmannian.functor in the ORIGINAL tensor ambient. -/
def originalGlobalAffineGrassmannianTensorPoint (f : Spec A ⟶ projectiveModel R ι ν) :
    Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι) := by
  have h := originalGlobalAffinePullbackSections_finitePresentation_projective R ι ν f
  let := h.1
  let := h.2
  exact Algebra.GrassmannQuotientKernel.point
    (originalGlobalAffineTensorQuotient R ι ν f)
    (originalGlobalAffineTensorQuotient_surjective R ι ν f)
    (Fintype.card ι) (originalGlobalAffinePullbackSections_rankAtStalk R ι ν f)

/-- The ENTIRE original tensor quotient kernel is retained in the native Grassmannian functor value. -/
theorem originalGlobalAffineGrassmannianTensorPoint_toSubmodule
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (originalGlobalAffineGrassmannianTensorPoint R ι ν f).toSubmodule =
      (originalGlobalAffineTensorQuotient R ι ν f).ker := rfl

/-- The produced tensor-ambient native quotient has BOTH whole actual linear maps to SAME original affine sections. -/
def originalGlobalAffineGrassmannianTensorQuotientEquiv
    (f : Spec A ⟶ projectiveModel R ι ν) :
    ((A ⊗[R] ((ι ⊕ ν) → R)) ⧸
      (originalGlobalAffineGrassmannianTensorPoint R ι ν f).toSubmodule) ≃ₗ[A]
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) :=
  (originalGlobalAffineTensorQuotient R ι ν f).quotKerEquivOfSurjective
    (originalGlobalAffineTensorQuotient_surjective R ι ν f)

/-- EVERY original pure tensor retains its actual native Grassmannian quotient and SAME original finite-coordinate readback. -/
theorem originalGlobalAffineGrassmannianTensorQuotientEquiv_mkQ_tmul
    (f : Spec A ⟶ projectiveModel R ι ν) (a : A) (v : (ι ⊕ ν) → R) :
    originalGlobalAffineGrassmannianTensorQuotientEquiv R ι ν f
      ((originalGlobalAffineGrassmannianTensorPoint R ι ν f).toSubmodule.mkQ (a ⊗ₜ[R] v)) =
      originalGlobalAffinePullbackQuotientSections R ι ν f (fun i => v i • a) :=
  (LinearMap.quotKerEquivOfSurjective_apply_mk
    (originalGlobalAffineTensorQuotient R ι ν f)
    (originalGlobalAffineTensorQuotient_surjective R ι ν f) (a ⊗ₜ[R] v)).trans
      (originalGlobalAffineTensorQuotient_tmul R ι ν f a v)

end Hironaka.Geometry.QuotGrassmann
