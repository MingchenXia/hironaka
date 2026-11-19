import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Complex.Basic

/-! # Scalar extension of the actual continuous bilinear operation -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension

/-- The exact complex-bilinear map underneath a continuous bilinear map. -/
noncomputable def underlyingBilinear {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) : E →ₗ[ℂ] F →ₗ[ℂ] G where
  toFun e := (B e).toLinearMap
  map_add' e e' := by ext f; simp
  map_smul' c e := by ext f; simp

/-- The actual bilinear operation extended to the entire parameter tensor
products, with no tensor norm or completed tensor product. -/
noncomputable def tensorBilinear {Γ E F G : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) :
    (Γ ⊗[ℂ] E) →ₗ[ℂ] (Γ ⊗[ℂ] F) →ₗ[ℂ] (Γ ⊗[ℂ] G) :=
  TensorProduct.curry <|
    (TensorProduct.map (TensorProduct.lift (LinearMap.mul ℂ Γ))
      (TensorProduct.lift (underlyingBilinear B))).comp
        (TensorProduct.tensorTensorTensorComm ℂ Γ E Γ F).toLinearMap

/-- The actual extension multiplies the parameter scalars and applies the
original bilinear map to the original Banach vectors. -/
theorem tensorBilinear_tmul {Γ E F G : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) (a b : Γ) (e : E) (f : F) :
    tensorBilinear B (a ⊗ₜ[ℂ] e) (b ⊗ₜ[ℂ] f) = (a*b) ⊗ₜ[ℂ] B e f := by
  rfl

end Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
