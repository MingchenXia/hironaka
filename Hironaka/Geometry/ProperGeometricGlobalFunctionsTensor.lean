import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # A finite field extension whose ACTUAL self tensor is a domain has degree one. -/

noncomputable section
open scoped TensorProduct
namespace Hironaka.Geometry.ProperGeometricGlobalFunctions
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite field extension with ACTUAL domain self tensor has bijective ORIGINAL coefficient map. -/
theorem algebraMap_bijective_of_selfTensor_domain
    (k F : Type u) [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]
    [IsDomain (F ⊗[k] F)] : Function.Bijective (algebraMap k F) := by
  let T := F ⊗[k] F
  let : Algebra.IsIntegral k T := Algebra.IsIntegral.of_finite k T
  let : Field T := (isField_of_isIntegral_of_isField' (Field.toIsField k) : IsField T).toField
  let m : T →ₐ[k] F := Algebra.TensorProduct.lmul' k
  have hm : Function.Bijective m := ⟨m.injective, fun x => ⟨1 ⊗ₜ[k] x, by change (1 : F) * x = x; exact one_mul x⟩⟩
  let e : T ≃ₗ[k] F := LinearEquiv.ofBijective m.toLinearMap hm
  have hd : Module.finrank k F * Module.finrank k F = Module.finrank k F := by
    calc
      _ = Module.finrank k T := (Module.finrank_tensorProduct (R := k) (S := k) (M := F) (M' := F)).symm
      _ = _ := e.finrank_eq
  have hpos : 0 < Module.finrank k F := Module.finrank_pos
  have h1 : Module.finrank k F = 1 := mul_left_cancel₀ (ne_of_gt hpos) (by simpa using hd)
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1

end Hironaka.Geometry.ProperGeometricGlobalFunctions
