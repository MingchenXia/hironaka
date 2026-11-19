import Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroBaseChange

/-! Flatness over one quotient passes to every further quotient, retaining
the literal tensor-base-changed module. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatNestedQuotientBaseChange
noncomputable section

/-- Flatness after quotienting by I yields flatness after quotienting by any
larger ideal L, for the same original module. -/
theorem flat_tensor_of_flat_quotient {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (I L : Ideal R) (hIL : I ≤ L)
    (hflat : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    Module.Flat (R ⧸ L) ((R ⧸ L) ⊗[R] M) := by
  let B := R ⧸ I
  let Q := R ⧸ L
  let _ : Algebra B Q := (Ideal.Quotient.factor hIL).toAlgebra
  let _ : IsScalarTower R B Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : Module.Flat B (B ⊗[R] M) := hflat
  have hQ : Module.Flat Q (Q ⊗[B] (B ⊗[R] M)) := inferInstance
  let _ := hQ
  exact Module.Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q Q M).symm
end
end Hironaka.Analytic.Unibranch.HironakaG10FlatNestedQuotientBaseChange
