import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
import Mathlib.RingTheory.Flat.Basic

/-! Flatness of a square-zero extension as a module is flatness of both summands. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped DirectSum
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroSplit
noncomputable section
variable {R B M : Type} [CommRing R] [CommRing B] [Module R B]
  [AddCommGroup M] [Module R M]

/-- A product of two flat modules is flat. -/
theorem flat_product [Module.Flat R B] [Module.Flat R M] : Module.Flat R (B × M) := by
  let C : Bool → Type _ := fun i => if i then M else B
  letI : ∀ i, AddCommMonoid (C i) := fun i => by cases i <;> dsimp [C] <;> infer_instance
  letI : ∀ i, Module R (C i) := fun i => by cases i <;> dsimp [C] <;> infer_instance
  letI : ∀ i, Module.Flat R (C i) := fun i => by cases i <;> dsimp [C] <;> infer_instance
  let e : (B × M) ≃ₗ[R] (∀ i, C i) := {
    toFun := fun p i => match i with | false => p.1 | true => p.2
    invFun := fun f => (f false,f true)
    left_inv := by intro p; cases p; rfl
    right_inv := by intro f; funext i; cases i <;> rfl
    map_add' := by intro p q; funext i; cases i <;> rfl
    map_smul' := by intro r p; funext i; cases i <;> rfl
  }
  let e' := e.trans (DirectSum.linearEquivFunOnFintype R Bool C).symm
  exact Module.Flat.of_linearEquiv e'

/-- If the constant summand is flat, a square-zero extension is flat exactly
when its linear summand is flat, for the componentwise scalar action. -/
theorem flat_squareZero_iff [Module B M] [Module.Flat R B] :
    Module.Flat R (TrivSqZeroExt B M) ↔ Module.Flat R M := by
  constructor
  · intro h
    letI : Module.Flat R (B × M) := h
    exact Module.Flat.of_retract (LinearMap.inr R B M) (LinearMap.snd R B M) (by ext; rfl)
  · intro h
    letI := h
    have hp : Module.Flat R (B × M) := flat_product
    exact hp
end
end Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroSplit
