import Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroSplit
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Stability
import Hironaka.Resolution.HironakaG10HirFlatQuotient

/-! Base change of square-zero split flatness over arbitrary commutative bases. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped TensorProduct DirectSum
open Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroSplit
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroBaseChange
noncomputable section
variable {R S B M : Type} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing B] [Module R B] [AddCommGroup M] [Module R M]

theorem flat_product_modules {R B M : Type} [CommRing R] [AddCommGroup B] [Module R B] [AddCommGroup M] [Module R M] [Module.Flat R B] [Module.Flat R M] : Module.Flat R (B × M) := by
  let C : Bool → Type _ := fun i => if i then M else B
  let _ : ∀ i, AddCommMonoid (C i) := fun i => by cases i <;> dsimp [C] <;> infer_instance
  let _ : ∀ i, Module R (C i) := fun i => by cases i <;> dsimp [C] <;> infer_instance
  let _ : ∀ i, Module.Flat R (C i) := fun i => by cases i <;> dsimp [C] <;> infer_instance
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


/-- After an arbitrary base change, a product with a flat constant summand
is flat exactly when its other summand is flat. -/
theorem flat_baseChange_product_iff [Module.Flat R B] :
    Module.Flat S (S ⊗[R] (B × M)) ↔ Module.Flat S (S ⊗[R] M) := by
  let E := TensorProduct.prodRight R S S B M
  have hs : Module.Flat S (S ⊗[R] B) := inferInstance
  constructor
  · intro h
    let _ := h
    let _ : Module.Flat S ((S ⊗[R] B) × (S ⊗[R] M)) := Module.Flat.of_linearEquiv E.symm
    exact Module.Flat.of_retract (LinearMap.inr S (S ⊗[R] B) (S ⊗[R] M))
      (LinearMap.snd S (S ⊗[R] B) (S ⊗[R] M)) (by ext; rfl)
  · intro h
    let _ := h
    let _ := hs
    let _ : Module.Flat S ((S ⊗[R] B) × (S ⊗[R] M)) := flat_product_modules
    exact Module.Flat.of_linearEquiv E
/-- If an algebra splits linearly as a flat module plus a second summand,
its quotient base change is flat precisely when the second summand is. -/
theorem flat_quotMap_iff_tensor_summand {A C N : Type} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup N] [Module A N] [Module A B] [Module.Flat A B] (E : C ≃ₗ[A] B × N) (I : Ideal A) :
    (Hironaka.HironakaG10HirFlatQuotient.quotMap
      (algebraMap A C) I).Flat ↔ Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] N) := by
  let T := A ⧸ I
  let H := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I
  have hsplit := flat_baseChange_product_iff (R := A) (S := T) (B := B) (M := N)
  have heq : Hironaka.HironakaG10HirFlatQuotient.quotMap
      (algebraMap A C) I = algebraMap T (C ⧸ I.map (algebraMap A C)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  rw [heq, RingHom.flat_algebraMap_iff]
  rw [Module.Flat.equiv_iff H.toLinearEquiv, Module.Flat.equiv_iff (E.baseChange A T C (B × N))]
  exact hsplit

end
end Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroBaseChange
