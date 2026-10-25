import DeJongAlterations.Algebra.NodeFittingModuleBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Whole intrinsic Fitting ideals under actual semilinear ring-isomorphism transport -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {R : Type u} [CommRing R] {S : Type w} [CommRing S]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type z} [AddCommGroup N] [Module S N]
  (ρ : R ≃+* S)

local instance : RingHomInvPair ρ.toRingHom ρ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv ρ

local instance : RingHomInvPair ρ.symm.toRingHom ρ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm ρ

/-- The identity of the actual coefficient ring with its original semilinear coefficient action. -/
def coefficientSemilinearEquiv :
    letI : Algebra R S := ρ.toRingHom.toAlgebra
    S ≃ₛₗ[ρ.toRingHom] S := by
  letI : Algebra R S := ρ.toRingHom.toAlgebra
  exact {
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl }

/-- Actual native tensor congruence retains the given original semilinear equivalence. -/
def semilinearTensorAux (e : M ≃ₛₗ[ρ.toRingHom] N) :
    letI : Algebra R S := ρ.toRingHom.toAlgebra
    (S ⊗[R] M) ≃ₛₗ[ρ.toRingHom] N := by
  letI : Algebra R S := ρ.toRingHom.toAlgebra
  exact (TensorProduct.congr (coefficientSemilinearEquiv ρ) e).trans (TensorProduct.lid S N)

/-- The same actual tensor equivalence is linear over the actual target coefficient ring. -/
def semilinearTensorEquiv (e : M ≃ₛₗ[ρ.toRingHom] N) :
    letI : Algebra R S := ρ.toRingHom.toAlgebra
    (S ⊗[R] M) ≃ₗ[S] N := by
  letI : Algebra R S := ρ.toRingHom.toAlgebra
  refine {
    toEquiv := (semilinearTensorAux ρ e).toEquiv
    map_add' := (semilinearTensorAux ρ e).map_add
    map_smul' := ?_ }
  intro s x
  have hsrc : s • x = (ρ.symm s) • x := by
    conv_lhs => rw [← ρ.apply_symm_apply s]
    exact algebraMap_smul S (ρ.symm s) x
  calc
    semilinearTensorAux ρ e (s • x) = semilinearTensorAux ρ e ((ρ.symm s) • x) := congrArg _ hsrc
    _ = ρ (ρ.symm s) • semilinearTensorAux ρ e x := (semilinearTensorAux ρ e).map_smulₛₗ _ _
    _ = s • semilinearTensorAux ρ e x := by rw [ρ.apply_symm_apply]

/-- The whole actual pure-tensor coefficient triangle. -/
@[simp]
theorem semilinearTensorEquiv_tmul (e : M ≃ₛₗ[ρ.toRingHom] N) (s : S) (m : M) :
    let : Algebra R S := ρ.toRingHom.toAlgebra
    semilinearTensorEquiv ρ e (s ⊗ₜ m) = s • e m := by
  let : Algebra R S := ρ.toRingHom.toAlgebra
  rfl

/-- The actual inverse uses the same original inverse semilinear module map. -/
@[simp]
theorem semilinearTensorEquiv_symm (e : M ≃ₛₗ[ρ.toRingHom] N) (n : N) :
    let : Algebra R S := ρ.toRingHom.toAlgebra
    (semilinearTensorEquiv ρ e).symm n = 1 ⊗ₜ e.symm n := by
  let : Algebra R S := ρ.toRingHom.toAlgebra
  rfl

/-- Original native finite presentation transports through the actual semilinear coefficient isomorphism. -/
theorem finitePresentation_semilinear [Module.FinitePresentation R M]
    (e : M ≃ₛₗ[ρ.toRingHom] N) : Module.FinitePresentation S N := by
  let : Algebra R S := ρ.toRingHom.toAlgebra
  exact (semilinearTensorEquiv ρ e).finitePresentation_iff.mp inferInstance

/-- The entire intrinsic original Fitting ideal follows the exact actual original coefficient isomorphism. -/
theorem fittingIdeal_semilinear [Module.FinitePresentation R M] [Module.FinitePresentation S N]
    (e : M ≃ₛₗ[ρ.toRingHom] N) (i : ℕ) :
    (fittingIdeal (R := R) (M := M) i).map ρ.toRingHom = fittingIdeal (R := S) (M := N) i := by
  let : Algebra R S := ρ.toRingHom.toAlgebra
  exact (fittingIdeal_baseChange (R := R) (M := M) S i).trans
    (fittingIdeal_equiv (semilinearTensorEquiv ρ e) i)

end DeJongAlterations.Algebra.NodeFittingModule
