import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The whole original quotient base-change map has its intrinsic original kernel, internally. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.SurjectiveBaseChangeKernel

open scoped TensorProduct

set_option autoImplicit false

universe u v w z
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} {P : Type z} [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P] [Module S P] [IsScalarTower R S P]
  {f : M →ₗ[R] P} (hf : IsBaseChange S f) (hS : Function.Surjective (algebraMap R S))

include hf hS

/-- Surjectivity of the SAME original scalar map internally gives surjectivity of the WHOLE base change. -/
theorem surjective : Function.Surjective f := by
  intro p
  obtain ⟨t, rfl⟩ := hf.equiv.surjective p
  obtain ⟨m, rfl⟩ := TensorProduct.mk_surjective (R := R) (S := S) (M := M) hS t
  exact ⟨m, (one_smul S (f m)).symm⟩

/-- The ENTIRE original base-change kernel is the SAME intrinsic scalar kernel times the original module. -/
theorem eq_zero_iff_mem_kernel_smul (m : M) :
    f m = 0 ↔ m ∈ RingHom.ker (algebraMap R S) • (⊤ : Submodule R M) := by
  let e : (R ⧸ RingHom.ker (algebraMap R S)) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS
  let E := (e.symm.toLinearEquiv.rTensor M).trans
    (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (algebraMap R S)))
  have hE : E ((1 : S) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_one,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  calc
    f m = 0 ↔ (1 : S) ⊗ₜ[R] m = 0 := by
      simpa only [hf.equiv_symm_apply] using (hf.equiv.symm.map_eq_zero_iff (x := f m)).symm
    _ ↔ Submodule.Quotient.mk m = 0 := by
      rw [← hE]
      exact E.map_eq_zero_iff.symm
    _ ↔ m ∈ RingHom.ker (algebraMap R S) • (⊤ : Submodule R M) :=
      Submodule.Quotient.mk_eq_zero _

end DeJongAlterations.StableModificationBridge.SurjectiveBaseChangeKernel
