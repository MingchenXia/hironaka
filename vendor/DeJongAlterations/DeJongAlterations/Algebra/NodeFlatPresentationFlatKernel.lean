import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

/-! # The actual flat-cokernel kernel intersection used by the node presentation -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFlatPresentation

open TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  {N : Type w} [AddCommGroup N] [Module A N]

/-- Tensor injectivity for the actual flat cokernel gives the exact original submodule intersection. -/
theorem ker_inf_smul_top (f : M →ₗ[A] N) (hf : Function.Surjective f) [Module.Flat A N]
    (I : Ideal A) : LinearMap.ker f ⊓ I • (⊤ : Submodule A M) = I • LinearMap.ker f := by
  apply le_antisymm
  · intro x hx
    let y : LinearMap.ker f := ⟨x, hx.1⟩
    have hinj := LinearMap.lTensor_injective_of_exact_of_flat f hf (LinearMap.ker f).subtype
      (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map f) (A ⧸ I)
    have ht : ((LinearMap.ker f).subtype.lTensor (A ⧸ I)) (1 ⊗ₜ[A] y) = 0 := by
      apply (TensorProduct.quotTensorEquivQuotSMul M I).injective
      rw [map_zero, LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx.2
    have hy : (1 : A ⧸ I) ⊗ₜ[A] y = 0 := hinj (by simpa only [map_zero] using ht)
    have hq : Submodule.Quotient.mk (p := I • (⊤ : Submodule A (LinearMap.ker f))) y = 0 := by
      rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, hy, map_zero]
    have hm : y ∈ I • (⊤ : Submodule A (LinearMap.ker f)) :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    exact (Submodule.mem_smul_top_iff I (LinearMap.ker f) y).mp hm
  · exact le_inf (Submodule.smul_le_right) (Submodule.smul_mono le_rfl le_top)

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]

/-- For an actual surjective algebra map with flat target, the actual ideal intersection is a product. -/
theorem ker_inf_extended (f : S →ₐ[A] T) (hf : Function.Surjective f) [Module.Flat A T]
    (I : Ideal A) :
    RingHom.ker f.toRingHom ⊓ I.map (algebraMap A S) =
      I.map (algebraMap A S) * RingHom.ker f.toRingHom := by
  have h := ker_inf_smul_top f.toLinearMap hf I
  have hs : I • (⊤ : Submodule A S) = (I.map (algebraMap A S)).restrictScalars A :=
    Ideal.smul_top_eq_map I
  rw [hs] at h
  have hm := Submodule.restrictScalars_map_smul_eq I (RingHom.ker f.toRingHom)
  rw [Ideal.smul_eq_mul] at hm
  have hk : LinearMap.ker f.toLinearMap = (RingHom.ker f.toRingHom).restrictScalars A := rfl
  rw [hk, ← hm] at h
  ext x
  exact Iff.of_eq (congrArg (fun p : Submodule A S => x ∈ p) h)

end DeJongAlterations.Algebra.NodeFlatPresentation
