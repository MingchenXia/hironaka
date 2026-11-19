import Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Parameter reduction on whole tensor modules and genuine flat relation lifting

For a complex parameter algebra with a residue homomorphism, the kernel of
reduction on its whole scalar extension is exactly the residue ideal multiple.
Thus a relation after actual residue reduction lifts if the actual cokernel is
flat over the parameter algebra.  Neither a lifted relation nor an ideal
intersection condition is supplied.  Compact holomorphic globalization remains
a separate analytic step.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift

open Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift

noncomputable section

variable {Q E : Type*} [CommRing Q] [Algebra ℂ Q]
  [AddCommGroup E] [Module ℂ E]

/-- Actual reduction of the entire scalar-extended module along the residue
homomorphism of the parameter algebra. -/
def residueTensor (ε : Q →ₐ[ℂ] ℂ) : Q ⊗[ℂ] E →ₗ[ℂ] E :=
  (TensorProduct.lid ℂ E).toLinearMap.comp (ε.toLinearMap.rTensor E)

@[simp]
theorem residueTensor_tmul (ε : Q →ₐ[ℂ] ℂ) (a : Q) (e : E) :
    residueTensor ε (a ⊗ₜ[ℂ] e) = ε a • e := by
  simp [residueTensor]

/-- Reduction intertwines the genuine parameter action with its residue. -/
theorem residueTensor_smul (ε : Q →ₐ[ℂ] ℂ) (a : Q) (x : Q ⊗[ℂ] E) :
    residueTensor ε (a • x) = ε a • residueTensor ε x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [TensorProduct.smul_tmul', mul_smul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Reduction zero is a submodule for the actual parameter action. -/
def residueKernel (ε : Q →ₐ[ℂ] ℂ) : Submodule Q (Q ⊗[ℂ] E) where
  carrier := {x | residueTensor ε x = 0}
  zero_mem' := map_zero _
  add_mem' {x y} hx hy := by
    change residueTensor ε x = 0 at hx
    change residueTensor ε y = 0 at hy
    change residueTensor ε (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  smul_mem' a x hx := by
    change residueTensor ε x = 0 at hx
    change residueTensor ε (a • x) = 0
    rw [residueTensor_smul, hx, smul_zero]

theorem residueIdeal_smul_le_residueKernel (ε : Q →ₐ[ℂ] ℂ) :
    RingHom.ker ε.toRingHom • (⊤ : Submodule Q (Q ⊗[ℂ] E)) ≤ residueKernel ε := by
  rw [Submodule.smul_le]
  intro a ha x _
  change residueTensor ε (a • x) = 0
  have ha0 : ε a = 0 := ha
  rw [residueTensor_smul, ha0, zero_smul]

/-- Subtracting the constant lift of the residue leaves precisely a residue
ideal multiple in the whole tensor module. -/
theorem sub_unit_tmul_residue_mem (ε : Q →ₐ[ℂ] ℂ) (x : Q ⊗[ℂ] E) :
    x - (1 : Q) ⊗ₜ[ℂ] residueTensor ε x ∈
      RingHom.ker ε.toRingHom • (⊤ : Submodule Q (Q ⊗[ℂ] E)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have ha : a - algebraMap ℂ Q (ε a) ∈ RingHom.ker ε.toRingHom := by
      change ε (a - algebraMap ℂ Q (ε a)) = 0
      rw [map_sub, ε.commutes]
      simp
    have hmem := Submodule.smul_mem_smul ha
      (show (1 : Q) ⊗ₜ[ℂ] e ∈ (⊤ : Submodule Q (Q ⊗[ℂ] E)) from trivial)
    convert hmem using 1
    simp [TensorProduct.smul_tmul', TensorProduct.sub_tmul,
      TensorProduct.tmul_smul, Algebra.smul_def]
  | add x y hx hy =>
    have h := (RingHom.ker ε.toRingHom • (⊤ : Submodule Q (Q ⊗[ℂ] E))).add_mem hx hy
    simpa only [map_add, TensorProduct.tmul_add, add_sub_add_comm] using h

/-- The actual kernel of residue reduction is the full residue-ideal
multiple, without a finite-dimensionality or nilpotence hypothesis. -/
theorem residueTensor_eq_zero_iff_mem_ideal_smul (ε : Q →ₐ[ℂ] ℂ) (x : Q ⊗[ℂ] E) :
    residueTensor ε x = 0 ↔
      x ∈ RingHom.ker ε.toRingHom • (⊤ : Submodule Q (Q ⊗[ℂ] E)) := by
  constructor
  · intro hx
    have h := sub_unit_tmul_residue_mem ε x
    simpa only [hx, TensorProduct.tmul_zero, sub_zero] using h
  · intro hx
    exact residueIdeal_smul_le_residueKernel (E := E) ε hx

variable {P N : Type*} [AddCommGroup P] [Module ℂ P]
  [AddCommGroup N] [Module ℂ N]

/-- A residue relation lifts to an actual relation when the actual
parameter-module cokernel is flat. -/
theorem exists_relation_lift_of_residue_zero (ε : Q →ₐ[ℂ] ℂ)
    (F : (Q ⊗[ℂ] P) →ₗ[Q] (Q ⊗[ℂ] N))
    [Module.Flat Q ((Q ⊗[ℂ] N) ⧸ LinearMap.range F)]
    (p : Q ⊗[ℂ] P) (hp : residueTensor ε (F p) = 0) :
    ∃ k : Q ⊗[ℂ] P, F k = 0 ∧ residueTensor ε k = residueTensor ε p := by
  let : Module.Flat Q (Q ⊗[ℂ] N) :=
    Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension.flat_tensor_complex
  obtain ⟨k, hk, hmod⟩ := exists_relation_lift_mod_of_flat F
    (RingHom.ker ε.toRingHom) p ((residueTensor_eq_zero_iff_mem_ideal_smul ε _).mp hp)
  refine ⟨k, hk, ?_⟩
  have hz := (residueTensor_eq_zero_iff_mem_ideal_smul ε (p - k)).mpr hmod
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

end

end Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift
