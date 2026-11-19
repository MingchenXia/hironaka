import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Entire original-linear completion maps from their actual original values

Only the actual finitely generated ideal, native coordinate kernels and native
original module actions are used. No completed target action or continuity input.
-/

noncomputable section

namespace Hironaka.Algebra.NodeFittingCompletionDensity

universe u v w
variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

include hI

/-- Actual original linearity preserves the ENTIRE native source coordinate filtration. -/
theorem linearMap_filtration (L : AdicCompletion I M →ₗ[R] N)
    (n : ℕ) (x : AdicCompletion I M) (hx : x.val n = 0) :
    L x ∈ (I ^ n • ⊤ : Submodule R N) := by
  have hmem : x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact hx
  have hle : Submodule.map L (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) ≤
      (I ^ n • ⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact hle (Submodule.mem_map_of_mem hmem)

/-- Equality on EVERY actual original element determines the ENTIRE original-linear map into a native Hausdorff target. -/
theorem linearMap_ext [IsHausdorff I N] (L H : AdicCompletion I M →ₗ[R] N)
    (hOriginal : ∀ m : M, L (AdicCompletion.of I M m) = H (AdicCompletion.of I M m)) :
    L = H := by
  apply LinearMap.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have hzero : (x - AdicCompletion.of I M m).val n = 0 := by
    rw [AdicCompletion.val_sub_apply]
    apply sub_eq_zero.mpr
    exact hm.symm
  have hL := linearMap_filtration I hI L n _ hzero
  have hH := linearMap_filtration I hI H n _ hzero
  rw [map_sub, hOriginal] at hL
  rw [map_sub] at hH
  rw [SModEq.sub_mem]
  convert Submodule.sub_mem _ hL hH using 1; abel

variable {T : Type w} [CommRing T] [Algebra R T] [IsHausdorff I T]

/-- Actual original algebra maps agree on the WHOLE completion, without a continuity certificate. -/
theorem algHom_ext (F G : AdicCompletion I R →ₐ[R] T) : F = G := by
  apply AlgHom.ext
  intro x
  apply LinearMap.congr_fun (linearMap_ext I hI F.toLinearMap G.toLinearMap ?_) x
  intro r
  change F (algebraMap R (AdicCompletion I R) r) = G (algebraMap R (AdicCompletion I R) r)
  rw [F.commutes, G.commutes]

end Hironaka.Algebra.NodeFittingCompletionDensity
