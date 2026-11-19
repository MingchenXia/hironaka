import Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Entrywise congruence of literal finite matrices controls the whole
parameter-linear matrix map on the entire finite product. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10MatrixIdealCongruence
open Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
noncomputable section

theorem matrix_map_congruent_of_entries
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {a b : ℕ}
    (I : Ideal A) (M N : Matrix (Fin a) (Fin b) B)
    (hentry : ∀ i j, M i j - N i j ∈ I • (⊤ : Submodule A B)) :
    ∀ v : Fin b → B, (M.mulVecLin.restrictScalars A) v -
      (N.mulVecLin.restrictScalars A) v ∈ I • (⊤ : Submodule A (Fin a → B)) := by
  classical
  intro v
  apply (mem_ideal_smul_pi_iff I _).mpr
  intro i
  change (∑ j, M i j * v j) - (∑ j, N i j * v j) ∈ I • (⊤ : Submodule A B)
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro j hj
  have hmap : (I • (⊤ : Submodule A B)).map (LinearMap.mulRight A (v j)) ≤
      I • (⊤ : Submodule A B) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact smul_mono_right I le_top
  have h := hmap (Submodule.mem_map_of_mem (hentry i j))
  simpa only [LinearMap.mulRight_apply, sub_mul] using h
end
end Hironaka.Analytic.Unibranch.HironakaG10MatrixIdealCongruence
