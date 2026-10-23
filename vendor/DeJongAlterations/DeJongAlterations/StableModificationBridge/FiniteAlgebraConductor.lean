/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModification.CurvesField.GenusLocal

/-!
# Intrinsic conductor of the entire original algebra map

This is the full conductor of `A → B`, with no chosen generator or monogenic-subalgebra
assumption. It is proved to be the extension of the annihilator of the original native cokernel
`CurvesField.Genus.Coker A B`. Its elements supply actual coefficients in the original ring.

Blueprint: `finite-algebra-conductor.tex`.
-/

universe u v

open DeJongAlterations.StableModification

namespace DeJongAlterations.StableModificationBridge.FiniteAlgebraConductor

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]

/-- The intrinsic full conductor: the largest actual `B`-ideal contained in the image of `A`. -/
def ideal : Ideal B where
  carrier := {b | ∀ c : B, b * c ∈ Set.range (algebraMap A B)}
  zero_mem' c := ⟨0, by simp⟩
  add_mem' hb hc d := by
    obtain ⟨a, ha⟩ := hb d
    obtain ⟨a', ha'⟩ := hc d
    exact ⟨a + a', by rw [map_add, ha, ha', add_mul]⟩
  smul_mem' c b hb d := by
    simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using hb (c * d)

/-- The annihilator of the original native structure-map cokernel. -/
def baseIdeal : Ideal A := Module.annihilator A (CurvesField.Genus.Coker A B)

/-- Intrinsic conductor membership constructs an actual coefficient under the original map. -/
theorem exists_preimage_of_mem {b : B} (hb : b ∈ ideal A B) :
    ∃ a : A, algebraMap A B a = b := by
  simpa only [mul_one, Set.mem_range] using hb 1

/-- The intrinsic ideal is exactly the largest actual ideal contained in the original image. -/
theorem le_ideal_iff (J : Ideal B) :
    J ≤ ideal A B ↔ ∀ b ∈ J, b ∈ Set.range (algebraMap A B) := by
  constructor
  · intro h b hb
    exact exists_preimage_of_mem A B (h hb)
  · intro h b hb c
    exact h (b * c) (J.mul_mem_right c hb)

theorem mem_baseIdeal_iff (a : A) :
    a ∈ baseIdeal A B ↔ algebraMap A B a ∈ ideal A B := by
  constructor
  · intro ha b
    have h := (Module.mem_annihilator.mp ha)
      (Submodule.Quotient.mk b : CurvesField.Genus.Coker A B)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    simpa only [Algebra.smul_def, LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range] using h
  · intro ha
    rw [baseIdeal, Module.mem_annihilator]
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H b =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      simpa only [Algebra.smul_def, LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range] using ha b

theorem baseIdeal_eq_comap : baseIdeal A B = (ideal A B).comap (algebraMap A B) := by
  ext a
  exact mem_baseIdeal_iff A B a

/-- The full intrinsic conductor is the extension of the original cokernel annihilator. -/
theorem map_baseIdeal_eq : (baseIdeal A B).map (algebraMap A B) = ideal A B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (mem_baseIdeal_iff A B a).mp ha
  · intro b hb
    obtain ⟨a, ha⟩ := exists_preimage_of_mem A B hb
    have haI : a ∈ baseIdeal A B := (mem_baseIdeal_iff A B a).mpr (ha ▸ hb)
    rw [← ha]
    exact Ideal.mem_map_of_mem _ haI

end DeJongAlterations.StableModificationBridge.FiniteAlgebraConductor
