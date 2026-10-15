/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Manifold.ComplexManifold
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

set_option autoImplicit false

/-! # Faithful point truncations of actual holomorphic germ ideals

Krull separation for the finite quotient module detects membership in any
ideal of the genuine holomorphic germ ring, in every complex dimension.
-/

namespace Hironaka.HolomorphicGermPointTruncationClosure



noncomputable section

private theorem mem_iff_mem_all_maximal_truncations
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (f : R) :
    f ∈ I ↔ ∀ N : ℕ, f ∈ I ⊔ IsLocalRing.maximalIdeal R ^ N := by
  constructor
  · intro hf N
    exact (show I ≤ I ⊔ IsLocalRing.maximalIdeal R ^ N from le_sup_left) hf
  · intro hf
    have hsep := (IsLocalRing.maximalIdeal R).iInf_pow_smul_eq_bot_of_isLocalRing
      (M := R ⧸ I) (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    have hmem : Ideal.Quotient.mk I f ∈
        (⨅ N : ℕ, IsLocalRing.maximalIdeal R ^ N • ⊤ : Submodule R (R ⧸ I)) := by
      rw [Submodule.mem_iInf]
      intro N
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hf N)
      have hq : Ideal.Quotient.mk I f = Ideal.Quotient.mk I b := by
        rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
      rw [hq]
      have hmul := Submodule.smul_mem_smul hb
        (show (1 : R ⧸ I) ∈ (⊤ : Submodule R (R ⧸ I)) from Submodule.mem_top)
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one] using hmul
    rw [hsep] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

/-- Every point truncation detects membership in any genuine holomorphic germ ideal. -/
theorem mem_iff_mem_all_point_truncations (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (f : HolGerm (ComplexModel n)) :
    f ∈ I ↔ ∀ N : ℕ,
      f ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ N := by
  let : IsNoetherianRing (HolGerm (ComplexModel n)) :=
    isNoetherianRing_holGerm_euclidean n
  exact mem_iff_mem_all_maximal_truncations I f

end
end Hironaka.HolomorphicGermPointTruncationClosure
