/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Coherence.CoherentIdealColon

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold

namespace Hironaka.CoherentIdealColon

open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf OkaIdealOperations
  CartanLocalReduction InvertibleIdealQuotient

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Membership in the span of the range of a finite family, with one coefficient per
generator. -/
theorem isInSpanAt_range_iff {N : ℕ} {S : Fin N → M → ℂ} {y : M} {f : M → ℂ} :
    IsInSpanAt (n := n) (· ∈ range S) y f ↔ HolomorphicAt n f y ∧
      ∃ c : Fin N → M → ℂ, (∀ i, HolomorphicAt n (c i) y) ∧
        f =ᶠ[𝓝 y] fun p => ∑ i, c i p * S i p := by
  classical
  constructor
  · rintro ⟨hf, N', s', a, hs', ha, hfa⟩
    choose σ hσ using hs'
    refine ⟨hf, fun i p => ∑ j, if σ j = i then a j p else 0, fun i => ?_, ?_⟩
    · refine HolomorphicAt.sum _ fun j _ => ?_
      split_ifs
      · exact ha j
      · exact holomorphicAt_const 0
    · filter_upwards [hfa] with p hp
      rw [hp]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← hσ j]
  · rintro ⟨hf, c, hc, hfc⟩
    exact ⟨hf, N, S, c, fun i => ⟨i, rfl⟩, hc, hfc⟩

end Hironaka.CoherentIdealColon
