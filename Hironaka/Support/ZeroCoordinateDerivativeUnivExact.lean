/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealCoherence
import Hironaka.Support.TangentFieldUnivExact

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DerivativeIdealAlong
open Hironaka.HolomorphicIdealSheaves Hironaka.DerivativeIdeal
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable {N : Set M} {𝔞 𝔟 : GermIdeal n M}

theorem derivIdealAlong_univ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    derivIdealAlong univ 𝔞 = derivIdeal 𝔞 := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hg
    rintro s (hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩)
    · exact isInSpanAt_of_eq_mul (Or.inl hs) (h𝔞 x s hs) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    · -- a germ vanishing near `x` is `0 · 1`
      have hs0 : s =ᶠ[𝓝 x] fun _ => 0 := hs.2.mono fun p hp => hp (mem_univ p)
      exact ⟨hs.1, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simpa using hs0⟩
    · refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun m _ => ?_
      exact isInSpanAt_of_eq_mul (Or.inr ⟨e, EuclideanSpace.single m 1, f, hξ.mem_source, hf, rfl⟩)
        ((hξ.holomorphicAt m).mul (holomorphicAt_chartDeriv hξ.mem_source (h𝔞 x f hf)))
        (hξ.holomorphicAt m) (Eventually.of_forall fun _ => rfl)
  · refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hg
    rintro s (hs | ⟨e, v, f, hx, hf, rfl⟩)
    · exact isInSpanAt_of_eq_mul (Or.inl hs) (h𝔞 x s hs) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    · -- `∂_v f = ∑ₘ vₘ ∂_{eₘ} f`, the field with constant coefficients `vₘ`
      refine isInSpanAt_of_eq_mul (s := fieldDeriv e (fun m _ => v m) f)
        (Or.inr (Or.inr ⟨e, fun m _ => v m, f,
          isTangentField_univ hx fun m => holomorphicAt_const _, hf, rfl⟩))
        (holomorphicAt_chartDeriv hx (h𝔞 x f hf)) (holomorphicAt_const 1) ?_
      refine Eventually.of_forall fun p => ?_
      simp only [fieldDeriv, chartDeriv, one_mul]
      conv_lhs => rw [← sum_smul_single v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul, smul_eq_mul]

theorem iterDerivIdealAlong_univ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ j, iterDerivIdealAlong univ 𝔞 j = iterDerivIdeal 𝔞 j
  | 0 => rfl
  | j + 1 => by
    rw [iterDerivIdealAlong, iterDerivIdealAlong_univ h𝔞 j, iterDerivIdeal_succ,
      derivIdealAlong_univ (holomorphicAt_of_mem_iterDerivIdeal h𝔞 j)]

end
end Hironaka.DerivativeIdealAlong
