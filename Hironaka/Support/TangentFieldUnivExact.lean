/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.DerivativeIdealAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold

namespace Hironaka.DerivativeIdealAlong

open Hironaka.HolomorphicIdealSheaves DerivativeIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]


variable {N : Set M} {𝔞 𝔟 : GermIdeal n M}

/-- Every vector field is tangent to `N = M` (`𝓘_M` consists of the germs vanishing near `x`). -/
theorem isTangentField_univ {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {x : M}
    (hx : x ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) x) : IsTangentField univ e ξ x := by
  refine ⟨hx, hξ, fun g hg => ⟨?_, ?_⟩⟩
  · have hg0 : g =ᶠ[𝓝 x] fun _ => 0 := hg.2.mono fun p hp => hp (mem_univ p)
    exact holomorphicAt_fieldDeriv hx hξ ((holomorphicAt_const 0).congr hg0.symm)
  · have hg0 : g =ᶠ[𝓝 x] fun _ => 0 := hg.2.mono fun p hp => hp (mem_univ p)
    have hd : ∀ m, chartDeriv e (EuclideanSpace.single m 1) g =ᶠ[𝓝 x]
        chartDeriv e (EuclideanSpace.single m 1) (fun _ => (0 : ℂ)) := fun m => chartDeriv_congr hx hg0
    filter_upwards [eventually_all.2 hd] with p hp _
    have h0 : ∀ m : Fin n, chartDeriv e (EuclideanSpace.single m 1) (fun _ => (0 : ℂ)) p = 0 :=
      fun m => by simp [chartDeriv, Function.comp_def]
    simp only [fieldDeriv, hp, h0, mul_zero, Finset.sum_const_zero]

end
end Hironaka.DerivativeIdealAlong
