/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.OrderTaylor
noncomputable section
open Hironaka IdealWeightPowers HolomorphicIdealSheaves GermIdealOrder RelativePrincipalizationSpan
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable {I : GermIdeal n M} {x : M} {f g : M → ℂ}

/-- `I^m` at `x` is closed under addition. -/
theorem mem_idealPow_add : ∀ {m : ℕ}, (idealPow I m).mem x f → (idealPow I m).mem x g →
    (idealPow I m).mem x (fun p => f p + g p)
  | 0, hf, hg => HolomorphicAt.add hf hg
  | _ + 1, hf, hg => mem_idealPow_succ_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.add
      (mem_idealPow_succ_iff.mp hf) (mem_idealPow_succ_iff.mp hg))

end
end Hironaka.OrderTaylor
