/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Hironaka.OrderTaylor
open Hironaka
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
theorem iterChartDeriv_append (e : ComplexChart n M) (L L' : List (ComplexModel n)) (g : M → ℂ) :
    iterChartDeriv e (L ++ L') g = iterChartDeriv e L (iterChartDeriv e L' g) := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [ih]


end
end Hironaka.OrderTaylor
