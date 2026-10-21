/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.NormalCrossingsComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.NormalCrossingsComparison

open Hironaka.BlowupSequences NormalCrossings BlowupSNCTransform
  SimultaneousNormalCrossings RegularAtDimTransport RegularPatchPushforward MarkedIdeals
  BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

variable [IsComplexManifold n X]

/-- **Well-formedness passes to a sublist of the divisor.** -/
theorem isWellFormed_withE {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed) {E' : List (Set X)}
    (hE' : E'.Sublist 𝔪.E) : ({ 𝔪 with E := E' } : MarkedIdeal n X).IsWellFormed :=
  ⟨h𝔪.isClosedSubmanifold_N, h𝔪.isCoherent, isSNCDivisor_of_sublist h𝔪.isSNCDivisor hE',
    isTransverse_of_forall_mem h𝔪.isTransverse fun _ hH => hE'.subset hH⟩

end Hironaka.NormalCrossingsComparison
