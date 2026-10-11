/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.EmbeddedFromResolution

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.EmbeddedFromResolution
open Hironaka BlowupSequences BlowupTowers RestrictEmptyTower
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}
/-- **The exceptional image lies off an open set the centres miss.** -/
theorem image_exceptionalLocus_subset_compl (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (h : CentresAvoid U T) : T.proj '' exceptionalLocus n T.proj ⊆ (U : Set X)ᶜ := by
  rintro _ ⟨y, hy, rfl⟩ hyU
  exact notMem_exceptionalLocus_of_centresAvoid U T h y hyU hy

end
end Hironaka.EmbeddedFromResolution
