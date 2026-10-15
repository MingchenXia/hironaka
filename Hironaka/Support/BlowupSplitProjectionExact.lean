/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupTowerSplit

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set

universe u v

namespace Hironaka.BlowupTowerSplit

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.ResolutionDriver
open Hironaka.ResolutionInvariantSpec (IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}


/-- The projection of the tower is that of the head after that of the tail. -/
theorem proj_eq_comp {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) : T.proj = (head T j).proj ∘ (tail T j).proj := by
  conv_lhs => rw [← head_append_tail T j]
  exact BlowupTower.proj_append _ _

end
end Hironaka.BlowupTowerSplit
