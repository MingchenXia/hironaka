/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerSplit

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.BlowupTowerSplit
noncomputable section
universe u
open Hironaka BlowupSequences BlowupTowers
variable {n : ℕ} {X : CMfd.{u} n}

theorem head_step_succ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (j : ℕ) : head (.step T C π hπ) (j + 1) = head T j := rfl

theorem tail_step_succ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (j : ℕ) : tail (.step T C π hπ) (j + 1) = .step (tail T j) C π hπ := rfl


end
end Hironaka.BlowupTowerSplit
