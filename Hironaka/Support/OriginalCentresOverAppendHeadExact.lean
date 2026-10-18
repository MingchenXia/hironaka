/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.RestrictEmptyTower
noncomputable section
open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit
variable {n : ℕ} {X : CMfd.{u} n}

theorem centresOver_step_iff (F : Set X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) : CentresOver F (.step T C π hπ) ↔ CentresOver F T ∧ C ⊆ T.proj ⁻¹' F :=
  Iff.rfl

/-- **Along a concatenation**: the centres of `T₀.append T₁` lie over `F` iff those of `T₀` do and those of `T₁` lie
over the preimage of `F` in the last stage of `T₀`. -/
theorem centresOver_append_iff (F : Set X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y),
      CentresOver F (T₀.append T₁) ↔ CentresOver F T₀ ∧ CentresOver (T₀.proj ⁻¹' F) T₁
  | _, .refl => by simp
  | _, .step T₁ C π hπ => by
    rw [BlowupTower.append_step, centresOver_step_iff, centresOver_step_iff, centresOver_append_iff F T₀ T₁,
      BlowupTower.proj_append, and_assoc]
    rfl

/-- **The head of a split lies over `F` if the tower does.** -/
theorem centresOver_head (F : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) (h : CentresOver F T) :
    CentresOver F (head T j) := by
  have h' : CentresOver F ((head T j).append (tail T j)) := (head_append_tail T j).symm ▸ h
  exact ((centresOver_append_iff F (head T j) (tail T j)).mp h').1

end
end Hironaka.RestrictEmptyTower
