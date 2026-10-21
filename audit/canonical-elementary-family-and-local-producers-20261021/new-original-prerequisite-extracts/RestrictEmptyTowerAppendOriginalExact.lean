/- One complete original tower concatenation prerequisite. Draft only. -/
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.RestrictEmptyTower

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Along a concatenation**: the centres of `T₀.append T₁` avoid `U` iff those of `T₀` avoid `U` and those of `T₁`
avoid the open preimage of `U` in the last stage of `T₀`. -/
theorem centresAvoid_append_iff (U : Opens X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y),
      CentresAvoid U (T₀.append T₁) ↔ CentresAvoid U T₀ ∧ CentresAvoid (openPreimage T₀ U) T₁
  | _, .refl => by simp
  | _, .step T₁ C π hπ => by
    rw [BlowupTower.append_step, centresAvoid_step_iff, centresAvoid_step_iff, centresAvoid_append_iff U T₀ T₁,
      BlowupTower.proj_append, and_assoc]
    rfl

end

end Hironaka.RestrictEmptyTower
