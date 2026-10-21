/- Complete original empty-restriction prerequisite, with unchanged type and proof. -/
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.RestrictEmptyTower

open _root_.Hironaka _root_.Hironaka.BlowupSequences
open _root_.Hironaka.BlowupTowers _root_.Hironaka.BlowupTowerTransforms
  _root_.Hironaka.BlowupTowerSplit
open _root_.Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- **If the centres lie over a set disjoint from `U`, the restriction to `U` has only empty centres.** -/
theorem isEmptyTower_restrict_of_centresOver (U : Opens X) {F : Set X} (hUF : Disjoint (U : Set X) F)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (h : CentresOver F T) : IsEmptyTower (restrict U T) :=
  (isEmptyTower_restrict_iff U T).mpr (centresAvoid_of_centresOver U hUF T h)

end

end Hironaka.RestrictEmptyTower
