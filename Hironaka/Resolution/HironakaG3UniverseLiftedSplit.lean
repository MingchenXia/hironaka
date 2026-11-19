import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.Blowup.BlowupTowerSplit
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseLiftedSplit
open Hironaka.BlowupSequences BlowupTowers BlowupTowerSplit
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower
noncomputable section

/-- Literal splitting commutes with universe lift, retaining both physical tower halves. -/
theorem liftTower_split {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y) (j : ℕ) :
    split (liftTower.{u} T) j =
      ⟨liftCMfd.{u} (split T j).1, liftTower.{u} (head T j), liftTower.{u} (tail T j)⟩ := by
  induction T generalizing j with
  | refl => cases j <;> rfl
  | @step Y Z T C π hπ ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [liftTower,split]
      rw [ih j]
      rfl
end
end Hironaka.HironakaG3UniverseLiftedSplit
