import Hironaka.Resolution.HironakaG3UniverseLiftedBlowup
set_option autoImplicit false
set_option maxHeartbeats 3000000
universe u

namespace Hironaka.G3UniverseLiftedTower
open Set Function
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences BlowupTowers HironakaG3UniverseLiftManifold
  G3UniverseLiftedBlowup
noncomputable section

/-- Every actual finite blowup tower lifts with all of its stages retained. -/
def liftTower {n : ℕ} {X₀ : CMfd.{0} n} :
    {Y₀ : CMfd.{0} n} → BlowupTower X₀ Y₀ →
      BlowupTower (liftCMfd.{u} X₀) (liftCMfd.{u} Y₀)
  | _, .refl => .refl
  | _, .step T C π hπ =>
      .step (liftTower T) ((liftDiffeomorph.{u} _).symm ⁻¹' C)
        ((liftDiffeomorph.{u} _) ∘ π ∘ (liftDiffeomorph.{u} _).symm) (lifted_blowup hπ)

/-- Lifting preserves the literal finite stage count. -/
theorem liftTower_length {n : ℕ} {X₀ Y₀ : CMfd.{0} n} (T : BlowupTower X₀ Y₀) :
    (liftTower.{u} T).length = T.length := by
  induction T with
  | refl => rfl
  | step T C π hπ ih => simp [liftTower,ih]

/-- The lifted tower projection is the literal conjugate of the original projection. -/
theorem liftTower_proj {n : ℕ} {X₀ Y₀ : CMfd.{0} n} (T : BlowupTower X₀ Y₀) :
    (liftTower.{u} T).proj = (liftDiffeomorph.{u} X₀) ∘ T.proj ∘ (liftDiffeomorph.{u} Y₀).symm := by
  induction T with
  | refl =>
    funext y
    simp [liftTower,Function.comp_apply]
  | @step Y₀ Z₀ T C π hπ ih =>
    funext z
    simp [liftTower,BlowupTower.proj_step,Function.comp_apply,ih]
end
end Hironaka.G3UniverseLiftedTower
