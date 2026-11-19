import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseStrictAlong
open Hironaka.BlowupSequences BlowupTowers HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HomogenizedGlueingTower BlowupStrictSubmanifold
noncomputable section

/-- The actual iterated strict transform of any set commutes with literal tower lift. -/
theorem strictAlong_liftTower {n : ℕ} {X : CMfd.{0} n} (A : Set X) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) →
    strictAlong (liftTower.{u} T) ((liftDiffeomorph.{u} X).symm ⁻¹' A) =
      (liftDiffeomorph.{u} Y).symm ⁻¹' strictAlong T A
  | _, .refl => rfl
  | Z, .step T C π hπ => by
    simp only [liftTower, strictAlong_step, strictAlong_liftTower A T]
    unfold geoStrictTransform
    have hcl (S : Set Z) : (liftDiffeomorph.{u} Z).symm ⁻¹' closure S =
        closure ((liftDiffeomorph.{u} Z).symm ⁻¹' S) :=
      (liftDiffeomorph.{u} Z).symm.toHomeomorph.preimage_closure S
    rw [hcl]
    congr 1
end
end Hironaka.G3UniverseStrictAlong
