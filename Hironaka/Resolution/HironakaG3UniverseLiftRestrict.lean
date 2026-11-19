import Hironaka.Resolution.HironakaG3UniverseChartTowerTransport
import Hironaka.Blowup.BlowupTowerIsomorphism
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseLiftRestrict
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsoTail BlowupTowerIsomorphism HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower G3UniverseOpenDiffeo G3UniverseChartTowerTransport
noncomputable section

/-- The inverse image open of a lifted tower is the lift of the original inverse image. -/
theorem lifted_openPreimage_eq {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y) (U : Opens X) :
    openPreimage (liftTower.{u} T) (preimageOpens (liftDiffeomorph.{u} X).symm U) =
      preimageOpens (liftDiffeomorph.{u} Y).symm (openPreimage T U) := by
  apply Opens.ext
  ext y
  change (liftDiffeomorph.{u} X).symm ((liftTower.{u} T).proj y) ∈ (U : Set X) ↔
    T.proj ((liftDiffeomorph.{u} Y).symm y) ∈ (U : Set X)
  rw [liftTower_proj]
  simp

/-- Actual endpoint equivalence between the restricted lift and the lift of the restriction. -/
def lifted_restrictEndpoint {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y) (U : Opens X) :
    CMfd.of (n := n) (openPreimage (liftTower.{u} T) (preimageOpens (liftDiffeomorph.{u} X).symm U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} (CMfd.of (n := n) (openPreimage T U)) :=
  (opensCongr (lifted_openPreimage_eq T U)).trans
    (baseLiftDiffeo (liftDiffeomorph.{u} Y).symm (openPreimage T U))

/-- Restricting a literal lifted tower is physically isomorphic to lifting its restriction. -/
theorem liftTower_restrict_isTowerIso {n : ℕ} {X : CMfd.{0} n} (U : Opens X) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) →
    IsTowerIso (baseLiftDiffeo (liftDiffeomorph.{u} X).symm U)
      (restrict (preimageOpens (liftDiffeomorph.{u} X).symm U) (liftTower.{u} T))
      (liftTower.{u} (restrict U T)) (lifted_restrictEndpoint T U)
  | _, .refl => by
    have h : lifted_restrictEndpoint (BlowupTower.refl : BlowupTower X X) U =
        baseLiftDiffeo (liftDiffeomorph.{u} X).symm U := by
      ext x
      rfl
    rw [h]
    exact IsTowerIso.refl
  | _, .step T C π hπ => by
    apply IsTowerIso.step (liftTower_restrict_isTowerIso U T) _ _ (lifted_restrictEndpoint (.step T C π hπ) U)
    · intro p
      rfl
    · ext p
      rfl
end
end Hironaka.G3UniverseLiftRestrict
