import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.Resolution.HironakaG3UniverseOpenDiffeo
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseChartTowerTransport
open Hironaka.BlowupSequences BlowupTowers MarkedIdealTowerTransport
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseOpenDiffeo
noncomputable section

/-- The literal open of the original manifold identifies with the lifted small open. -/
def baseLiftDiffeo {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X₀) (U : Opens X₀) :
    CMfd.of (n := n) (preimageOpens e U) ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
      liftCMfd.{u} (CMfd.of (n := n) U) :=
  (preimageDiffeo e U).symm.trans (liftDiffeomorph.{u} (CMfd.of (n := n) U))

/-- The actual lifted history transported to the literal corresponding original open. -/
def chartTowerTransport {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X₀) (U : Opens X₀)
    (T : BlowupTower (CMfd.of (n := n) U) Y₀) :
    TowerTransport (CMfd.of (n := n) (preimageOpens e U)) (liftCMfd.{u} Y₀) :=
  transport (baseLiftDiffeo e U) (liftTower.{u} T)

/-- The chart tower is finite with the same number of stages. -/
theorem chartTowerTransport_length {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X₀) (U : Opens X₀)
    (T : BlowupTower (CMfd.of (n := n) U) Y₀) :
    (chartTowerTransport e U T).tower.length = T.length := by
  rw [chartTowerTransport, length_transport, liftTower_length]

/-- Its actual projection commutes with the small chart projection. -/
theorem chartTowerTransport_proj {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X₀) (U : Opens X₀)
    (T : BlowupTower (CMfd.of (n := n) U) Y₀) (z : (chartTowerTransport e U T).target) :
    baseLiftDiffeo e U ((chartTowerTransport e U T).tower.proj z) =
      liftDiffeomorph.{u} (CMfd.of (n := n) U)
        (T.proj ((liftDiffeomorph.{u} Y₀).symm ((chartTowerTransport e U T).back z))) := by
  change (baseLiftDiffeo e U) ((transport (baseLiftDiffeo e U) (liftTower.{u} T)).tower.proj z) = _
  calc
    _ = (liftTower.{u} T).proj ((transport (baseLiftDiffeo e U) (liftTower.{u} T)).back z) :=
      proj_transport (baseLiftDiffeo e U) (liftTower.{u} T) z
    _ = _ := congrFun (liftTower_proj.{u} T) _
end
end Hironaka.G3UniverseChartTowerTransport
