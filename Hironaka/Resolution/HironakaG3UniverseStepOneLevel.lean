import Hironaka.Resolution.HironakaG3UniverseLiftedMarkedHistory
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.Invariant.CodimOnePartCanonical
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseStepOneLevel
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
noncomputable section

/-- Original ordered members agree at each actual lifted test endpoint. -/
theorem origMembers_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) =
      (origMembers M T).map ((liftDiffeomorph.{u} Y).symm ⁻¹' ·) := by
  unfold origMembers
  rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (barMarked_E _) (liftTower.{u} T),
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (barMarked_E _) T,
    liftTower_geoTransformAlong M hM T hT]
  simp only [markedPullback,List.length_map,List.map_take]

/-- Step One's actual boundary-count level is preserved by the literal lift. -/
theorem level_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : liftCMfd.{u} Y) :
    level (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y =
      level M T ((liftDiffeomorph.{u} Y).symm y) := by
  unfold level
  rw [origMembers_liftTower M hM T hT]
  exact CodimOnePartCanonical.boundaryCount_map_preimage (liftDiffeomorph.{u} Y).symm _ y

/-- The same literal boundary-list comparison for the actual Step One test history of barMarked. -/
theorem origMembers_liftTower_barTest {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T) :
    origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) =
      (origMembers M T).map ((liftDiffeomorph.{u} Y).symm ⁻¹' ·) := by
  have hE : (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)).E =
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm (barMarked M)).E := by
    simp only [barMarked_E,markedPullback]
  unfold origMembers
  rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE (liftTower.{u} T),
    liftTower_geoTransformAlong (barMarked M) (StepOneLowerDomain.isWellFormed_barMarked M hM) T hT]
  simp only [markedPullback,List.length_map,List.map_take]

/-- Step One's boundary-count level for its actual bar-marked test history. -/
theorem level_liftTower_barTest {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T) (y : liftCMfd.{u} Y) :
    level (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y =
      level M T ((liftDiffeomorph.{u} Y).symm y) := by
  unfold level
  rw [origMembers_liftTower_barTest M hM T hT]
  exact CodimOnePartCanonical.boundaryCount_map_preimage (liftDiffeomorph.{u} Y).symm _ y
end
end Hironaka.G3UniverseStepOneLevel
