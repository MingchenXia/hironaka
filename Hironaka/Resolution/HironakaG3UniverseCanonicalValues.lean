import Hironaka.Resolution.HironakaG3UniverseGenericCanonicalValues
import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Invariant.CanonicalCentres
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseCanonicalValues
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
  HironakaG3UniverseLiftedTestHistory G3UniverseMarkedCosupport ResolutionDriver
open ResolutionInvariantSpec (IsCanonical)
open G3UniverseGenericCanonicalValues
noncomputable section

/-- Equality of the actual recursive invariant values at each original recorded prefix.
This is an explicit compatibility condition, not a theorem asserting it. -/
def LiftedOriginalValuesAgree {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (M : MarkedIdeal n X) : {Y : CMfd.{0} n} → BlowupTower X Y → Prop :=
  LiftedValuesAgree (fun {X} J {Y} T y => (invFamily.{0} hn k).inv (X := X) J (Y := Y) T y)
    (fun {X} J {Y} T y => (invFamily.{u} hn k).inv (X := X) J (Y := Y) T y) M

/-- Supplied original-value agreement transfers canonicality to the literal lift. -/
theorem liftTower_isCanonical_of_values {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
    IsCanonical M ((invFamily.{0} hn k).inv M) T → LiftedOriginalValuesAgree.{u} (k := k) hn M T →
    IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      ((invFamily.{u} hn k).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M))
      (liftTower.{u} T)
  | _, T, hT, hcan, hval =>
      liftTower_isCanonical_of_values_generic _ _ M hM T hT hcan hval
/-- The depth-zero recursive invariant has literal cross-universe agreement. -/
theorem liftedOriginalValuesAgree_zero {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) : LiftedOriginalValuesAgree.{u} (k := 0) hn M T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih => exact ⟨ih,fun _ _ => rfl⟩

/-- Depth-zero canonicality transfers without a separate value-equality premise. -/
theorem liftTower_isCanonical_zero {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (hcan : IsCanonical M ((invFamily.{0} hn 0).inv M) T) :
    IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      ((invFamily.{u} hn 0).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M))
      (liftTower.{u} T) :=
  liftTower_isCanonical_of_values hn M hM T hT hcan (liftedOriginalValuesAgree_zero hn M T)
end
end Hironaka.HironakaG3UniverseCanonicalValues
