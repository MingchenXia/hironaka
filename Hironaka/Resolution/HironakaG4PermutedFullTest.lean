import Hironaka.Resolution.HironakaG4FullBoundaryLocalizedTest
import Hironaka.Blowup.NormalCrossingsComparison

/-! Full-boundary tests work for reordered initial boundary lists. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4PermutedFullTest
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance MarkedIdealOpenBiholomorphism
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism BlowupRestrictOpen
  HironakaG4LocalizedEnlargedTest HironakaG4BoundaryRestrict

variable {n : ℕ} {X : CMfd.{u} n}

/-- Reordering a boundary commutes with its geometric transformation. -/
theorem perm_geoTransformAlong_boundary (D Q : MarkedIdeal n X) (hE : D.E.Perm Q.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong D T).E.Perm (geoTransformAlong Q T).E := by
  intro Y T
  induction T with
  | refl => exact hE
  | @step Y Z T C π hπ ih =>
    change (((geoTransformAlong D T).E.map (geoStrictTransform π C)) ++ [_]).Perm
      (((geoTransformAlong Q T).E.map (geoStrictTransform π C)) ++ [_])
    exact (ih.map _).append_right _

/-- The full test supplies the local boundary history after any reordering. -/
theorem local_boundary_history_of_permuted_full_test
    (Q D : MarkedIdeal n X) (hE : D.E.Perm Q.E) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      LocalBoundaryHistory D U T := by
  intro Y T
  induction T with
  | refl => intro _; trivial
  | @step Y Z T C π hπ ih =>
    intro hTest
    refine ⟨ih hTest.1, ?_⟩
    rw [boundary_geoTransformAlong_restrict]
    have hNC : HasNormalCrossings n C (geoTransformAlong D T).E :=
      hasNormalCrossings_of_forall_mem hTest.2.2.2 (perm_geoTransformAlong_boundary D Q hE T).subset
    exact hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T U)) hNC

/-- Reordered full-boundary tests imply the localized enlarged test. -/
theorem restricted_enlarged_test_of_permuted_full_boundary
    (P Q D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (hE : D.E.Perm Q.E)
    (U : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (hmark : D.d = 0) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hP : IsGeoTestTower P T) (hQ : IsGeoTestTower Q T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T) :=
  restricted_enlarged_test_of_local_nc P D hPN U hD hmark T hP
    (local_boundary_history_of_permuted_full_test Q D hE U T hQ)

end
end Hironaka.HironakaG4PermutedFullTest
