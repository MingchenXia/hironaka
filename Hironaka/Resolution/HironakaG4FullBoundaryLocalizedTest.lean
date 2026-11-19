import Hironaka.Resolution.HironakaG4LocalizedEnlargedTest
import Hironaka.Resolution.HironakaG4BoundaryRestrict
import Hironaka.MarkedIdeal.MarkedIdealEquivalence

/-! A full-boundary test supplies the local normal-crossings history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4FullBoundaryLocalizedTest
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance MarkedIdealOpenBiholomorphism MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  BlowupRestrictOpen HironakaG4LocalizedEnlargedTest HironakaG4BoundaryRestrict

variable {n : ℕ} {X : CMfd.{u} n}

/-- A test tower for the full recorded boundary supplies every local
normal-crossings condition, regardless of the lower record's mark. -/
theorem local_boundary_history_of_full_test
    (Q D : MarkedIdeal n X) (hE : D.E = Q.E) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      LocalBoundaryHistory D U T := by
  intro Y T
  induction T with
  | refl => intro _; trivial
  | @step Y Z T C π hπ ih =>
    intro hTest
    refine ⟨ih hTest.1, ?_⟩
    rw [boundary_geoTransformAlong_restrict,
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T]
    exact hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T U)) hTest.2.2.2

/-- A marked-zero enlarged record is tested locally by the actual lower
history whenever the same history tests its full boundary. -/
theorem restricted_enlarged_test_of_full_boundary
    (P Q D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (hE : D.E = Q.E)
    (U : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (hmark : D.d = 0) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hP : IsGeoTestTower P T) (hQ : IsGeoTestTower Q T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T) :=
  restricted_enlarged_test_of_local_nc P D hPN U hD hmark T hP
    (local_boundary_history_of_full_test Q D hE U T hQ)

end
end Hironaka.HironakaG4FullBoundaryLocalizedTest
