import Hironaka.Resolution.HironakaG8ContactStageAmbient
import Hironaka.Resolution.HironakaG8ClassStepHistory

/-!
# Actual ambient carriers along common test towers

A closed hypersurface carrier and its well-formed ambient carrier retain their
literal inclusion and dimensions along any tower which tests both records.
The original ordered boundary remains equal along the tower.
-/
set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTAmbientStage
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  BlowupStrictSubmanifold NormalCrossings HironakaG8P1ArcCarrierPlane

/-- A genuine codimension-one carrier in a well-formed ambient record retains
its ambient carrier, its full boundary and its dimensions along a common test
tower. All hypotheses concern the actual starting records and tower. -/
theorem ambient_hypersurface_along_common_test
    {n : ℕ} {X Y : CMfd.{u} n} (P R : MarkedIdeal n X)
    (hP : P.IsWellFormed) (hR : R.IsWellFormed) (hsub : P.N ⊆ R.N)
    (F : List (Set X)) (hE : R.E = F ++ P.E)
    (hdim : ∀ x ∈ P.N, ∃ m, RegularAtDim (n := n) R.N x (m+1) ∧
      RegularAtDim (n := n) P.N x m)
    (T : BlowupTower X Y) (hTP : IsGeoTestTower P T)
    (hTR : IsGeoTestTower R T) {y : Y} (hy : y ∈ (geoTransformAlong P T).N) :
    (geoTransformAlong R T).IsWellFormed ∧
      (geoTransformAlong P T).N ⊆ (geoTransformAlong R T).N ∧
      (geoTransformAlong R T).E =
        (geoTransformAlong { P with E := F ++ P.E } T).E ∧
      ∃ m, RegularAtDim (n := n) (geoTransformAlong R T).N y (m+1) ∧
        RegularAtDim (n := n) (geoTransformAlong P T).N y m := by
  have hRstage := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hR T hTR
  have hsubStage : (geoTransformAlong P T).N ⊆ (geoTransformAlong R T).N := by
    simpa only [N_geoTransformAlong] using (MemberInterTowerAlong.strictAlong_mono T hsub)
  have hyBase : T.proj y ∈ P.N := by
    apply MemberInterTowerAlong.strictAlong_subset_preimage T hP.isClosedSubmanifold_N.1
    simpa only [N_geoTransformAlong] using hy
  obtain ⟨m, hmR, hmP⟩ := hdim (T.proj y) hyBase
  have hmR' := regularAtDim_geoTransformAlong_carrier R hR T hTR (hsubStage hy) hmR
  have hmP' := regularAtDim_geoTransformAlong_carrier P hP T hTP hy hmP
  refine ⟨hRstage, hsubStage, ?_, m, hmR', hmP'⟩
  exact MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T

/-- When the prefixed contact record is locally equivalent to its actual
ambient record, a test tower of the former is automatically a common test
tower. Its ambient hypersurface data therefore persist without additional
stagewise certificates. -/
theorem ambient_hypersurface_along_prefixed_test
    {n : ℕ} {X Y : CMfd.{0} n} (P R : MarkedIdeal n X)
    (hP : P.IsWellFormed) (hR : R.IsWellFormed) (hsub : P.N ⊆ R.N)
    (F : List (Set X))
    (hrel : HironakaG8LocalHistory.LocWPEquiv { P with E := F ++ P.E } R)
    (hdim : ∀ x ∈ P.N, ∃ m, RegularAtDim (n := n) R.N x (m+1) ∧
      RegularAtDim (n := n) P.N x m)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower { P with E := F ++ P.E } T)
    {y : Y} (hy : y ∈ (geoTransformAlong P T).N) :
    (geoTransformAlong R T).IsWellFormed ∧
      (geoTransformAlong P T).N ⊆ (geoTransformAlong R T).N ∧
      (geoTransformAlong R T).E =
        (geoTransformAlong { P with E := F ++ P.E } T).E ∧
      ∃ m, RegularAtDim (n := n) (geoTransformAlong R T).N y (m+1) ∧
        RegularAtDim (n := n) (geoTransformAlong P T).N y m := by
  have hTP : IsGeoTestTower P T := HironakaG8ClassStepHistory.isGeoTestTower_of_addE P F T hT
  have hTR : IsGeoTestTower R T := (hrel.wEquiv.2 T).1.mp hT
  exact ambient_hypersurface_along_common_test P R hP hR hsub F hrel.E_eq hdim T hTP hTR hy

end
end Hironaka.HironakaG8CaseTAmbientStage
