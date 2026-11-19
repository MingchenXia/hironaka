import Hironaka.Resolution.HironakaActualMixedTestPowerNormalization

/-! A given native tower on the projected ambient is an existing mixed history
rooted at the original marked record. Whole records, testhood and clocks agree.
Blueprint FIRST: hironaka-actual-projection-tower-history.tex. -/
set_option autoImplicit false

universe u
namespace Hironaka.HironakaActualProjectionTowerHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualProjectionTestRecord
open HironakaActualMixedTestPowerNormalization (History)

/-- One genuine original projection, followed by the SAME given native tower. -/
def projectionTowerHistory {n : ℕ} {X : CMfd.{u} n} (M : MarkedIdeal n X) :
    {Y : CMfd.{u} (n+1)} → (T : BlowupTower (projectionAmbient X) Y) →
      History X M.E Y ((projectionTest M).geoTransformAlong T).E
  | _, .refl => .projection .refl
  | _, .step T C π hπ => .controlled (projectionTowerHistory M T) C π hπ

/-- Equality of the entire native record, including its proper carrier and ideal. -/
theorem record_projectionTowerHistory {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) {Y : CMfd.{u} (n+1)}
    (T : BlowupTower (projectionAmbient X) Y) :
    HironakaActualMixedTestPowerNormalization.record M (projectionTowerHistory M T) =
      (projectionTest M).geoTransformAlong T := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    change (HironakaActualMixedTestPowerNormalization.record M
      (projectionTowerHistory M T)).geoTransform C π =
        ((projectionTest M).geoTransformAlong T).geoTransform C π
    rw [ih]

/-- The native projected test and the original mixed test have identical conditions. -/
theorem isTest_projectionTowerHistory_iff {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) {Y : CMfd.{u} (n+1)}
    (T : BlowupTower (projectionAmbient X) Y) :
    HironakaActualMixedTestPowerNormalization.IsTest M (projectionTowerHistory M T) ↔
      IsGeoTestTower (projectionTest M) T := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    change (HironakaActualMixedTestPowerNormalization.IsTest M
      (projectionTowerHistory M T) ∧
      (HironakaActualMixedTestPowerNormalization.record M
        (projectionTowerHistory M T)).IsAdmissibleCentre C) ↔
        (IsGeoTestTower (projectionTest M) T ∧
          ((projectionTest M).geoTransformAlong T).IsAdmissibleCentre C)
    rw [record_projectionTowerHistory, ih]

/-- Actual original composite, one projection, all actions and all boundary slots. -/
theorem projectionTowerHistory_dictionary {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) {Y : CMfd.{u} (n+1)}
    (T : BlowupTower (projectionAmbient X) Y) :
    HironakaActualMixedTestPowerNormalization.length (projectionTowerHistory M T) = T.length+1 ∧
    HironakaActualMixedTestPowerNormalization.projections (projectionTowerHistory M T) = 1 ∧
    HironakaActualMixedTestPowerNormalization.baseMap (projectionTowerHistory M T) =
      (Prod.fst : projectionAmbient X → X) ∘ T.proj ∧
    ((projectionTest M).geoTransformAlong T).E.length = M.E.length+1+T.length := by
  have hLength : HironakaActualMixedTestPowerNormalization.length
      (projectionTowerHistory M T) = T.length+1 := by
    induction T with
    | refl => rfl
    | step T C π hπ ih =>
      change HironakaActualMixedTestPowerNormalization.length
        (projectionTowerHistory M T)+1 = (T.length+1)+1
      rw [ih]
  have hProjections : HironakaActualMixedTestPowerNormalization.projections
      (projectionTowerHistory M T) = 1 := by
    clear hLength
    induction T with
    | refl => rfl
    | step T C π hπ ih => exact ih
  have hMap : HironakaActualMixedTestPowerNormalization.baseMap
      (projectionTowerHistory M T) = (Prod.fst : projectionAmbient X → X) ∘ T.proj := by
    clear hLength hProjections
    induction T with
    | refl => rfl
    | step T C π hπ ih =>
      change HironakaActualMixedTestPowerNormalization.baseMap
        (projectionTowerHistory M T) ∘ π =
          (Prod.fst : projectionAmbient X → X) ∘ (T.proj ∘ π)
      rw [ih]
      rfl
  refine ⟨hLength,hProjections,hMap,?_⟩
  have hBoundary :=
    (HironakaActualMixedTestPowerNormalization.history_clocks M
      (projectionTowerHistory M T)).2
  rw [record_projectionTowerHistory,hLength] at hBoundary
  omega

end
end Hironaka.HironakaActualProjectionTowerHistory
