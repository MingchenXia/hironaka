import Hironaka.Resolution.HironakaG8CuspPointTowerEndpoint
import Hironaka.Resolution.HironakaG8FiniteCuspSheetSchedule
import Hironaka.Resolution.HironakaG8CuspSheetFootprintTraces
import Hironaka.Resolution.HironakaG8SheetNestedComparisons
import Hironaka.Resolution.HironakaG8PrescribedTowerChartChain
import Hironaka.Resolution.HironakaG8CofinalSheetScheduleLabels

/-! An actual original TEST atlas whose fixed spatial chronology has unbounded height. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspSheetsNoWeakRank

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3RTowerGluing G3UniversePhysicalClassComparisons
  HironakaG3EmptyAwareHistory HironakaG8OccupiedSlotComparison
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8ConsecutiveNestedReorderings HironakaG8SpatialCofinalPrecedence
  HironakaG8CuspPointTowerEndpoint HironakaG8CountableCuspSheets HironakaG8FiniteCuspSheetSchedule
  HironakaG8SheetNestedComparisons HironakaG8PrescribedTowerChartChain
  HironakaG8CuspSheetFootprintTraces HironakaG8CofinalSheetScheduleLabels
  HironakaStageCenters HironakaEmbeddedAnalytic MarkedIdeals.MarkedIdeal NormalCrossings MaxLocusLocal

/-- The identical degree-seven cusps on the countable sheet union carry
an actual compact-cofinal atlas of finished original TESTs whose fixed
physical event system has no weak natural spatial rank. -/
theorem exists_cusp_sheets_original_test_atlas_without_weak_rank :
    ∃ (K : LocalTowerClass sheetManifold) (Z : CMfd.{0} 3) (P : Z → sheetManifold),
      IsGluedFrom K Z P ∧
      ∃ (cmp : HasPhysicalComparisons K) (c : ℕ → TowerChart K Z P)
          (hMono : Monotone fun i => (c i).U),
        (∀ i, (c i).U = prefixOpen i) ∧
        (∀ F : Set sheetManifold, IsCompact F → ∃ i, F ⊆ ((c i).U : Set sheetManifold)) ∧
        (∀ i, let W := (Subtype.val : (c i).U → sheetManifold) ⁻¹' sheetCusps (fun _ => 7)
          IsGeoTestTower (cuspMarked W) (c i).T ∧
          StageCentres (fun Q C => C ⊆ singularSet (n := 3) (strictTransform 3 Q.proj W)) (c i).T ∧
          IsClosedSubmanifold 3 (strictTransform 3 (c i).T.proj W)) ∧
        ∃ E : CofinalEvents c (Option ℕ),
          (∀ a, ∃ i p, E.event i p = a) ∧
          (∀ {i j} (hij : i ≤ j) p, E.lift hij p =
            chartOccupiedLift cmp (c i) (c j) (hMono hij) p) ∧
          ¬ ∃ rank : Option ℕ → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  obtain ⟨Y,T,hLen,hSmooth,hTest,hStage,hFoot,_⟩ := exists_three_cusp_point_blowups_smooth
  have hChoose (m : ℕ) := finite_cusp_sheet_schedule T hLen hTest hStage hSmooth hFoot m
  choose B R _hLenR hTestR hStageR hSmoothR hPatch using hChoose
  have hTrace (m : ℕ) : ScheduledSingletonTraces m (R m) := fun i => (hPatch m i).2
  have hWF (i : ℕ) : (cuspMarked (cuspPrefix i)).IsWellFormed := by
    have hAnalytic := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      (sheetCusps_isAnalytic (fun _ => 7)) (prefixOpen i)
    exact ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      CartanIrreducible.cartanCoherence _ hAnalytic, isSNCDivisor_nil,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  have hNested (i j : ℕ) (hij : i ≤ j) :
      NestedGeometry (n := 3) (X := sheetManifold) (U := prefixOpen i) (V := prefixOpen j)
        (A := B i) (B := B j) (R i) (R j) := by
    let e := (nestedOpensDiffeo (n := 3) (prefixOpen_mono hij)).symm
    have hFp := scheduled_occupiedFootprints_cross_cutoff hij (hTrace i) (hTrace j)
      e (fun _ => rfl)
    refine nested_geometry_of_disjoint_sheet_comparisons (n := 3) (X := sheetManifold)
      (U := prefixOpen i) (V := prefixOpen j) (A := B i) (B := B j) (prefixOpen_mono hij)
      (fun s : Fin (i+1) => sheetOpen s.val)
      (fun s => sheetOpen_le_prefix (Nat.le_of_lt_succ s.isLt))
      (patch_cover i) ?_ (R i) (R j) (cuspMarked (cuspPrefix i)) (hWF i) hFp ?_
    · intro s t hne
      exact Set.disjoint_left.mpr (fun x hx hy => hne (Fin.ext
        ((mem_singleton_iff.mp hx.1).symm.trans (mem_singleton_iff.mp hy.1))))
    · intro s
      let t : Fin (j+1) := ⟨s.val,(Nat.lt_succ_of_le ((Nat.le_of_lt_succ s.isLt).trans hij))⟩
      obtain ⟨a,ha,_⟩ := (hPatch i s).1
      obtain ⟨b,hb,_⟩ := (hPatch j t).1
      let g := (patchCoord s).trans (patchCoord t).symm
      have hBase (x : patch s) : (g x).val.val = x.val.val := by
        change (s.val,x.val.val.2) = x.val.val
        exact Prod.ext (mem_singleton_iff.mp x.property.1).symm rfl
      exact ⟨g,hBase,a.symm.trans b,
        G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm ha) hb⟩
  let hPair := pairPhysical_of_nested (n := 3) (X := sheetManifold) prefixOpen B R prefixOpen_mono hNested
  let A := prescribedAtlas (n := 3) (X := sheetManifold) prefixOpen B R prefixOpen_point_cover hPair
  let c := prescribedChart (n := 3) (X := sheetManifold) prefixOpen B R prefixOpen_point_cover hPair
  let cmp := prescribed_hasPhysicalComparisons (n := 3) (X := sheetManifold) prefixOpen B R hPair
  have hMono : Monotone fun i => (c i).U := prefixOpen_mono
  have hFull : HasFullSheetClock c := fun i => scheduled_occupied_iff (hTrace i)
  have hVisible (i j : ℕ) (hij : i ≤ j) (k : ℕ) :
      Occupied (restrict (nestedOpens (c j).U ((c i).U ⊓ (c j).U)) (c j).T) k ↔
        k < i+2 ∨ k = j+2 := by
    change Occupied (restrict (nestedOpens (prefixOpen j) (prefixOpen i ⊓ prefixOpen j)) (R j)) k ↔ _
    rw [inf_eq_left.mpr (prefixOpen_mono hij)]
    exact scheduled_occupied_restrict_cross_cutoff hij (hTrace j) k
  refine ⟨_,A.manifold,A.proj,⟨A.contMDiff_proj,A.isProperMap_proj,A.surjective_proj,?_⟩,
    cmp,c,hMono,fun _ => rfl,prefixOpen_compact_cofinal,fun i => ⟨hTestR i,hStageR i,hSmoothR i⟩,
    sheetScheduleEvents c hFull,sheetScheduleEvents_occurs c hFull,
    fun hij p => sheetScheduleEvents_lift_eq_chartOccupiedLift c hFull cmp hMono hVisible hij p,?_⟩
  · intro x
    obtain ⟨i,hi⟩ := prefixOpen_point_cover x
    exact ⟨c i,hi⟩
  · exact no_weak_rank_of_scheduled_shared_sheet_hits c hFull
      (fun j _ => scheduled_shared_last_sheet_hits (hTrace j))

end Hironaka.HironakaG8CuspSheetsNoWeakRank
