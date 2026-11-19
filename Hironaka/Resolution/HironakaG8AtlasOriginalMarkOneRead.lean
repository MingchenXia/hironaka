import Hironaka.Resolution.HironakaG8CompleteEmbeddedAtlas
import Hironaka.Resolution.HironakaSharpActualCurveBirthBoundaryOverlaps
import Hironaka.Resolution.HironakaCurrentStrictTransformIdeal

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8AtlasOriginalMarkOneRead

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IsolatedCompactSingularAtlas
  HironakaG8CompleteEmbeddedAtlas HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3GenericBornChartOverlap HironakaG3EmptyAwareBornSlots HironakaG3EmptyAwareFullBoundary
  AnalyticSubsetOpens

abbrev originalRecord {n : ℕ} {X : CMfd.{0} n} (W : Set X) : MarkedIdeal n X :=
  ⟨univ, [], vanishingIdeal (n := n) W, 1⟩

/-- The actual mixed embedded history is a TEST of the original reduced mark-one record. -/
theorem original_markOne_test_of_positions {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), EmbeddedPositions W T →
      IsGeoTestTower (originalRecord W) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hPos => by
    have hTest := original_markOne_test_of_positions W hW T hPos.1
    have hWF : (originalRecord W).IsWellFormed :=
      ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
        isSNCDivisor_nil, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
    let O : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
    have hAvoid := centresAvoid_of_centresOver O (F := singularSet (n := n) W)
      disjoint_compl_left T (embedded_positions_centres_over hW.isClosed T hPos.1).1
    have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
      change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
      simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
    have hCos := HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid_wellFormed
      hW.isClosed hWF O hDense T hTest hAvoid
    refine ⟨hTest, hπ.1, ?_, hPos.2.2⟩
    intro x hx
    rcases hPos.2.1 with hSing | hBoundary
    · exact hCos (hSing hx).1
    · exact hCos (hBoundary.2 hx).1

/-- Each actual finite chart tests the restriction of the original mark-one record.
Its strict carrier and the whole raw boundary list pull back from the atlas chart,
including slots whose trace is empty. -/
theorem chart_original_markOne_read {n : ℕ} {X Z : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {K : LocalTowerClass X} {P : Z → X}
    (A : CompleteEmbeddedAtlas W K P) (c : TowerChart K Z P) :
    let M := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X)
      (originalRecord W)
    IsGeoTestTower M c.T ∧
      (chartIncl c) ⁻¹' strictTransform n P W =
        strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) ∧
      (chartBoundary c (originalRecord W)).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
        (geoTransformAlong M c.T).E.map (c.φ.symm ⁻¹' ·) := by
  dsimp only
  have hM :
      MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) (originalRecord W) =
        originalRecord (X := CMfd.of (n := n) c.U) ((Subtype.val : c.U → X) ⁻¹' W) :=
    by simpa only [originalRecord, List.map_nil] using
      HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal c.U [] W
  refine ⟨?_, (strictTransform_chart c A.glued.1 W).symm, ?_⟩
  · rw [hM]
    exact original_markOne_test_of_positions _ (isComplexAnalyticSubset_preimage_val hW c.U)
      c.T (A.actualHistory c).positions
  · exact chartBoundary_map_val c (originalRecord W)

open HironakaSharpActualCurveBirthBoundaryOverlaps

/-- The raw slot at any index is read through the same actual terminal chart. -/
theorem chart_original_markOne_raw_slot {n : ℕ} {X Z : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {K : LocalTowerClass X} {P : Z → X}
    (A : CompleteEmbeddedAtlas W K P) (c : TowerChart K Z P) (k : ℕ) :
    let M := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X)
      (originalRecord W)
    (Subtype.val : c.V → Z) ⁻¹' boundaryReadout (chartBoundary c (originalRecord W)) k =
      c.φ.symm ⁻¹' boundaryReadout (geoTransformAlong M c.T).E k := by
  dsimp only
  rw [← boundaryReadout_map_preimage, (chart_original_markOne_read hW A c).2.2,
    boundaryReadout_map_preimage]

end
end Hironaka.HironakaG8AtlasOriginalMarkOneRead
