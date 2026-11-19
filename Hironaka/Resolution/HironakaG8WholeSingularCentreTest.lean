import Hironaka.Resolution.HironakaG8DimensionZeroSingularTest
import Hironaka.Resolution.HironakaG8DisjointMarkedSwap

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8WholeSingularCentreTest

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaG8IntrinsicSingularBlockSchedule HironakaResolutionSpaceSingular HironakaResolutionSpace NormalCrossings

variable {n : ℕ} {X Y : CMfd.{0} n}

private abbrev original (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)

/-- Along a singular-only original TEST, a smooth closed part of the
current singular locus is admissible whenever it has normal crossings
with the actual accumulated boundary. -/
theorem whole_singular_subcentre_admissible
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (original W E) T)
    (hStage : StageCentres
      (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    {C : Set Y} (hC : IsClosedSubmanifold n C)
    (hSing : C ⊆ singularSet (n := n) (strictTransform n T.proj W))
    (hNC : HasNormalCrossings n C (geoTransformAlong (original W E) T).E) :
    (geoTransformAlong (original W E) T).IsAdmissibleCentre C := by
  have hWF : (original W E).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hAvoid := (actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)).1
  have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
    change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
    simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hCos := HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid_wellFormed
    hW.isClosed hWF O hDense T hTest hAvoid
  exact ⟨hC, hSing.trans ((singularSet_subset _).trans hCos), hNC⟩

/-- One actual whole blowup services a closed singular subcentre with
normal crossings with the current boundary, without compactness. -/
theorem exists_whole_singular_subcentre_test_step
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (original W E) T)
    (hStage : StageCentres
      (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    {C : Set Y} (hC : IsClosedSubmanifold n C)
    (hSing : C ⊆ singularSet (n := n) (strictTransform n T.proj W))
    (hNC : HasNormalCrossings n C (geoTransformAlong (original W E) T).E) :
    ∃ (Z : CMfd.{0} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (original W E) (.step T C π hπ) ∧
        StageCentres (fun P D => D ⊆ singularSet (n := n) (strictTransform n P.proj W))
          (.step T C π hπ) := by
  have hInterior : interior C = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact disjoint_left.mp (disjoint_interior_singularSet (strictTransform n T.proj W))
      (interior_mono (hSing.trans (singularSet_subset _)) hx) (hSing (interior_subset hx))
  obtain ⟨Z,tZ,cZ,mZ,π,hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hInterior
  let : TopologicalSpace Z := tZ
  let : ChartedSpace (ComplexModel n) Z := cZ
  let : IsComplexManifold n Z := mZ
  let Z₀ : CMfd.{0} n := ⟨Z⟩
  let π₀ : Z₀ → Y := π
  have hπ₀ : IsBlowupAlong n C π₀ := hπ
  have hAd := whole_singular_subcentre_admissible W hW E hE T hTest hStage hC hSing hNC
  exact ⟨Z₀,π₀,hπ₀,⟨hTest,hAd⟩,⟨hStage,hSing⟩⟩

end Hironaka.HironakaG8WholeSingularCentreTest
