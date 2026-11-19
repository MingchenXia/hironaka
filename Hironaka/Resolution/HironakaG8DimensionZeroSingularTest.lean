import Hironaka.Resolution.HironakaG8FiniteSingularHSPotential
import Hironaka.Resolution.HironakaActualHSSingularOriginalPrefix
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual
import Hironaka.Resolution.HironakaGeneralSingularCentreCodimension
import Hironaka.Resolution.HironakaResolutionSpaceSingular
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8DimensionZeroSingularTest
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves AnalyticDimensionBasics
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaActualHSSingularOriginalPrefix HironakaOneDimensionalCanonicalSuperlevels
  HironakaSharpActualAccumulatedTraceResidual HironakaHolomorphicJetChartInvariance
  HironakaG8IntrinsicSingularBlockSchedule HironakaResolutionSpaceSingular NormalCrossings

/-- Any actual singular-centred history whose literal centres are zero-dimensional
is a test of the same original mark-one ideal with the actual SNC boundary. -/
theorem zero_dimensional_singular_centres_is_original_test {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun _ C => DimLE (n := n) C 0) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hStage, hPoint => by
    have hTest := zero_dimensional_singular_centres_is_original_test W hW E hE T hStage.1 hPoint.1
    let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
    have hWF : M.IsWellFormed :=
      ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW, hE,
        SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
    let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
    have hGeo := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T hStage.1)
    have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
      change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
      simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
    have hCos := HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid_wellFormed
      hW.isClosed hWF O hDense T hTest hGeo.1
    have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      hWF T hTest).isSNCDivisor
    have hCd := hPoint.2
    have hCa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
    have hreg : ∀ x ∈ C, RegularAtDim (n := n) C x 0 := by
      intro x hx
      exact regularAtDim_zero_of_analytic_dimLE_zero hCa hCd hx
    have hNC := actual_discrete_centre_hasNormalCrossings hreg hSNC
    exact ⟨hTest,hπ.1,fun x hx => hCos ((singularSet_subset _) (hStage.2 hx)),hNC⟩

/-- If every singular-centred prefix has zero-dimensional intrinsic singular locus,
then every such tower tests the original marked ideal with the actual SNC boundary. -/
theorem dimension_zero_singular_history_is_original_test {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hDim : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      DimLE (n := n) (singularSet (n := n) (strictTransform n T.proj W)) 0)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T := by
  intro Y T hStage
  have hPoint : ∀ {Z : CMfd.{0} n} (S : BlowupTower X Z),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) S →
      StageCentres (fun _ C => DimLE (n := n) C 0) S := by
    intro Z S
    induction S with
    | refl => intro _; trivial
    | @step A B S C π hπ ih =>
      intro hS
      refine ⟨ih hS.1,?_⟩
      have hV := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform S.isBlowupSequence hW
      have hSa := isComplexAnalyticSubset_singularSet hV
      exact DimensionMonotone.DimLE.anti hSa hS.2 (hDim S hS.1)
  exact zero_dimensional_singular_centres_is_original_test W hW E hE T hStage (hPoint T hStage)

end
end Hironaka.HironakaG8DimensionZeroSingularTest
