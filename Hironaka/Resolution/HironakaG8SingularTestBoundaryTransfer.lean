import Hironaka.Resolution.HironakaG8SurfaceFiniteService
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SingularTestBoundaryTransfer
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular NormalCrossings

/-- A test tower for an auxiliary record with the same initial boundary is
also a test of the original mark-one ideal when its literal centres are
intrinsically singular for the actual strict transforms. -/
theorem singular_auxiliary_test_is_original_test {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (P : MarkedIdeal n X) (hPE : P.E = E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      StageCentres (fun R C => C ⊆ singularSet (n := n) (strictTransform n R.proj W)) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hP, hStage => by
    let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
    have hTest := singular_auxiliary_test_is_original_test W hW E hE P hPE T hP.1 hStage.1
    have hWF : M.IsWellFormed :=
      ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW, hE,
        SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
    let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T hStage.1)
    have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
      change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
      simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
    have hCos := HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid_wellFormed
      hW.isClosed hWF O hDense T hTest hp.1
    have hBound := HironakaHypersurfaceMultiplicityDescent.boundary_geoTransformAlong_eq_of_boundary_eq P M hPE T
    have hNC : HasNormalCrossings n C (geoTransformAlong M T).E := by
      rw [← hBound]
      exact hP.2.2.2
    exact ⟨hTest,hπ.1,fun x hx => hCos ((singularSet_subset _) (hStage.2 hx)),hNC⟩
end
end Hironaka.HironakaG8SingularTestBoundaryTransfer
