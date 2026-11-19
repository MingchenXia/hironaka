import Hironaka.Resolution.HironakaG8SingularTestBoundaryTransfer
import Hironaka.Resolution.HironakaG8SubmersionSingularHistory
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SubmersionSurfaceResolution
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular NormalCrossings
  HironakaG8SurfaceSingularPhase HironakaG8SubmersionSingularHistory
  HironakaG8SingularTestBoundaryTransfer HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionNormalCrossings
  HironakaOriginalStoppedPrefixSmoothComparison

/-- A finite singular-centred original-test resolution pulls back to the
same kind of resolution along an arbitrary holomorphic submersion. -/
theorem submersion_finite_singular_resolution {n m : ℕ} {X D : CMfd.{0} n} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (T : BlowupTower X D)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hTest : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W)) :
    ∃ (D' : CMfd.{0} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) Q ∧
      IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y) Q ∧
      strictTransform m Q.proj (f ⁻¹' W) = g ⁻¹' strictTransform n T.proj W ∧
      IsClosedSubmanifold m (strictTransform m Q.proj (f ⁻¹' W)) := by
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  have hM : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  obtain ⟨D',Q,g,hActual,hg,hLength,hSquare,hQTest,hDict,hWF,hCos,hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM T hTest
  have hQStage := actual_pullback_singular_stages hf W hW hActual hStage
  have hWF' := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
  have hE' := isSNCDivisor_preimage_submersion hf E hE
  have hEeq : (markedPullback (m := m) f M).E = E.map (f ⁻¹' ·) := rfl
  have hOriginal := singular_auxiliary_test_is_original_test (f ⁻¹' W) hWF' _ hE'
    (markedPullback (m := m) f M) hEeq Q hQTest hQStage
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
    change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
    simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hp := actual_singular_history_original_regular_protection W hW T (intrinsic_stage_native_history W T hStage)
  have heq := HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
    hf hActual O hp.1 W hDense
  refine ⟨D',Q,g,hActual,hQStage,hOriginal,heq,?_⟩
  rw [heq]
  exact isClosedSubmanifold_preimage_submersion hg hSmooth
/-- Compact surface singularity sources produce actual finite resolutions
upstairs in arbitrary ambient dimension. -/
theorem submersion_surface_finite_singular_resolution {m : ℕ} {X : CMfd.{0} 2} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W) (hK : IsCompact (singularSet (n := 2) W))
    (E : List (Set X)) (hE : IsSNCDivisor 2 E) {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel 2) ∞ f) :
    ∃ (D : CMfd.{0} 2) (T : BlowupTower X D) (D' : CMfd.{0} m)
      (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) Q ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T ∧
      IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y) Q ∧
      strictTransform m Q.proj (f ⁻¹' W) = g ⁻¹' strictTransform 2 T.proj W ∧
      IsClosedSubmanifold m (strictTransform m Q.proj (f ⁻¹' W)) := by
  obtain ⟨D,T,hStage,hTest,hSmooth⟩ := surface_finite_original_test_resolution W hW hK E hE
  obtain ⟨D',Q,g,hActual,hQStage,hOriginal,heq,hQSmooth⟩ :=
    submersion_finite_singular_resolution W hW E hE hf T hStage hTest hSmooth
  exact ⟨D,T,D',Q,g,hActual,hStage,hQStage,hTest,hOriginal,heq,hQSmooth⟩

end
end Hironaka.HironakaG8SubmersionSurfaceResolution
