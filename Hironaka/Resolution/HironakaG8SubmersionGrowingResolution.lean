import Hironaka.Resolution.HironakaG8LocallyFiniteCountBridge
import Hironaka.Resolution.HironakaG8SubmersionSurfaceResolution
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
set_option autoImplicit false
open Set Filter Classical TopologicalSpace Function
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SubmersionGrowingResolution
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular NormalCrossings
  HironakaG8SurfaceSingularPhase HironakaG8SurfaceGlobalScheduler HironakaG8SurfaceLimitEndpoint
  HironakaG8SubmersionSingularHistory HironakaG8SingularTestBoundaryTransfer
  HironakaG8SubmersionSurfaceResolution HironakaG8LocallyFiniteCountBridge
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOriginalLocallyFiniteHistory HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionNormalCrossings
  HironakaOriginalStoppedPrefixSmoothComparison HironakaOriginalCanonicalDimensionList
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryFactors
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaLocallyFiniteResolutionSequence
  HironakaActualLimitProtectedOpen HironakaG4CompactComponentLimit HironakaAdmissibleSequence
open ResolutionInvariantSeq (GrowingSeq)
attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- Every source prefix tests its own original mark-one input and has literal
singular centres, on the same actual stagewise Cartesian pullback history. -/
theorem actualSourceGrowing_singular_original_tests {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) {f : Y → X}
    (β : SmoothBlowupChoices.{0} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (s : GrowingSeq X)
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2)
    (hTest : ∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) (s.stage i).2) :
    let q := actualSourceGrowing β hf s
    (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) (q.stage i).2) ∧
    ∀ i, IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y) (q.stage i).2 := by
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  have hM : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hWf := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
  have hEf := isSNCDivisor_preimage_submersion hf E hE
  have hEeq : (markedPullback (m := m) f M).E = E.map (f ⁻¹' ·) := rfl
  constructor
  · intro i
    exact actual_pullback_singular_stages hf W hW
      (chosenActualTower β hf (s.stage i).2).2.2.property (hStage i)
  · intro i
    have h := (chosenActualTower β hf (s.stage i).2).2.2.property
    have hQStage := actual_pullback_singular_stages hf W hW h (hStage i)
    have hQTest := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      h M hM (hTest i)).1
    exact singular_auxiliary_test_is_original_test (f ⁻¹' W) hWf _ hEf
      (markedPullback (m := m) f M) hEeq _ hQTest hQStage

/-- Every base window regular at one actual stage gives a corresponding
source window regular at the same actual Cartesian stage. -/
theorem actualSourceGrowing_regular_windows {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) {f : Y → X}
    (β : SmoothBlowupChoices.{0} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (s : GrowingSeq X)
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2)
    (hReg : ∀ x : X, ∃ (U : Opens X) (N : ℕ), x ∈ U ∧
      Disjoint (singularSet (n := n) (strictTransform n (s.stage N).2.proj W))
        ((s.stage N).2.proj ⁻¹' (U : Set X))) :
    ∀ y : Y, ∃ (V : Opens Y) (N : ℕ), y ∈ V ∧
      Disjoint (singularSet (n := m) (strictTransform m ((actualSourceGrowing β hf s).stage N).2.proj (f ⁻¹' W)))
        (((actualSourceGrowing β hf s).stage N).2.proj ⁻¹' (V : Set Y)) := by
  intro y
  obtain ⟨U,N,hyU,hBase⟩ := hReg (f y)
  let V : Opens Y := ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.contMDiff.continuous⟩
  refine ⟨V,N,hyU,?_⟩
  let T := (s.stage N).2
  let h := (chosenActualTower β hf T).2.2.property
  let g := (chosenActualTower β hf T).2.2.val
  let Q := (chosenActualTower β hf T).2.1
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
    change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
    simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hp := actual_singular_history_original_regular_protection W hW T (intrinsic_stage_native_history W T (hStage N))
  have heq := HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
    hf h O hp.1 W hDense
  have hSing : singularSet (n := m) (strictTransform m Q.proj (f ⁻¹' W)) =
      g ⁻¹' singularSet (n := n) (strictTransform n T.proj W) := by
    rw [heq,singularSet_preimage_eq h.isSubmersion]
  apply disjoint_left.mpr
  intro z hz hV
  have hz' : g z ∈ singularSet (n := n) (strictTransform n T.proj W) := by
    change z ∈ singularSet (n := m) (strictTransform m Q.proj (f ⁻¹' W)) at hz
    rw [hSing] at hz
    exact hz
  have hU' : T.proj (g z) ∈ U := by
    have hc := h.proj_comm z
    change f (Q.proj z) ∈ U at hV
    rw [hc]
    exact hV
  exact disjoint_left.mp hBase hz' hU'
/-- A regular locally finite singular-test history pulls back to a genuine
locally finite singular-test history and a smooth proper source limit. -/
theorem submersion_growing_singular_resolution {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) {f : Y → X}
    (β : SmoothBlowupChoices.{0} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2)
    (hTest : ∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) (s.stage i).2)
    (hReg : ∀ x : X, ∃ (U : Opens X) (N : ℕ), x ∈ U ∧
      Disjoint (singularSet (n := n) (strictTransform n (s.stage N).2.proj W))
        ((s.stage N).2.proj ⁻¹' (U : Set X))) :
    ∃ (hLFq : LocallyFinite (centreImage (actualSourceGrowing β hf s))),
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W)))
        ((actualSourceGrowing β hf s).stage i).2) ∧
      (∀ i, IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y)
        ((actualSourceGrowing β hf s).stage i).2) ∧
      IsClosedSubmanifold m (strictTransform m (gluedProjection (actualSourceGrowing β hf s) hLFq) (f ⁻¹' W)) ∧
      IsProperMap (gluedProjection (actualSourceGrowing β hf s) hLFq) ∧
      Surjective (gluedProjection (actualSourceGrowing β hf s) hLFq) ∧
      IsIsomorphismOver m (gluedProjection (actualSourceGrowing β hf s) hLFq)
        (singularSet (n := m) (f ⁻¹' W))ᶜ ∧
      exceptionalLocus m (gluedProjection (actualSourceGrowing β hf s) hLFq) =
        (gluedProjection (actualSourceGrowing β hf s) hLFq) ⁻¹' singularSet (n := m) (f ⁻¹' W) ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞
        (gluedProjection (actualSourceGrowing β hf s) hLFq) := by
  let q := actualSourceGrowing β hf s
  have hLFq := actualSourceGrowing_locallyFinite β hf s hLF
  have hWf := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
  obtain ⟨hQStage,hQTest⟩ := actualSourceGrowing_singular_original_tests W hW E hE β hf s hStage hTest
  have hQReg := actualSourceGrowing_regular_windows W hW β hf s hStage hReg
  have hSmooth := intrinsic_limit_strictTransform_smooth (f ⁻¹' W) hWf q hLFq hQStage hQReg
  have hIso := intrinsic_limit_regular_open_iso (f ⁻¹' W) hWf q hLFq hQStage
  have hEq := intrinsic_limit_strictTransform_eq_projection (f ⁻¹' W) hWf q hLFq hQStage hIso
  have hProper := gluedProjection_isProperMap q hLFq
  have hHolo := gluedProjection_contMDiff q hLFq
  have hSmooth' : IsClosedSubmanifold m (strictTransform m (gluedProjection q hLFq) (f ⁻¹' W)) := hEq ▸ hSmooth
  let Z : CMfd.{0} m := CMfd.of (n := m) (limitManifold q hLFq)
  have hExc : exceptionalLocus m (gluedProjection q hLFq) =
      (gluedProjection q hLFq) ⁻¹' singularSet (n := m) (f ⁻¹' W) :=
    exceptionalLocus_eq_singular_preimage (X := Y) (Y := Z) (f ⁻¹' W) hWf.isClosed (gluedProjection q hLFq) hHolo hIso hSmooth'
  exact ⟨hLFq,hQStage,hQTest,hSmooth',hProper,proper_regular_open_iso_surjective (X := Y) (Y := Z) (f ⁻¹' W) _ hProper hIso,
    hIso,hExc,hHolo⟩

/-- Any global smooth pullback of an analytic surface set admits an actual
singular-centred original-test resolution, even when the singular locus is noncompact. -/
theorem submersion_surface_singular_resolution {m : ℕ} {X : CMfd.{0} 2} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : IsSNCDivisor 2 E) {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel 2) ∞ f) :
    (∃ (D : CMfd.{0} 2) (T : BlowupTower X D) (D' : CMfd.{0} m)
      (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) Q ∧
      IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y) Q ∧
      strictTransform m Q.proj (f ⁻¹' W) = g ⁻¹' strictTransform 2 T.proj W ∧
      IsClosedSubmanifold m (strictTransform m Q.proj (f ⁻¹' W)) ∧
      IsProperMap Q.proj ∧ Surjective Q.proj ∧
      IsIsomorphismOver m Q.proj (singularSet (n := m) (f ⁻¹' W))ᶜ ∧
      exceptionalLocus m Q.proj = Q.proj ⁻¹' singularSet (n := m) (f ⁻¹' W) ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj) ∨
    ∃ (s : GrowingSeq X) (_hLF : LocallyFinite (centreImage s))
      (hLFq : LocallyFinite (centreImage (actualSourceGrowing (defaultSmoothBlowupChoices (m := m)) hf s))),
      let q := actualSourceGrowing (defaultSmoothBlowupChoices (m := m)) hf s
      (∀ i, ∃ g, IsActualTowerPullback f (q.stage i).2 (s.stage i).2 g ∧
        strictTransform m (q.stage i).2.proj (f ⁻¹' W) =
          g ⁻¹' strictTransform 2 (s.stage i).2.proj W) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) (q.stage i).2) ∧
      (∀ i, IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y) (q.stage i).2) ∧
      IsClosedSubmanifold m (strictTransform m (gluedProjection q hLFq) (f ⁻¹' W)) ∧
      IsProperMap (gluedProjection q hLFq) ∧ Surjective (gluedProjection q hLFq) ∧
      IsIsomorphismOver m (gluedProjection q hLFq) (singularSet (n := m) (f ⁻¹' W))ᶜ ∧
      exceptionalLocus m (gluedProjection q hLFq) = (gluedProjection q hLFq) ⁻¹' singularSet (n := m) (f ⁻¹' W) ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ (gluedProjection q hLFq) := by
  obtain ⟨K,hK,U,hU,hCover,hResult⟩ := surface_exists_intrinsic_singular_service_schedule W hW E hE
  rcases hResult with hFinite | hInfinite
  · obtain ⟨a,hStable,hTest,hStage,hEmpty⟩ := hFinite
    let T := (HironakaExhaustionBlockLocalFiniteness.blockEndpoints (surfaceNext W hW K hK) a).2
    have hp := actual_singular_history_original_regular_protection W hW T (intrinsic_stage_native_history W T hStage)
    have hSmooth := hp.2.2.2.2.2.2.mp hEmpty
    obtain ⟨D',Q,g,hActual,hQStage,hQTest,heq,hQSmooth⟩ :=
      submersion_finite_singular_resolution W hW E hE hf T hStage hTest hSmooth
    have hWf := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
    have hpQ := actual_singular_history_original_regular_protection (f ⁻¹' W) hWf Q
      (intrinsic_stage_native_history (f ⁻¹' W) Q hQStage)
    have hQIso := hpQ.2.1
    have hQProper := HironakaLocalPrincipalization.isProperMap_proj Q
    have hQSurj := proper_regular_open_iso_surjective (f ⁻¹' W) Q.proj hQProper hQIso
    have hQExc := exceptionalLocus_eq_singular_preimage (f ⁻¹' W) hWf.isClosed Q.proj Q.contMDiff_proj hQIso hQSmooth
    exact Or.inl ⟨_,T,D',Q,g,hActual,hQStage,hQTest,heq,hQSmooth,hQProper,hQSurj,hQIso,hQExc,Q.contMDiff_proj⟩
  · obtain ⟨s,hBoundary,hTest,hStage,hLF,hEmpty⟩ := hInfinite
    have hWindow := surface_scheduled_sequence_regular W hW K hK U hU s hBoundary
    have hReg : ∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧
        Disjoint (singularSet (n := 2) (strictTransform 2 (s.stage N).2.proj W))
          ((s.stage N).2.proj ⁻¹' (V : Set X)) := by
      intro x
      obtain ⟨a,ha⟩ := hCover x
      obtain ⟨N,hN⟩ := hWindow a
      exact ⟨U a,N,ha,hN⟩
    let β : SmoothBlowupChoices.{0} m := defaultSmoothBlowupChoices
    obtain ⟨hLFq,hQStage,hQTest,hSmooth,hProper,hSurj,hIso,hExc,hHolo⟩ :=
      submersion_growing_singular_resolution W hW E hE β hf s hLF hStage hTest hReg
    refine Or.inr ⟨s,hLF,hLFq,?_,hQStage,hQTest,hSmooth,hProper,hSurj,hIso,hExc,hHolo⟩
    intro i
    let T := (s.stage i).2
    let h := (chosenActualTower β hf T).2.2.property
    let O : Opens X := ⟨(singularSet (n := 2) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
    have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
      change W ⊆ closure (W ∩ (singularSet (n := 2) W)ᶜ)
      simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T (hStage i))
    exact ⟨(chosenActualTower β hf T).2.2.val,h,
      HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
        hf h O hp.1 W hDense⟩

/-- A globally smooth pullback of any analytic surface subset has a proper
surjective holomorphic singular resolution in arbitrary ambient dimension. -/
theorem submersion_surface_proper_singular_resolution {m : ℕ} {X : CMfd.{0} 2} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W) {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel 2) ∞ f) :
    ∃ (Z : CMfd.{0} m) (π : Z → Y), IsProperMap π ∧ Surjective π ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ π ∧
      IsIsomorphismOver m π (singularSet (n := m) (f ⁻¹' W))ᶜ ∧
      IsClosedSubmanifold m (strictTransform m π (f ⁻¹' W)) ∧
      exceptionalLocus m π = π ⁻¹' singularSet (n := m) (f ⁻¹' W) := by
  rcases submersion_surface_singular_resolution W hW [] isSNCDivisor_nil hf with hFinite|hInfinite
  · obtain ⟨D,T,Z,Q,g,hActual,hStage,hTest,heq,hSmooth,hProper,hSurj,hIso,hExc,hHolo⟩ := hFinite
    exact ⟨Z,Q.proj,hProper,hSurj,hHolo,hIso,hSmooth,hExc⟩
  · obtain ⟨s,hLF,hLFq,hPullback,hStage,hTest,hSmooth,hProper,hSurj,hIso,hExc,hHolo⟩ := hInfinite
    let q := actualSourceGrowing (defaultSmoothBlowupChoices (m := m)) hf s
    let Z : CMfd.{0} m := CMfd.of (n := m) (limitManifold q hLFq)
    exact ⟨Z,gluedProjection q hLFq,hProper,hSurj,hHolo,hIso,hSmooth,hExc⟩

end
end Hironaka.HironakaG8SubmersionGrowingResolution
