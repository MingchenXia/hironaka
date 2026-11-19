import Hironaka.Resolution.HironakaG8CompactConnectedSingular
import Hironaka.Resolution.HironakaG8SubmersionGrowingResolution
import Hironaka.Resolution.HironakaG8CartesianSingularPrefix

/-! Pull back the compact-connected singular-locus endpoint along a submersion. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8SubmersionCompactConnectedTest

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaResolutionSpaceLocal HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaG8IntrinsicSingularBlockSchedule HironakaG8SurfaceLimitEndpoint
  HironakaG8SubmersionSurfaceResolution HironakaG8SubmersionGrowingResolution
  HironakaG8CompactConnectedSingular HironakaG8CartesianSingularPrefix
  HironakaG8GlobalNativeTestAssembly NormalCrossings HomogenizedGlueingTower
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaLocallyFiniteResolutionSequence HironakaG4CompactComponentLimit
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOriginalLocallyFiniteHistory
open ResolutionInvariantSeq (GrowingSeq)

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- Smoothness of the recorded strict transform gives eventual regularity
on the actual stable base windows of an intrinsic singular history. -/
theorem intrinsic_regular_windows_of_smooth_limit {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s))
    (hStage : ∀ i, StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj W)) (s.stage i).2)
    (hSmooth : IsClosedSubmanifold n (limitStrictTransform s hLF W)) :
    ∀ x : X, ∃ (U : Opens X) (N : ℕ), x ∈ U ∧
      Disjoint (singularSet (n := n) (strictTransform n (s.stage N).2.proj W))
        ((s.stage N).2.proj ⁻¹' (U : Set X)) := by
  intro x
  let U := stableWindow s hLF x
  let N := stableIndex s hLF x
  refine ⟨U,N,point_mem_stableWindow s hLF x,Set.disjoint_left.mpr ?_⟩
  intro y hSing hy
  have hEq := intrinsic_strictAlong_eq W hW (s.stage N).2 (hStage N)
  let q : localEndpoint s hLF x := ⟨y,hy⟩
  have hMem : actualHistoryLocalInclusion s hLF x q ∈ limitStrictTransform s hLF W := by
    change q ∈ (actualHistoryLocalInclusion s hLF x) ⁻¹' limitStrictTransform s hLF W
    rw [localInclusion_preimage_limitStrictTransform s hLF hW.isClosed x]
    change y ∈ strictAlong (s.stage N).2 W
    rw [hEq]
    exact (mem_singularSet_iff.mp hSing).1
  obtain ⟨d,hd⟩ := hSmooth.2 _ hMem
  have hReg := (regularAtDim_limitStrictTransform_local_iff s hLF hW.isClosed x q d).mp hd
  change RegularAtDim (n := n) (strictAlong (s.stage N).2 W) y d at hReg
  rw [hEq] at hReg
  exact (mem_singularSet_iff.mp hSing).2 d hReg

/-- A holomorphic submersion pulls back the actual finite or growing
resolution from a base whose original singular components are compact.
The growing supports are the literal inverse images of the base supports. -/
theorem submersion_test_of_compact_connected_base_singular
    {n m : ℕ} {X : CMfd.{0} (n+1)} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hCompact : ∀ x ∈ singularSet (n := n+1) W,
      IsCompact (connectedComponentIn (singularSet (n := n+1) W) x))
    {f : Y → X} (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel (n+1)) ∞ f) :
    (∃ (D : CMfd.{0} (n+1)) (T : BlowupTower X D) (D' : CMfd.{0} m)
      (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) Q ∧
      IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y) Q ∧
      strictTransform m Q.proj (f ⁻¹' W) = g ⁻¹' strictTransform (n+1) T.proj W ∧
      IsClosedSubmanifold m (strictTransform m Q.proj (f ⁻¹' W)) ∧ IsProperMap Q.proj ∧
      Surjective Q.proj ∧ IsIsomorphismOver m Q.proj (singularSet (n := m) (f ⁻¹' W))ᶜ) ∨
    ∃ (s : GrowingSeq X)
      (hLFq : LocallyFinite (centreImage (actualSourceGrowing (defaultSmoothBlowupChoices (m := m)) hf s))),
      let q := actualSourceGrowing (defaultSmoothBlowupChoices (m := m)) hf s
      LocallyFinite (centreImage s) ∧
      (∀ i, ∃ g, IsActualTowerPullback f (q.stage i).2 (s.stage i).2 g) ∧
      (∀ i, centreImage q i = f ⁻¹' centreImage s i) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m)
        (strictTransform m P.proj (f ⁻¹' W))) (q.stage i).2) ∧
      (∀ i, IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ : MarkedIdeal m Y)
        (q.stage i).2) ∧
      IsClosedSubmanifold m (strictTransform m (gluedProjection q hLFq) (f ⁻¹' W)) ∧
      IsProperMap (gluedProjection q hLFq) ∧ Surjective (gluedProjection q hLFq) ∧
      IsIsomorphismOver m (gluedProjection q hLFq) (singularSet (n := m) (f ⁻¹' W))ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ (gluedProjection q hLFq) := by
  rcases compact_connected_original_singular_finite_or_proper_limit W hW E hE hDense hCompact with hFinite | hGrowing
  · obtain ⟨D,T,hT,hSmooth,_,_,_⟩ := hFinite
    obtain ⟨D',Q,g,hActual,hQStage,hQTest,hStrict,hQSmooth⟩ :=
      submersion_finite_singular_resolution W hW E hE hf T hT.singular hT.tested hSmooth
    have hWf := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
    have hp := actual_singular_history_original_regular_protection (f ⁻¹' W) hWf Q
      (intrinsic_stage_native_history (f ⁻¹' W) Q hQStage)
    exact Or.inl ⟨D,T,D',Q,g,hActual,hQStage,hQTest,hStrict,hQSmooth,hp.2.2.1,
      proper_regular_open_iso_surjective (f ⁻¹' W) Q.proj hp.2.2.1 hp.2.1,hp.2.1⟩
  · obtain ⟨s,hLF,hState,_,hSmooth,_,_,_,_,_⟩ := hGrowing
    have hStage := fun i => (hState i).singular
    have hReg := intrinsic_regular_windows_of_smooth_limit W hW s hLF hStage hSmooth
    let β : SmoothBlowupChoices.{0} m := defaultSmoothBlowupChoices
    obtain ⟨hLFq,hQstage,hQtest,hQSmooth,hProper,hSurj,hIso,_,hHolo⟩ :=
      submersion_growing_singular_resolution W hW E hE β hf s hLF hStage (fun i => (hState i).tested) hReg
    refine Or.inr ⟨s,hLFq,hLF,?_,actualSourceGrowing_centreImage_eq β hf s,
      hQstage,hQtest,hQSmooth,hProper,hSurj,hIso,hHolo⟩
    intro i
    exact ⟨(chosenActualTower β hf (s.stage i).2).2.2.val,
      (chosenActualTower β hf (s.stage i).2).2.2.property⟩

end Hironaka.HironakaG8SubmersionCompactConnectedTest
