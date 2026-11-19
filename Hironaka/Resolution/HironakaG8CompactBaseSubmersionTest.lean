import Hironaka.Resolution.HironakaG8GlobalNativeTestAssembly
import Hironaka.Resolution.HironakaG8SubmersionSurfaceResolution
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList
import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaG8PlaneArrangementSingular

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompactBaseSubmersionTest
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings
  HironakaG8GlobalNativeTestAssembly HironakaG8SubmersionSurfaceResolution
  HironakaG8IntrinsicSingularBlockSchedule HironakaSmoothSubmersionCartesianTower
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaOriginalCanonicalDimensionList
  HironakaResolutionSpaceLocal HironakaActualProjectionTestRecord HironakaG8SurfaceLimitEndpoint

/-- A compact-singular base in any positive ambient dimension has a finite
original TEST whose actual submersion pullback resolves the source.
No compactness of the source singular locus is required. -/
theorem submersion_finite_test_of_compact_base_singular
    {n m : ℕ} {X : CMfd.{0} (n+1)} {Y : CMfd.{0} m}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (hCompact : IsCompact (singularSet (n := n+1) W)) {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel (n+1)) ∞ f) :
    ∃ (D : CMfd.{0} (n+1)) (T : BlowupTower X D) (D' : CMfd.{0} m)
      (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      StageCentres (fun P C => C ⊆ singularSet (n := m)
        (strictTransform m P.proj (f ⁻¹' W))) Q ∧
      IsGeoTestTower (⟨univ,E.map (f ⁻¹' ·),vanishingIdeal (n := m) (f ⁻¹' W),1⟩ :
        MarkedIdeal m Y) Q ∧
      strictTransform m Q.proj (f ⁻¹' W) = g ⁻¹' strictTransform (n+1) T.proj W ∧
      IsClosedSubmanifold m (strictTransform m Q.proj (f ⁻¹' W)) ∧
      IsProperMap Q.proj ∧ Function.Surjective Q.proj ∧
      IsIsomorphismOver m Q.proj (f ⁻¹' singularSet (n := n+1) W)ᶜ := by
  obtain ⟨D,T,hT,hSmooth,_⟩ := global_native_test_of_compact_singular W hW E hE hDense hCompact
  obtain ⟨D',Q,g,hPull,hStage,hTest,hStrict,hQSmooth⟩ :=
    submersion_finite_singular_resolution W hW E hE hf T hT.singular hT.tested hSmooth
  have hY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
  have hP := actual_singular_history_original_regular_protection (f ⁻¹' W) hY Q
    (intrinsic_stage_native_history (f ⁻¹' W) Q hStage)
  have hIso := hP.2.1
  rw [singularSet_preimage_eq hf W] at hIso
  exact ⟨D,T,D',Q,g,hPull,hStage,hTest,hStrict,hQSmooth,hP.2.2.1,
    proper_regular_open_iso_surjective (f ⁻¹' W) Q.proj hP.2.2.1 hP.2.1,hIso⟩

open scoped ProductComplexManifold

/-- The actual line cylinder has connected, noncompact intrinsic singular
locus whenever the base singular locus is connected. -/
theorem cylinder_singular_connected_noncompact
    {n : ℕ} {X : CMfd.{0} n} (W : Set X)
    (hConnected : IsConnected (singularSet (n := n) W)) :
    let f : projectionAmbient X → X := Prod.fst
    IsConnected (singularSet (n := n+1) (f ⁻¹' W)) ∧
      ¬ IsCompact (singularSet (n := n+1) (f ⁻¹' W)) := by
  intro f
  have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1)
    (X := X) (Y := ComplexModel 1)
  rw [singularSet_preimage_eq hf W]
  have hProd : f ⁻¹' singularSet (n := n) W =
      singularSet (n := n) W ×ˢ (univ : Set (ComplexModel 1)) := by
    ext x
    change x.1 ∈ singularSet (n := n) W ↔ x.1 ∈ singularSet (n := n) W ∧ x.2 ∈ univ
    simp
  refine ⟨hProd.symm ▸ hConnected.prod isConnected_univ,?_⟩
  intro hCompact
  obtain ⟨x,hx⟩ := hConnected.nonempty
  have hImage : (Prod.snd : projectionAmbient X → ComplexModel 1) ''
      (f ⁻¹' singularSet (n := n) W) = univ := by
    apply eq_univ_of_forall
    intro y
    exact ⟨(x,y),hx,rfl⟩
  have hFull := hImage ▸ hCompact.image continuous_snd
  have : Nontrivial (ComplexModel 1) := inferInstance
  exact NormedSpace.unbounded_univ ℂ (ComplexModel 1) hFull.isBounded

open HironakaG8PlaneLineProducts HironakaG8PlaneArrangementSingular

abbrev planeBase : CMfd.{0} 2 := CMfd.of (n := 2) (ComplexModel 2)
abbrev lineCylinder : CMfd.{0} (2+1) := projectionAmbient planeBase
abbrev planeCross : Set planeBase := planeLineArrangement 2
abbrev cylinderProj : lineCylinder → planeBase := Prod.fst
abbrev cylinderCross : Set lineCylinder := cylinderProj ⁻¹' planeCross

/-- The literal cylinder over the two-line arrangement has a connected
noncompact singular line and a finite original-test embedded resolution. -/
theorem two_line_cylinder_finite_test :
    singularSet (n := 2+1) cylinderCross = cylinderProj ⁻¹' {(0 : ComplexModel 2)} ∧
    IsConnected (singularSet (n := 2+1) cylinderCross) ∧ ¬ IsCompact (singularSet (n := 2+1) cylinderCross) ∧
    ∃ (D : CMfd.{0} 2) (T : BlowupTower planeBase D) (D' : CMfd.{0} (2+1))
      (Q : BlowupTower lineCylinder D') (g : D' → D),
      IsActualTowerPullback cylinderProj Q T g ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 2+1) (strictTransform (2+1) P.proj cylinderCross)) Q ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := 2+1) cylinderCross,1⟩ : MarkedIdeal (2+1) lineCylinder) Q ∧
      strictTransform (2+1) Q.proj cylinderCross = g ⁻¹' strictTransform 2 T.proj planeCross ∧
      IsClosedSubmanifold (2+1) (strictTransform (2+1) Q.proj cylinderCross) ∧
      IsProperMap Q.proj ∧ Function.Surjective Q.proj ∧
      IsIsomorphismOver (2+1) Q.proj (singularSet (n := 2+1) cylinderCross)ᶜ := by
  have hW : IsComplexAnalyticSubset (n := 2) planeCross := isComplexAnalyticSubset_planeLineArrangement 2
  have hS : singularSet (n := 2) planeCross = {(0 : ComplexModel 2)} := singularSet_planeLineArrangement (by decide)
  have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := 2) (m := 1)
    (X := planeBase) (Y := ComplexModel 1)
  have hV : singularSet (n := 2+1) cylinderCross = cylinderProj ⁻¹' singularSet (n := 2) planeCross :=
    singularSet_preimage_eq (X := planeBase) (Y := lineCylinder) hf planeCross
  have hConn : IsConnected (singularSet (n := 2) planeCross) := hS.symm ▸ isConnected_singleton
  have hComp : IsCompact (singularSet (n := 2) planeCross) := hS.symm ▸ isCompact_singleton
  obtain ⟨hConnV,hNoncompact⟩ := cylinder_singular_connected_noncompact (X := planeBase) planeCross hConn
  refine ⟨hV.trans (congrArg (cylinderProj ⁻¹' ·) hS),hConnV,hNoncompact,?_⟩
  rw [hV]
  exact submersion_finite_test_of_compact_base_singular (n := 1) (X := planeBase) (Y := lineCylinder)
    planeCross hW [] isSNCDivisor_nil (by simp [subset_closure]) hComp hf

#print axioms two_line_cylinder_finite_test
#print axioms submersion_finite_test_of_compact_base_singular
#print axioms cylinder_singular_connected_noncompact

end
end Hironaka.HironakaG8CompactBaseSubmersionTest
