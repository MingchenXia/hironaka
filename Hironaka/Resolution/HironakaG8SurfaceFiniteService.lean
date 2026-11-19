import Hironaka.Resolution.HironakaG8HereditaryDiscreteFiniteService
import Hironaka.Resolution.HironakaG8SurfaceSingularPhase
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SurfaceFiniteService
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves AnalyticDimensionBasics
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaHolomorphicJetChartInvariance
  HironakaG8FiniteIsolatedProfilePhase HironakaG8FiniteSingularHSPotential HironakaG8PureCurveSingularPhase
  HironakaG8SurfaceSingularPhase HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaActualHilbertSamuelWellFounded
  HironakaG11PresTowerState NormalCrossings

/-- Serve all descendants above a finite nonempty set in one phase, strictly
reducing their finite multiset of profiles. -/
theorem surface_finite_subset_phase {X : CMfd.{0} 2} (W F : Set X)
    (hW : IsComplexAnalyticSubset (n := 2) W) (hF : F.Finite)
    (hFS : F ⊆ singularSet (n := 2) W) (hNe : F.Nonempty) :
    ∃ (Y : CMfd.{0} 2) (Q : BlowupTower X Y)
      (hNew : (singularSet (n := 2) (strictTransform 2 Q.proj W) ∩ Q.proj ⁻¹' F).Finite),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) Q ∧
      CentresOver F Q ∧
      Multiset.IsDershowitzMannaLT
        (finiteHSProfiles (strictTransform 2 Q.proj W)
          (singularSet (n := 2) (strictTransform 2 Q.proj W) ∩ Q.proj ⁻¹' F) hNew)
        (finiteHSProfiles W F hF) := by
  let discreteW : DiscreteTopology (singularSet (n := 2) W) := surface_singular_discrete hW
  have hPersist : ∀ {Y : CMfd.{0} 2} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T →
      DiscreteTopology (singularSet (n := 2) (strictTransform 2 T.proj W)) := by
    intro Y T hT
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T hT)
    exact surface_singular_discrete hp.2.2.2.1
  exact HironakaG8HereditaryDiscreteFiniteService.hereditary_discrete_finite_subset_phase
    (by decide) W F hW hPersist hF hFS hNe

/-- Finite singular-point footprint service: every actual singular descendant
above the chosen finite set disappears, with centres supported over that set. -/
theorem surface_finite_subset_service {X : CMfd.{0} 2} (W F : Set X)
    (hW : IsComplexAnalyticSubset (n := 2) W) (hF : F.Finite)
    (hFS : F ⊆ singularSet (n := 2) W) (E : List (Set X)) (hE : IsSNCDivisor 2 E) :
    ∃ (Y : CMfd.{0} 2) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T ∧
      CentresOver F T ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T ∧
      singularSet (n := 2) (strictTransform 2 T.proj W) ∩ T.proj ⁻¹' F = ∅ := by
  let P : ∀ A : CMfd.{0} 2, Set A → Prop := fun _ _ => True
  have hDisc : ∀ (A : CMfd.{0} 2) (V : Set A), IsComplexAnalyticSubset (n := 2) V → P A V →
      DiscreteTopology (singularSet (n := 2) V) := fun _ _ hV _ => surface_singular_discrete hV
  have hNext : ∀ {A B : CMfd.{0} 2} (V : Set A), IsComplexAnalyticSubset (n := 2) V → P A V →
      ∀ (T : BlowupTower A B),
        StageCentres (fun Q C => C ⊆ singularSet (n := 2) (strictTransform 2 Q.proj V)) T →
        P B (strictTransform 2 T.proj V) := by
    intros
    trivial
  obtain ⟨Y,T,hStage,hOver,hEmpty⟩ :=
    HironakaG8HereditaryDiscreteFiniteService.hereditary_discrete_finite_subset_service_core
      (by decide) W F P hDisc hNext hW trivial hF hFS
  exact ⟨Y,T,hStage,hOver,surface_singular_history_is_original_test W hW E hE T hStage,hEmpty⟩

end
end Hironaka.HironakaG8SurfaceFiniteService
