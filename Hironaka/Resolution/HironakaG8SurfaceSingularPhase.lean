import Hironaka.Resolution.HironakaG8DimensionZeroSingularTest
import Hironaka.Resolution.HironakaG8PureCurveSingularPhase
import Hironaka.Resolution.HironakaGeneralSingularCentreCodimension
import Hironaka.Resolution.HironakaResolutionSpaceSingular
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SurfaceSingularPhase
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves AnalyticDimensionBasics
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaGeneralSingularCentreCodimension
  HironakaResolutionSpaceSingular HironakaOneDimensionalCanonicalSuperlevels
  HironakaG8FiniteSingularHSPotential HironakaG8PureCurveSingularPhase
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaHolomorphicJetChartInvariance HironakaActualHilbertSamuelWellFounded HironakaG11PresTowerState
  NormalCrossings HironakaSharpActualAccumulatedTraceResidual

theorem surface_singular_discrete {X : CMfd.{0} 2} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := 2) W) : DiscreteTopology (singularSet (n := 2) W) := by
  have hSa := isComplexAnalyticSubset_singularSet hW
  have hSd : DimLE (n := 2) (singularSet (n := 2) W) 0 := by
    intro x k hreg
    have hk := regular_intrinsic_singular_centre_add_two_le hW (subset_rfl) hreg
    omega
  exact isDiscrete_iff_discreteTopology.mp (isDiscrete_of_analytic_dimLE_zero hSa hSd)

theorem surface_singular_phase_multiset_descent {X : CMfd.{0} 2} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := 2) W) (hK : IsCompact (singularSet (n := 2) W))
    (hNe : (singularSet (n := 2) W).Nonempty) :
    ∃ (hOld : (singularSet (n := 2) W).Finite) (Y : CMfd.{0} 2) (Q : BlowupTower X Y)
      (hNew : (singularSet (n := 2) (strictTransform 2 Q.proj W)).Finite),
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) Q ∧
      (∀ y ℓ, hilbertSamuelAt (vanishingIdeal (n := 2) (strictTransform 2 Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := 2) W) (Q.proj y) ℓ) ∧
      Multiset.IsDershowitzMannaLT (singularHSProfiles (strictTransform 2 Q.proj W) hNew)
        (singularHSProfiles W hOld) := by
  let discreteW : DiscreteTopology (singularSet (n := 2) W) := surface_singular_discrete hW
  apply discrete_singular_global_phase_multiset_descent (by decide) W hW hK hNe
  intro Y T hstage
  exact surface_singular_discrete (actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hstage)).2.2.2.1

theorem surface_finite_singular_resolution {X : CMfd.{0} 2} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := 2) W) (hK : IsCompact (singularSet (n := 2) W)) :
    ∃ (Y : CMfd.{0} 2) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T ∧
      singularSet (n := 2) (strictTransform 2 T.proj W) = ∅ := by
  let wfHS : WellFoundedLT (ActualHilbertSamuelProfile 2) := actual_hilbertSamuel_wellFounded 2
  have hwf : WellFounded (Multiset.IsDershowitzMannaLT : Multiset (ActualHilbertSamuelProfile 2) → Multiset (ActualHilbertSamuelProfile 2) → Prop) :=
    Multiset.wellFounded_isDershowitzMannaLT
  have hall : ∀ (s : Multiset (ActualHilbertSamuelProfile 2)) (A : CMfd.{0} 2) (V : Set A)
      (hV : IsComplexAnalyticSubset (n := 2) V) (hCV : IsCompact (singularSet (n := 2) V))
      (hFin : (singularSet (n := 2) V).Finite), singularHSProfiles V hFin = s →
      ∃ (B : CMfd.{0} 2) (T : BlowupTower A B),
        StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj V)) T ∧
        singularSet (n := 2) (strictTransform 2 T.proj V) = ∅ := by
    intro s
    induction s using hwf.induction with
    | h s ih =>
      intro A V hV hCV hFin hs
      by_cases hNe : (singularSet (n := 2) V).Nonempty
      · obtain ⟨hOld,B,Q,hNew,hTest,hStage,hBound,hDrop⟩ :=
          surface_singular_phase_multiset_descent V hV hCV hNe
        have hGeo := actual_singular_history_original_regular_protection V hV Q
          (intrinsic_stage_native_history V Q hStage)
        let discreteQ : DiscreteTopology (singularSet (n := 2) (strictTransform 2 Q.proj V)) :=
          surface_singular_discrete hGeo.2.2.2.1
        have hNewCompact := (current_singular_compact_finite V hV hCV Q hStage).1
        have hsmaller : Multiset.IsDershowitzMannaLT
            (singularHSProfiles (strictTransform 2 Q.proj V) hNew) s := by
          simpa [← hs] using hDrop
        obtain ⟨D,R,hR,hEmpty⟩ := ih _ hsmaller B (strictTransform 2 Q.proj V)
          hGeo.2.2.2.1 hNewCompact hNew rfl
        refine ⟨D,Q.append R,HironakaG8IntrinsicSingularBlockSchedule.intrinsic_stage_append V Q R hStage hR,?_⟩
        have hstrict := StrictTransformComposition.strictTransform_comp Q.contMDiff_proj R.contMDiff_proj V
        rw [← BlowupTower.proj_append] at hstrict
        rw [hstrict]
        exact hEmpty
      · refine ⟨A, .refl, trivial, ?_⟩
        simpa only [BlowupTower.proj_refl, strictTransform_id hV.isClosed] using
          Set.not_nonempty_iff_eq_empty.mp hNe
  have hFin : (singularSet (n := 2) W).Finite :=
    hK.finite (isDiscrete_iff_discreteTopology.mpr (surface_singular_discrete hW))
  exact hall (singularHSProfiles W hFin) X W hW hK hFin rfl
/-- For any analytic surface subset, every intrinsic singular history is a
test of the same original mark-one input, with arbitrary initial SNC boundary. -/
theorem surface_singular_history_is_original_test {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : IsSNCDivisor 2 E) :
    ∀ {Y : CMfd.{0} 2} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T
  := by
  have hDim : ∀ {Y : CMfd.{0} 2} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T →
      DimLE (n := 2) (singularSet (n := 2) (strictTransform 2 T.proj W)) 0 := by
    intro Y T hStage
    have hCurrent := (actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T hStage)).2.2.2.1
    intro x k hreg
    have hk := regular_intrinsic_singular_centre_add_two_le hCurrent subset_rfl hreg
    omega
  intro Y T hStage
  exact HironakaG8DimensionZeroSingularTest.dimension_zero_singular_history_is_original_test W hW hDim E hE T hStage

theorem surface_finite_original_test_resolution {X : CMfd.{0} 2} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := 2) W) (hK : IsCompact (singularSet (n := 2) W))
    (E : List (Set X)) (hE : IsSNCDivisor 2 E) :
    ∃ (Y : CMfd.{0} 2) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T ∧
      IsClosedSubmanifold 2 (strictTransform 2 T.proj W) := by
  obtain ⟨Y,T,hStage,hEmpty⟩ := surface_finite_singular_resolution W hW hK
  have hGeo := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)
  exact ⟨Y,T,hStage,surface_singular_history_is_original_test W hW E hE T hStage,
    hGeo.2.2.2.2.2.2.mp hEmpty⟩

end
end Hironaka.HironakaG8SurfaceSingularPhase
