import Hironaka.Resolution.HironakaG8DimensionZeroSingularTest
import Hironaka.Resolution.HironakaG8FiniteSingularHSPotential
import Hironaka.Resolution.HironakaActualHSSingularOriginalPrefix
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PureCurveSingularPhase
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  AnalyticDimensionBasics BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8FiniteSingularHSPotential
  HironakaActualHSSingularOriginalPrefix HironakaActualHSSingularBlowupRestart HironakaOneDimensionalCanonicalSuperlevels
  HironakaHolomorphicJetChartInvariance NormalCrossings HironakaSharpActualAccumulatedTraceResidual
  HironakaActualHilbertSamuelWellFounded HironakaG11PresTowerState

theorem pure_curve_singular_discrete {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hpure : IsPureDim (n := n) W 1) :
    DiscreteTopology (singularSet (n := n) W) := by
  have ha := PureSingularLocus.isComplexAnalyticSubset_diff_regularLocus hW hpure
  have hd := PureSingularLocus.dimLE_diff_regularLocus hW hpure
  have hsub : singularSet (n := n) W ⊆ W \ regularLocus (n := n) W 1 := by
    intro x hx
    exact ⟨(mem_singularSet_iff.mp hx).1,(mem_singularSet_iff.mp hx).2 1⟩
  exact isDiscrete_iff_discreteTopology.mp ((isDiscrete_of_analytic_dimLE_zero ha hd).mono hsub)

theorem singular_to_curve_stage {n : ℕ} {X : CMfd.{0} n} (W : Set X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
        regularLocus (n := n) (strictTransform n P.proj W) 1) T
  | _, .refl, _ => trivial
  | _, .step T C _ _, h => ⟨singular_to_curve_stage W T h.1, by
      intro x hx
      exact ⟨(mem_singularSet_iff.mp (h.2 hx)).1,(mem_singularSet_iff.mp (h.2 hx)).2 1⟩⟩

/-- Intrinsic singular-centred histories preserve pure analytic curve geometry,
without any compactness hypothesis on the initial carrier. -/
theorem pure_curve_current_geometry {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hpure : IsPureDim (n := n) W 1)
    (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    IsComplexAnalyticSubset (n := n) (strictTransform n T.proj W) ∧
      IsPureDim (n := n) (strictTransform n T.proj W) 1 := by
  have hdense := HironakaHypersurfaceMultiplicityDescent.strictTransform_subset_closure_regularLocus_of_stageCentres_singular
    hW.isClosed (actualPure_subset_closure_regularLocus hW hpure) T (singular_to_curve_stage W T hStage)
  exact ⟨HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW,
    actualPure_of_subset_closure_regularLocus hdense⟩

/-- A singular-centred history of a possibly noncompact pure curve tests the
same original mark-one ideal with any initial SNC boundary. -/
theorem pure_curve_history_is_original_test {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (_hn : 1 < n) (hpure : IsPureDim (n := n) W 1)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T
  := by
  have hDim : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      DimLE (n := n) (singularSet (n := n) (strictTransform n T.proj W)) 0 := by
    intro Y T hStage
    have hGeo := pure_curve_current_geometry W hW hpure T hStage
    have hSa := PureSingularLocus.isComplexAnalyticSubset_diff_regularLocus hGeo.1 hGeo.2
    have hSd := PureSingularLocus.dimLE_diff_regularLocus hGeo.1 hGeo.2
    have hSub : singularSet (n := n) (strictTransform n T.proj W) ⊆
        strictTransform n T.proj W \ regularLocus (n := n) (strictTransform n T.proj W) 1 := by
      intro x hx
      exact ⟨(mem_singularSet_iff.mp hx).1,(mem_singularSet_iff.mp hx).2 1⟩
    exact DimensionMonotone.DimLE.anti hSa hSub hSd
  intro Y T hStage
  exact HironakaG8DimensionZeroSingularTest.dimension_zero_singular_history_is_original_test W hW hDim E hE T hStage

theorem compact_pure_curve_global_phase_multiset_descent {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hpure : IsPureDim (n := n) W 1)
    (hNe : (singularSet (n := n) W).Nonempty) :
    ∃ (hOld : (singularSet (n := n) W).Finite) (Y : CMfd.{0} n) (Q : BlowupTower X Y)
      (hNew : (singularSet (n := n) (strictTransform n Q.proj W)).Finite),
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      (∀ y ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ) ∧
      Multiset.IsDershowitzMannaLT (singularHSProfiles (strictTransform n Q.proj W) hNew)
        (singularHSProfiles W hOld) := by
  let discreteW : DiscreteTopology (singularSet (n := n) W) := pure_curve_singular_discrete hW hpure
  have hKS : IsCompact (singularSet (n := n) W) :=
    hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) (singularSet_subset W)
  apply discrete_singular_global_phase_multiset_descent hn W hW hKS hNe
  intro Y T hstage
  have hgeo := actual_singular_prefix_current_geometry hW hK hpure T
    (singular_to_curve_stage W T hstage)
  exact pure_curve_singular_discrete hgeo.1 hgeo.2.2
/-- Every singular-centred pure-curve history tests the same original
mark-one ideal with any given SNC initial boundary. -/
theorem pure_curve_singular_history_is_original_test {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (_hK : IsCompact W)
    (hn : 1 < n) (hpure : IsPureDim (n := n) W 1)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T :=
  pure_curve_history_is_original_test W hW hn hpure E hE

/-- A compact pure curve admits a finite actual singular-centred tower with
smooth strict transform; the same tower tests any initial SNC boundary. -/
theorem compact_pure_curve_finite_singular_resolution {n : ℕ} (hn : 1<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hpure : IsPureDim (n := n) W 1)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T ∧
      singularSet (n := n) (strictTransform n T.proj W) = ∅ := by
  let wfHS : WellFoundedLT (ActualHilbertSamuelProfile n) := actual_hilbertSamuel_wellFounded n
  have hwf : WellFounded (Multiset.IsDershowitzMannaLT : Multiset (ActualHilbertSamuelProfile n) → Multiset (ActualHilbertSamuelProfile n) → Prop) :=
    Multiset.wellFounded_isDershowitzMannaLT
  have hall : ∀ (s : Multiset (ActualHilbertSamuelProfile n)) (A : CMfd.{0} n) (V : Set A)
      (hV : IsComplexAnalyticSubset (n := n) V) (hCV : IsCompact V)
      (hPV : IsPureDim (n := n) V 1) (hFin : (singularSet (n := n) V).Finite),
      singularHSProfiles V hFin = s →
      ∃ (B : CMfd.{0} n) (T : BlowupTower A B),
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj V)) T ∧
        singularSet (n := n) (strictTransform n T.proj V) = ∅ := by
    intro s
    induction s using hwf.induction with
    | h s ih =>
      intro A V hV hCV hPV hFin hs
      by_cases hNe : (singularSet (n := n) V).Nonempty
      · obtain ⟨hOld,B,Q,hNew,hTest,hStage,hBound,hDrop⟩ :=
          compact_pure_curve_global_phase_multiset_descent (by omega) V hV hCV hPV hNe
        have hGeo := actual_singular_prefix_current_geometry hV hCV hPV Q
          (singular_to_curve_stage V Q hStage)
        have hsmaller : Multiset.IsDershowitzMannaLT
            (singularHSProfiles (strictTransform n Q.proj V) hNew) s := by
          simpa [← hs] using hDrop
        obtain ⟨D,R,hR,hEmpty⟩ := ih _ hsmaller B (strictTransform n Q.proj V)
          hGeo.1 hGeo.2.1 hGeo.2.2 hNew rfl
        refine ⟨D,Q.append R,HironakaG8IntrinsicSingularBlockSchedule.intrinsic_stage_append V Q R hStage hR,?_⟩
        have hstrict := StrictTransformComposition.strictTransform_comp Q.contMDiff_proj R.contMDiff_proj V
        rw [← BlowupTower.proj_append] at hstrict
        rw [hstrict]
        exact hEmpty
      · refine ⟨A, .refl, trivial, ?_⟩
        simpa only [BlowupTower.proj_refl, strictTransform_id hV.isClosed] using
          Set.not_nonempty_iff_eq_empty.mp hNe
  have hFin : (singularSet (n := n) W).Finite :=
    (hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) (singularSet_subset W)).finite
      (isDiscrete_iff_discreteTopology.mpr (pure_curve_singular_discrete hW hpure))
  obtain ⟨Y,T,hStage,hEmpty⟩ := hall (singularHSProfiles W hFin) X W hW hK hpure hFin rfl
  exact ⟨Y,T,hStage,pure_curve_singular_history_is_original_test W hW hK hn hpure E hE T hStage,hEmpty⟩

/-- The same actual finite history has a closed smooth strict transform. -/
theorem compact_pure_curve_finite_smooth_strict_transform {n : ℕ} (hn : 1<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hpure : IsPureDim (n := n) W 1)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) := by
  obtain ⟨Y,T,hStage,hTest,hEmpty⟩ := compact_pure_curve_finite_singular_resolution hn W hW hK hpure E hE
  have hGeo := actual_singular_prefix_current_geometry hW hK hpure T (singular_to_curve_stage W T hStage)
  refine ⟨Y,T,hStage,hTest,hGeo.1.isClosed,?_⟩
  intro x hx
  by_contra h
  have hxS : x ∈ singularSet (n := n) (strictTransform n T.proj W) :=
    mem_singularSet_iff.mpr ⟨hx,fun d hd => h ⟨d,hd⟩⟩
  rw [hEmpty] at hxS
  exact hxS

end
end Hironaka.HironakaG8PureCurveSingularPhase
