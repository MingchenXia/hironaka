import Hironaka.Resolution.HironakaActualHilbertSamuelLexOrder
import Hironaka.Resolution.HironakaG11PresTowerState
import Hironaka.Resolution.HironakaActualGeometricCleanupComposition
import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase
import Hironaka.Resolution.HironakaG8SingularTestBoundaryTransfer
import Hironaka.Resolution.HironakaUniformHistoricalSuccessorCompactSingular

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompactLexInduction

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings HironakaHolomorphicJetChartInvariance
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaActualHilbertSamuelLexOrder HironakaActualHilbertSamuelWellFounded
  HironakaHolomorphicJetRankLoci HironakaG11PresTowerState
  HironakaActualGeometricCleanupComposition HironakaSharpActualFiniteChronologicalHistory
  HironakaG8SingularTestBoundaryTransfer HironakaUniformHistoricalSuccessorCompactSingular

variable {n : ℕ} {X : CMfd.{0} n}

/-- The actual singular Hilbert–Samuel value in the well-founded lexicographic order. -/
private def lexHS (W : Set X) (x : X) : ActualLexHilbertSamuelProfile n :=
  ⟨toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x),
    analytic_hilbertSamuel_realizable (wholeChartStalkIdeal (vanishingIdeal (n := n) W) x x
      (mem_chart_source (ComplexModel n) x))⟩

/-- Append a test of the reduced current carrier on the prefix's exact accumulated
boundary, retaining the test and singular centre positions relative to the original input. -/
theorem original_test_and_singular_stages_append {Y Z : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {E : List (Set X)} (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hTStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hS : IsGeoTestTower (⟨univ,
      (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E,
      vanishingIdeal (n := n) (strictTransform n T.proj W), 1⟩ : MarkedIdeal n Y) S)
    (hSStage : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj (strictTransform n T.proj W))) S) :
    IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) (T.append S) ∧
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (T.append S) := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let G := geometricTemplate (univ : Set X) E
  let F := (geoTransformAlong M T).E
  let N : MarkedIdeal n Y := ⟨univ, F, vanishingIdeal (n := n) (strictTransform n T.proj W), 1⟩
  have hSame : (geoTransformAlong G T).E = F :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := G) (𝔫 := M) rfl T
  have hAppGeo : IsGeoTestTower G (T.append S) := by
    apply (geometric_test_append_iff (univ : Set X) E T S).mpr
    refine ⟨geometric_test_of_test M E (List.Sublist.refl _) T hT, ?_⟩
    change IsGeoTestTower (geometricTemplate (strictAlong T univ) (geoTransformAlong G T).E) S
    rw [HironakaG4CompactWholeMonomialMaskPhase.strict_univ, hSame]
    exact geometric_test_of_test N F (List.Sublist.refl _) S hS
  have hAppStage := intrinsic_stage_append W T S hTStage hSStage
  exact ⟨singular_auxiliary_test_is_original_test W hW E hE G rfl (T.append S) hAppGeo hAppStage,
    hAppStage⟩

/-- The current singular locus is a closed subset of the proper inverse image
of the original singular locus along an intrinsically singular-centred history. -/
private theorem isCompact_current_singular {Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact (singularSet (n := n) W)) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    IsCompact (singularSet (n := n) (strictTransform n T.proj W)) := by
  have hGeo := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)
  exact (hGeo.2.2.1.isCompact_preimage hK).of_isClosed_subset
    (isClosed_singularSet hGeo.2.2.2.1.isClosed) hGeo.2.2.2.2.2.1

private theorem exists_singular_resolution_of_lex_phases_core
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact (singularSet (n := n) W))
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (Supported : ∀ {A : CMfd.{0} n}, Set A → Prop)
    (hSupported : ∀ {A : CMfd.{0} n} (T : BlowupTower X A),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      Supported (strictTransform n T.proj W))
    (hPhase : ∀ {A : CMfd.{0} n} (V : Set A), IsComplexAnalyticSubset (n := n) V →
      Supported V → ¬ IsClosedSubmanifold n V →
      ∀ F : List (Set A), IsSNCDivisor n F →
        (∀ D ∈ F, ∀ x ∈ singularSet (n := n) V, x ∈ D →
          ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ V) →
        ∃ a ∈ singularSet (n := n) V, ∃ (B : CMfd.{0} n) (S : BlowupTower A B),
          IsGeoTestTower (⟨univ, F, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n A) S ∧
          StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj V)) S ∧
          ∀ z ∈ singularSet (n := n) (strictTransform n S.proj V),
            toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n S.proj V)) z) <
              toLex (hilbertSamuelAt (vanishingIdeal (n := n) V) a))
    (hRestart : ∀ {A : CMfd.{0} n} (T : BlowupTower X A),
      let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
      let V := strictTransform n T.proj W
      IsGeoTestTower M T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      ∀ D ∈ (geoTransformAlong M T).E, ∀ x ∈ singularSet (n := n) V, x ∈ D →
        ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ V) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) := by
  classical
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let Goal := ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y), IsGeoTestTower M T ∧
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
    IsClosedSubmanifold n (strictTransform n T.proj W)
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
    hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hSolve : ∀ H : ActualLexHilbertSamuelProfile n,
      ∀ {A : CMfd.{0} n} (T : BlowupTower X A), IsGeoTestTower M T →
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
        (∀ x ∈ singularSet (n := n) (strictTransform n T.proj W),
          lexHS (strictTransform n T.proj W) x ≤ H) → Goal := by
    intro H
    induction H using (actual_hilbertSamuel_lex_wellFounded n).wf.induction with
    | h H ih =>
      intro A T hT hTStage hUpper
      let V := strictTransform n T.proj W
      by_cases hSmooth : IsClosedSubmanifold n V
      · exact ⟨A, T, hT, hTStage, hSmooth⟩
      let F := (geoTransformAlong M T).E
      have hGeo := actual_singular_history_original_regular_protection W hW T
        (intrinsic_stage_native_history W T hTStage)
      have hF : IsSNCDivisor n F :=
        (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
      obtain ⟨a, ha, B, S, hS, hSStage, hDrop⟩ :=
        hPhase V hGeo.2.2.2.1 (hSupported T hTStage) hSmooth F hF (hRestart T hT hTStage)
      obtain ⟨hTS, hTSStage⟩ := original_test_and_singular_stages_append hW hE T S hT hTStage hS hSStage
      let V' := strictTransform n (T.append S).proj W
      have hStrict : V' = strictTransform n S.proj V := by
        change strictTransform n (T.append S).proj W = _
        rw [BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W]
      by_cases hSmooth' : IsClosedSubmanifold n V'
      · exact ⟨B, T.append S, hTS, hTSStage, hSmooth'⟩
      have hGeo' := actual_singular_history_original_regular_protection W hW (T.append S)
        (intrinsic_stage_native_history W (T.append S) hTSStage)
      obtain ⟨b, hb, hMax, _⟩ := exists_compact_singular_maximal_stratum_of_compact_singular
        hGeo'.2.2.2.1 (isCompact_current_singular hW hK (T.append S) hTSStage) hSmooth'
      have hLower : lexHS V' b < lexHS V a := by
        have hb' : b ∈ singularSet (n := n) (strictTransform n S.proj V) := hStrict ▸ hb
        rw [hStrict]
        exact hDrop b hb'
      exact ih _ (hLower.trans_le (hUpper a ha)) (T.append S) hTS hTSStage hMax
  by_cases hSmooth : IsClosedSubmanifold n W
  · refine ⟨X, .refl, trivial, trivial, ?_⟩
    simpa only [BlowupTower.proj_refl, strictTransform_id hW.isClosed] using hSmooth
  obtain ⟨a, _, hMax, _⟩ := exists_compact_singular_maximal_stratum_of_compact_singular hW hK hSmooth
  apply hSolve (lexHS W a) (.refl : BlowupTower X X) trivial trivial
  rw [BlowupTower.proj_refl, strictTransform_id hW.isClosed]
  exact hMax


/-- Strict lexicographic phases over a compact singular locus give one actual
finite original-test resolution tower. Each restart uses the original prefix's
exact accumulated boundary and retains all its centres. -/
theorem exists_compact_singular_resolution_of_lex_phases_of_compact_singular
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact (singularSet (n := n) W))
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hPhase : ∀ {A : CMfd.{0} n} (V : Set A), IsComplexAnalyticSubset (n := n) V →
      IsCompact (singularSet (n := n) V) → ¬ IsClosedSubmanifold n V →
      ∀ F : List (Set A), IsSNCDivisor n F →
        (∀ D ∈ F, ∀ x ∈ singularSet (n := n) V, x ∈ D →
          ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ V) →
        ∃ a ∈ singularSet (n := n) V, ∃ (B : CMfd.{0} n) (S : BlowupTower A B),
          IsGeoTestTower (⟨univ, F, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n A) S ∧
          StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj V)) S ∧
          ∀ z ∈ singularSet (n := n) (strictTransform n S.proj V),
            toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n S.proj V)) z) <
              toLex (hilbertSamuelAt (vanishingIdeal (n := n) V) a))
    (hRestart : ∀ {A : CMfd.{0} n} (T : BlowupTower X A),
      let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
      let V := strictTransform n T.proj W
      IsGeoTestTower M T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      ∀ D ∈ (geoTransformAlong M T).E, ∀ x ∈ singularSet (n := n) V, x ∈ D →
        ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ V) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) := by
  exact exists_singular_resolution_of_lex_phases_core hW hK E hE
    (fun V => IsCompact (singularSet (n := n) V)) (isCompact_current_singular hW hK)
    hPhase hRestart

/-- Strict lexicographic phases over compact carriers give one actual finite
original-test resolution tower with singular-centred stages. -/
theorem exists_compact_singular_resolution_of_lex_phases
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hPhase : ∀ {A : CMfd.{0} n} (V : Set A), IsComplexAnalyticSubset (n := n) V →
      IsCompact V → ¬ IsClosedSubmanifold n V →
      ∀ F : List (Set A), IsSNCDivisor n F →
        (∀ D ∈ F, ∀ x ∈ singularSet (n := n) V, x ∈ D →
          ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ V) →
        ∃ a ∈ singularSet (n := n) V, ∃ (B : CMfd.{0} n) (S : BlowupTower A B),
          IsGeoTestTower (⟨univ, F, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n A) S ∧
          StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj V)) S ∧
          ∀ z ∈ singularSet (n := n) (strictTransform n S.proj V),
            toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n S.proj V)) z) <
              toLex (hilbertSamuelAt (vanishingIdeal (n := n) V) a))
    (hRestart : ∀ {A : CMfd.{0} n} (T : BlowupTower X A),
      let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
      let V := strictTransform n T.proj W
      IsGeoTestTower M T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      ∀ D ∈ (geoTransformAlong M T).E, ∀ x ∈ singularSet (n := n) V, x ∈ D →
        ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ V) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) := by
  have hSingular : IsCompact (singularSet (n := n) W) :=
    hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) (singularSet_subset W)
  exact exists_singular_resolution_of_lex_phases_core hW hSingular E hE
    (fun V => IsCompact V) (fun T hStage =>
      (actual_singular_history_original_regular_protection W hW T
        (intrinsic_stage_native_history W T hStage)).2.2.2.2.1 hK)
    hPhase hRestart

end

end Hironaka.HironakaG8CompactLexInduction
