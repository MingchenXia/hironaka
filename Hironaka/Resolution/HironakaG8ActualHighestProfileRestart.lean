import Hironaka.Resolution.HironakaG8FreshNativeCompactFirstCut
import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaG8LabelledOriginalCanonicalPrefixes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ActualHighestProfileRestart
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings
  HironakaHolomorphicJetChartInvariance HironakaG8NativePhaseCertificate
  HironakaG8DenseBoundaryRestart HironakaActualCompactHSMaximalProfile
  HironakaLocalPrincipalization HironakaG8LabelledOriginalCanonicalPrefixes NormalCrossingsInvariance
  HironakaBaseChange HironakaActualVanishingIntrinsicHSTransport

/-- An actual singular-centred prefix with dense initial divisor complement
supplies a certified native phase at the attained highest singular profile
over a compact base task. The entire clipped prefix lands in its phase open. -/
theorem exists_actual_highest_profile_restart_over_compact_task
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ D ∈ E, D))
    (P : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) P)
    (hStage : StageCentres (fun T C => C ⊆ singularSet (n := n) (strictTransform n T.proj W)) P)
    (K : Set X) (hK : IsCompact K)
    (hNe : (P.proj ⁻¹' K ∩ singularSet (n := n) (strictTransform n P.proj W)).Nonempty) :
    let A := strictTransform n P.proj W
    let F := (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) P).E
    ∃ a ∈ P.proj ⁻¹' K ∩ singularSet (n := n) A,
      (∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n) A,
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) x) ≤
          toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) a)) ∧
      (∀ D ∈ F, ∀ x ∈ singularSet (n := n) A, x ∈ D →
        ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ A) ∧
      ∃ (V : Opens Y) (O : Opens X), K ⊆ O ∧ openPreimage P O ≤ V ∧
        ∃ (Z : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) V) Z),
          ActualNativePhase ((Subtype.val : V → Y) ⁻¹' A)
            (F.map ((Subtype.val : V → Y) ⁻¹' ·))
            (hilbertSamuelAt (vanishingIdeal (n := n) A) a) T ∧
          RawEpochChartPrefixes hn ((Subtype.val : V → Y) ⁻¹' A)
            (F.map ((Subtype.val : V → Y) ⁻¹' ·))
            (hilbertSamuelAt (vanishingIdeal (n := n) A) a) T ∧
          phaseLevel (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' A) (hilbertSamuelAt (vanishingIdeal (n := n) A) a) =
            (Subtype.val : V → Y) ⁻¹' phaseLevel A (hilbertSamuelAt (vanishingIdeal (n := n) A) a) := by
  intro A F
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW,hE,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hA : IsComplexAnalyticSubset (n := n) A :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hF : IsSNCDivisor n F :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM P hTest).isSNCDivisor
  have hADense := strict_transform_dense_off_accumulated_boundary hW E hE hDense P hTest hStage
  have hNot := boundary_noncontainment_at_current_singular_of_dense_complement hn hW E hE hDense P hTest hStage
  let L := P.proj ⁻¹' K
  have hProper := isProperMap_proj P
  have hL : IsCompact L := hProper.isCompact_preimage hK
  obtain ⟨a,ha,hMax⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) A)
    (CartanIrreducible.cartanCoherence A hA) (L ∩ singularSet (n := n) A)
    (hL.inter_right (isClosed_singularSet hA.isClosed)) hNe
  obtain ⟨V,hLV,Z,T,hPhase⟩ :=
    exists_actual_native_phase_near_compact hn hA F hF hADense L hL a ha hMax
  let O : Opens X := ⟨(P.proj '' (V : Set Y)ᶜ)ᶜ,(hProper.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hAV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hA V
  have hFV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hF
  have hRaw := actual_native_phase_raw_chart_prefixes hn hAV hFV hPhase
  refine ⟨a,ha,hMax,hNot,V,O,?_,?_,Z,T,hPhase,hRaw,?_⟩
  · intro x hx
    rintro ⟨y,hy,rfl⟩
    exact hy (hLV hx)
  · intro y hy
    by_contra hyV
    exact hy ⟨y,hyV,rfl⟩
  · ext x
    change hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : V → Y) ⁻¹' A)) x =
      hilbertSamuelAt (vanishingIdeal (n := n) A) a ↔
      hilbertSamuelAt (vanishingIdeal (n := n) A) x.val =
        hilbertSamuelAt (vanishingIdeal (n := n) A) a
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any V A x)]

end
end Hironaka.HironakaG8ActualHighestProfileRestart
