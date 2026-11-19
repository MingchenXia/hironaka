import Hironaka.Resolution.HironakaG8LabelledOriginalCanonicalPrefixes
import Hironaka.Resolution.HironakaG8MergedHSLocality

/-! # Exact current profiles on occupied physical overlaps -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedEpochOverlap
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism NormalCrossings HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaHolomorphicJetChartInvariance HironakaActualVanishingIntrinsicHSTransport
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaG3EmptyAwareHistory
  HironakaG8NativePhaseCertificate HironakaG8LabelledOriginalCanonicalPrefixes
  HironakaG8NativePhaseHSControl HironakaG8MergedHSLocality
  HironakaG11PresLineState HironakaActualOpenEmbeddingVanishingIdeal
open ResolutionInvariantExt (IsEmptyTower)

private abbrev original {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) :
    MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩

/-- Every actual centre of a certified epoch has its original label as
its exact current strict-transform profile. Coverage and native
resolution on the literal chart restriction discharge the local read. -/
theorem actual_epoch_exact_current_centre_profile {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {W : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {T : BlowupTower X Y} (hW : IsComplexAnalyticSubset (n := n) W)
    (hE : IsSNCDivisor n E) (hPhase : ActualNativePhase W E H T) :
    StageCentres (fun P C => ∀ c ∈ C, ∀ l,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) c l = H l) T := by
  obtain ⟨I,A,hRes,_⟩ := actual_native_phase_raw_chart_prefixes hn hW hE hPhase
  have hProfile (i : I) := native_test_stages_HS_profile (A.record i)
    (hW.isClosed.preimage continuous_subtype_val) (A.native i).hsTowerState
    (restrict (A.openSet i) T) (hRes i).1
  have assemble : ∀ {D : CMfd.{0} n} (S : BlowupTower X D), CentresOver (phaseLevel W H) S →
      (∀ i : I, StageCentres (fun P C => ∀ c ∈ C, ∀ l,
        hilbertSamuelAt (vanishingIdeal (n := n)
          (strictTransform n P.proj ((Subtype.val : A.openSet i → X) ⁻¹' W))) c l = H l)
        (restrict (A.openSet i) S)) →
      StageCentres (fun P C => ∀ c ∈ C, ∀ l,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) c l = H l) S := by
    intro D S
    induction S with
    | refl => exact fun _ _ => trivial
    | @step D F S C π hπ ih =>
      intro hf hp
      refine ⟨ih hf.1 (fun i => (hp i).1),?_⟩
      intro c hc l
      obtain ⟨i,hi⟩ := A.covers (S.proj c) (hf.2 hc)
      let z : openPreimage S (A.openSet i) := ⟨c,hi⟩
      have hZ := (hp i).2 z (show z ∈ (Subtype.val : openPreimage S (A.openSet i) → D) ⁻¹' C from hc) l
      rw [strictTransform_restricted_tower (A.openSet i) S W,
        hilbertSamuelAt_vanishing_actual_open_any] at hZ
      exact hZ
  exact assemble T hPhase.supports hProfile

/-- The actual chart restriction retains the original epoch label,
full ordered mark-one TEST, and the exact current strict profile at
every retained centre point. -/
theorem actual_epoch_restrict_original_label_test_and_profile {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {W : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {T : BlowupTower X Y} (hW : IsComplexAnalyticSubset (n := n) W)
    (hE : IsSNCDivisor n E) (p : ActualNativePhase W E H T) (U : Opens X) :
    let V := (Subtype.val : U → X) ⁻¹' W
    let F := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let R := restrict U T
    ActualNativePhase V F H R ∧ IsGeoTestTower (original V F) R ∧
    StageCentres (fun P C => ∀ c ∈ C, ∀ l,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj V)) c l = H l) R := by
  have h := p.restrictOpen hW U
  exact ⟨h,h.test,stages_HS_profile_restrict W H U T
    (actual_epoch_exact_current_centre_profile hn hW hE p)⟩

private theorem profile_eq_of_occupied {n : ℕ} {X Y : CMfd.{0} n} (W : Set X) (H K : ℕ → ℕ)
    (T : BlowupTower X Y) (hOcc : ¬ IsEmptyTower T)
    (hH : StageCentres (fun P C => ∀ c ∈ C, ∀ l,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) c l = H l) T)
    (hK : StageCentres (fun P C => ∀ c ∈ C, ∀ l,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) c l = K l) T) : H = K := by
  induction T with
  | refl => exact False.elim (hOcc trivial)
  | @step Y Z T C π hπ ih =>
    by_cases hC : C.Nonempty
    · obtain ⟨c,hc⟩ := hC
      exact funext fun l => (hH.2 c hc l).symm.trans (hK.2 c hc l)
    · exact ih (fun h => hOcc ⟨h,Set.not_nonempty_iff_eq_empty.mp hC⟩) hH.1 hK.1

/-- On a genuine empty-aware overlap comparing two actual epochs over
the same strict source and full ordered boundary, both original TEST
certificates are retained and any occupied matched centre forces equality of the
labels. Open restrictions preserve the result by applying this theorem
to the two restricted epoch certificates. -/
theorem occupied_overlap_epoch_label_and_whole_test {n : ℕ} (hn : 0 < n)
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n} {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    (W : Set X₂) (E : List (Set X₂)) (hW : IsComplexAnalyticSubset (n := n) W)
    (hE : IsSNCDivisor n E)
    (φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    {χ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (hIso : EmptyAwareTowerIso φ T₁ T₂ χ)
    {H₁ H₂ : ℕ → ℕ}
    (p₁ : ActualNativePhase (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) H₁ T₁)
    (p₂ : ActualNativePhase W E H₂ T₂) (hOcc : ¬ IsEmptyTower T₂) :
    H₁ = H₂ ∧
    StageCentres (fun P C => ∀ c ∈ C, ∀ l,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) c l = H₁ l) T₂ ∧
    IsGeoTestTower (original (φ ⁻¹' W) (E.map (φ ⁻¹' ·))) T₁ ∧
    IsGeoTestTower (original W E) T₂ := by
  have hW' := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage φ.contMDiff hW
  have hE' := (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff φ).mpr hE
  have h₁ := actual_epoch_exact_current_centre_profile hn hW' hE' p₁
  have h₂ := actual_epoch_exact_current_centre_profile hn hW hE p₂
  have hv := stages_HS_profile_of_emptyAware W hW.isClosed H₁ φ hIso h₁
  exact ⟨profile_eq_of_occupied W H₁ H₂ T₂ hOcc hv h₂,hv,p₁.test,p₂.test⟩

end
end Hironaka.HironakaG8OccupiedEpochOverlap
