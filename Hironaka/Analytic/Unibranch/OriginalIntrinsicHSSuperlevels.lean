import Hironaka.Analytic.Unibranch.OriginalCompactIntrinsicHSProfiles
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel
import Mathlib.Order.PiLex

/-! Literal coordinatewise ALL-order original HS thresholds in EVERY original
embedding, and the genuine analytic compact thin singular maximum stratum.
Blueprint FIRST. Existing native structural scalars and all original power
quotients are unchanged. No smooth centre, history or stopping result. -/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels

noncomputable section

open Hironaka Hironaka
  Hironaka.HolomorphicIdealSheaves
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaActualWholeAmbientHSSuperlevel
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicSingularLocus
  OriginalCompactIntrinsicHSProfiles

/-- The SAME original entire profile at every coordinate; arbitrary thresholds. -/
def originalWholeHSSuperlevel (X : SourceReducedComplexSpace) (H : ℕ → ℕ) :
    Set X.obj.left := {x | ∀ ℓ : ℕ, H ℓ ≤ originalStalkHS X x ℓ}

/-- Literal intersection with the SAME native intrinsic singular locus. -/
def originalSingularHSThreshold (X : SourceReducedComplexSpace) (H : ℕ → ℕ) :
    Set X.obj.left := intrinsicSingularLocus X.obj ∩ originalWholeHSSuperlevel X H

theorem original_hs_threshold_dictionary
    (X : SourceReducedComplexSpace) (H : ℕ → ℕ) :
    X.IsAnalyticSubset (originalWholeHSSuperlevel X H) ∧
    X.IsAnalyticSubset (originalSingularHSThreshold X H) ∧
    ∀ e : LocalEmbedding X,
      (e.toPoint ⁻¹' originalWholeHSSuperlevel X H =
        (Subtype.val : e.carrier → e.ambient) ⁻¹'
          actualWholeAmbientHSSuperlevel
            (vanishingIdeal (n := e.dim) e.carrier) H) ∧
      (e.toPoint ⁻¹' originalSingularHSThreshold X H =
        (Subtype.val : e.carrier → e.ambient) ⁻¹'
          (singularSet (n := e.dim) e.carrier ∩
            actualWholeAmbientHSSuperlevel
              (vanishingIdeal (n := e.dim) e.carrier) H)) := by
  have hWhole (e : LocalEmbedding X) :
      e.toPoint ⁻¹' originalWholeHSSuperlevel X H =
        (Subtype.val : e.carrier → e.ambient) ⁻¹'
          actualWholeAmbientHSSuperlevel
            (vanishingIdeal (n := e.dim) e.carrier) H := by
    ext c
    change (∀ ℓ, H ℓ ≤ originalStalkHS X (e.toPoint c) ℓ) ↔ _
    exact forall_congr' (fun ℓ => by rw [originalStalkHS_localEmbedding_eq X e c ℓ])
  have hSing (e : LocalEmbedding X) :
      e.toPoint ⁻¹' originalSingularHSThreshold X H =
        (Subtype.val : e.carrier → e.ambient) ⁻¹'
          (singularSet (n := e.dim) e.carrier ∩
            actualWholeAmbientHSSuperlevel
              (vanishingIdeal (n := e.dim) e.carrier) H) := by
    change e.toPoint ⁻¹' (intrinsicSingularLocus X.obj ∩
      originalWholeHSSuperlevel X H) = _
    rw [preimage_inter, intrinsicSingularLocus_localEmbedding_preimage X e, hWhole]
    rfl
  have hAmbient (e : LocalEmbedding X) :
      IsComplexAnalyticSubset (n := e.dim)
        (actualWholeAmbientHSSuperlevel
          (vanishingIdeal (n := e.dim) e.carrier) H) :=
    isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
      (CartanIrreducible.cartanCoherence e.carrier e.analytic) H
  refine ⟨?_, ?_, fun e => ⟨hWhole e, hSing e⟩⟩
  · intro x
    let e := LocalEmbedding.ofPoint X x
    exact ⟨e, LocalEmbedding.mem_range_ofPoint X x, _, hAmbient e, hWhole e⟩
  · intro x
    let e := LocalEmbedding.ofPoint X x
    exact ⟨e, LocalEmbedding.mem_range_ofPoint X x, _,
      (HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet e.analytic).inter
        (hAmbient e), hSing e⟩

theorem exists_original_compact_singular_hs_maximal_stratum
    (X : SourceReducedComplexSpace) [CompactSpace X.obj.left]
    (hns : ¬ X.IsSmooth) :
    ∃ a ∈ intrinsicSingularLocus X.obj,
      let H := originalStalkHS X a
      let D := originalSingularHSThreshold X H
      (∀ x ∈ intrinsicSingularLocus X.obj,
        toLex (originalStalkHS X x) ≤ toLex H) ∧
      D = {x | x ∈ intrinsicSingularLocus X.obj ∧ originalStalkHS X x = H} ∧
      a ∈ D ∧ D.Nonempty ∧ X.IsAnalyticSubset D ∧
      IsCompact D ∧ interior D = ∅ := by
  obtain ⟨a, ha, hMax⟩ := exists_original_compact_singular_hs_lex_maximum X hns
  let H := originalStalkHS X a
  let D := originalSingularHSThreshold X H
  have haD : a ∈ D := ⟨ha, fun _ => le_rfl⟩
  have hEq : D = {x | x ∈ intrinsicSingularLocus X.obj ∧ originalStalkHS X x = H} := by
    ext x
    constructor
    · rintro ⟨hx, hThreshold⟩
      exact ⟨hx, congrArg ofLex (le_antisymm (hMax x hx)
        (Pi.toLex_monotone hThreshold))⟩
    · rintro ⟨hx, heq⟩
      exact ⟨hx, fun ℓ => (congrFun heq ℓ).ge⟩
  have hAnalytic : X.IsAnalyticSubset D := (original_hs_threshold_dictionary X H).2.1
  refine ⟨a, ha, hMax, hEq, haD, ⟨a, haD⟩, hAnalytic, hAnalytic.isClosed.isCompact, ?_⟩
  apply Set.eq_empty_of_subset_empty
  intro x hx
  have hs := interior_mono (show D ⊆ intrinsicSingularLocus X.obj from inter_subset_left) hx
  rw [interior_intrinsicSingularLocus_eq_empty X] at hs
  exact hs

end
end Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels
