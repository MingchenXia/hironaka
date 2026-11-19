import Hironaka.Resolution.HironakaG8LabelledEmbeddedAtlas
import Hironaka.Resolution.HironakaG8OriginalOverlapPrefixTransport

/-! Original invariant transport on the actual overlap of complete embedded charts. -/

set_option autoImplicit false

open Set TopologicalSpace Classical
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LabelledEmbeddedOriginalOverlap

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaStageCenters
  HironakaG3RTowerClass HironakaG3RChartOfMember HironakaG3EmptyAwareHistory
  HironakaG8LocalMixedPhaseAssembly HironakaG8LabelledEmbeddedAtlas
  HironakaG8OriginalOverlapPrefixTransport HironakaOriginalTerminalOverlapComparison MaxLocusLocal

/-- The physical comparison of complete embedded atlas charts identifies
original canonicality of the restricted full towers. Every right prefix
has an actual aligned left prefix and only the right prefix's canonicality
is needed to read its original maximum centre. -/
theorem labelled_embedded_chart_original_overlap {n : ℕ} (hn : 0 < n)
    {X Z : CMfd.{0} n} {P : Z → X} {W : Set X} {C : SmoothTailCertificate n}
    (hW : IsComplexAnalyticSubset (n := n) W) (hC : SmoothTailHasComparisons C)
    (a b : TowerChart (labelledEmbeddedClass C W) Z P) (j : ℕ) :
    let A := nestedOpens a.U (a.U ⊓ b.U)
    let B := nestedOpens b.U (a.U ⊓ b.U)
    let φ := overlapBaseEquiv (n := n) (show a.U ⊓ b.U ≤ a.U from inf_le_left)
      (show a.U ⊓ b.U ≤ b.U from inf_le_right)
    let L := restrict A a.T
    let R := restrict B b.T
    let Wl : Set A := {x | x.val.val ∈ W}
    let Wr : Set B := {x | x.val.val ∈ W}
    let Ml : MarkedIdeal n A := ⟨univ, [], vanishingIdeal (n := n) Wl, 1⟩
    let Mr : MarkedIdeal n B := ⟨univ, [], vanishingIdeal (n := n) Wr, 1⟩
    IsInvDomain n Mr →
    ∃ β : CMfd.of (n := n) (openPreimage a.T A)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage b.T B),
      EmptyAwareTowerIso φ L R β ∧
      (IsCanonical Ml ((canonicalInvariant n).inv Ml) L ↔
        IsCanonical Mr ((canonicalInvariant n).inv Mr) R) ∧
      (IsCanonical Mr ((canonicalInvariant n).inv Mr) R →
        (geoTransformAlong Ml L).cosupp = β ⁻¹' (geoTransformAlong Mr R).cosupp ∧
        maxLocus ((canonicalInvariant n).inv Ml L) (geoTransformAlong Ml L).cosupp =
          β ⁻¹' maxLocus ((canonicalInvariant n).inv Mr R) (geoTransformAlong Mr R).cosupp) ∧
    ∃ i ≤ L.length,
      ∃ η : (split L i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split R j).1,
        EmptyAwareTowerIso φ (head L i) (head R j) η ∧
        (IsCanonical Ml ((canonicalInvariant n).inv Ml) (head L i) ↔
          IsCanonical Mr ((canonicalInvariant n).inv Mr) (head R j)) ∧
        (IsCanonical Mr ((canonicalInvariant n).inv Mr) (head R j) →
          (geoTransformAlong Ml (head L i)).cosupp = η ⁻¹' (geoTransformAlong Mr (head R j)).cosupp ∧
          maxLocus ((canonicalInvariant n).inv Ml (head L i)) (geoTransformAlong Ml (head L i)).cosupp =
            η ⁻¹' maxLocus ((canonicalInvariant n).inv Mr (head R j)) (geoTransformAlong Mr (head R j)).cosupp) := by
  intro A B φ L R Wl Wr Ml Mr hMr
  obtain ⟨β, hβ⟩ := labelled_embedded_class_physical hn hC hW
    a.U b.U a.Y b.Y a.T b.T a.mem b.mem
  have hCarrier : Wl = φ ⁻¹' Wr := by
    ext x
    change x.val.val ∈ W ↔ (φ x).val.val ∈ W
    rw [overlapBaseEquiv_point]
  have hAnalytic : IsComplexAnalyticSubset (n := n) Wl :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW a.U) A
  have hFull := original_native_overlap_prefix_read hn φ Wr Wl [] [] hCarrier hAnalytic rfl L R β hβ hMr
  obtain ⟨i, hi, η, hη⟩ := exists_aligned_prefix_of_emptyAware hβ j
  have hRead := original_native_overlap_prefix_read hn φ Wr Wl [] [] hCarrier hAnalytic rfl
    (head L i) (head R j) η hη hMr
  exact ⟨β, hβ, hFull.1, hFull.2, i, hi, η, hη, hRead⟩

end Hironaka.HironakaG8LabelledEmbeddedOriginalOverlap
