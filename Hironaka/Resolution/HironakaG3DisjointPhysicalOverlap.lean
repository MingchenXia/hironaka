import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointPhysicalOverlap
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3AllEmptyComparison HironakaG3EmptyAwareHistory
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower

/-- Same-component physical comparisons and actual centre footprints yield
physical comparisons for the entire disjoint class. -/
theorem disjoint_physical_overlap {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hSame : ∀ (i : ι) (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{0} n)
      (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂),
      K i U₁ Y₁ T₁ → K i U₂ Y₂ T₂ →
      ∃ β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
        EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
          (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{0} n)
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : disjointWindowClass A W K U₁ Y₁ T₁) (h₂ : disjointWindowClass A W K U₂ Y₂ T₂) :
    ∃ β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β := by
  have hEmptyPair (hA : CentresAvoid (nestedOpens U₁ (U₁ ⊓ U₂)) T₁)
      (hB : CentresAvoid (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) :=
    exists_comparison_of_restricted_histories_avoiding_opens
      (nestedOpens U₁ (U₁ ⊓ U₂)) (nestedOpens U₂ (U₁ ⊓ U₂))
      (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) T₁ T₂ hA hB
  rcases h₁ with ⟨i,hi,hm₁⟩ | ⟨hi,hm₁⟩ <;> rcases h₂ with ⟨j,hj,hm₂⟩ | ⟨hj,hm₂⟩
  · by_cases hij : i = j
    · subst j
      exact hSame i U₁ U₂ Y₁ Y₂ T₁ T₂ hm₁ hm₂
    · refine hEmptyPair ?_ ?_
      · apply centresAvoid_of_centresOver _ _ T₁ (hCentres i U₁ Y₁ T₁ hm₁)
        apply Set.disjoint_left.mpr
        intro x hx hxA
        exact Set.disjoint_left.mp (hWindow j i (Ne.symm hij)) hxA (hj hx.2)
      · apply centresAvoid_of_centresOver _ _ T₂ (hCentres j U₂ Y₂ T₂ hm₂)
        apply Set.disjoint_left.mpr
        intro x hx hxA
        exact Set.disjoint_left.mp (hWindow i j hij) hxA (hi hx.1)
  · refine hEmptyPair ?_ ?_
    · apply centresAvoid_of_centresOver _ _ T₁ (hCentres i U₁ Y₁ T₁ hm₁)
      apply Set.disjoint_left.mpr
      intro x hx hxA
      exact (hj hx.2) (mem_iUnion.mpr ⟨i,hxA⟩)
    · exact empty_avoids _ T₂ hm₂
  · refine hEmptyPair ?_ ?_
    · exact empty_avoids _ T₁ hm₁
    · apply centresAvoid_of_centresOver _ _ T₂ (hCentres j U₂ Y₂ T₂ hm₂)
      apply Set.disjoint_left.mpr
      intro x hx hxA
      exact (hi hx.1) (mem_iUnion.mpr ⟨j,hxA⟩)
  · exact hEmptyPair (empty_avoids _ T₁ hm₁) (empty_avoids _ T₂ hm₂)
end
end Hironaka.HironakaG3DisjointPhysicalOverlap
