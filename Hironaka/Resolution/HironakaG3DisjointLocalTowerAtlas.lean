import Hironaka.Resolution.HironakaG3AllEmptyComparison
import Hironaka.Resolution.HironakaG3RTowerClass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointLocalTowerAtlas
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3AllEmptyComparison HironakaG3EmptyAwareHistory
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

/-- Each local chart either belongs to one isolated component class or is empty off all components. -/
def disjointWindowClass {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) : LocalTowerClass X :=
  fun U Y T => (∃ i, U ≤ W i ∧ K i U Y T) ∨ ((U : Set X) ⊆ (⋃ i, A i)ᶜ ∧ IsEmptyTower T)

theorem empty_avoids {n : ℕ} {X Y : CMfd.{0} n} (U : Opens X) (T : BlowupTower X Y)
    (hT : IsEmptyTower T) : CentresAvoid U T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    exact ⟨ih hT.1, by rw [hT.2]; exact Set.empty_disjoint _⟩

theorem avoiding_overlap_comparison {n : ℕ} {X : CMfd.{0} n} (U₁ U₂ : Opens X)
    {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : CentresAvoid (nestedOpens U₁ (U₁ ⊓ U₂)) T₁)
    (h₂ : CentresAvoid (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) :
    ∃ η : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      ∀ y, ((T₂.proj (η y).val : U₂) : X) = ((T₁.proj y.val : U₁) : X) := by
  obtain ⟨β,hβ⟩ := exists_comparison_of_restricted_histories_avoiding_opens
    (nestedOpens U₁ (U₁ ⊓ U₂)) (nestedOpens U₂ (U₁ ⊓ U₂))
    (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) T₁ T₂ h₁ h₂
  refine ⟨β,?_⟩
  intro y
  have hz := congrArg (fun q : nestedOpens U₂ (U₁ ⊓ U₂) => q.val.val) (emptyAware_proj_comm hβ y)
  rw [overlapBaseEquiv_point] at hz
  have htproj := congrArg (fun q : U₂ => q.val) (proj_restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂ (β y))
  have hsproj := congrArg (fun q : U₁ => q.val) (proj_restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁ y)
  exact htproj.symm.trans (hz.trans hsproj)

/-- Distinct isolated component classes have actual comparisons by empty restrictions. -/
theorem disjoint_window_comparisons {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T) :
    HasComparisons (disjointWindowClass A W K) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ hm₁ hm₂
  rcases hm₁ with ⟨i,hi,hm₁⟩ | ⟨hi,hm₁⟩ <;> rcases hm₂ with ⟨j,hj,hm₂⟩ | ⟨hj,hm₂⟩
  · by_cases hij : i = j
    · subst j
      exact hCompare i U₁ U₂ Y₁ Y₂ T₁ T₂ hm₁ hm₂
    · apply avoiding_overlap_comparison U₁ U₂ T₁ T₂
      · apply centresAvoid_of_centresOver _ _ T₁ (hCentres i U₁ Y₁ T₁ hm₁)
        apply Set.disjoint_left.mpr
        intro x hx hxA
        exact Set.disjoint_left.mp (hWindow j i (Ne.symm hij)) hxA (hj hx.2)
      · apply centresAvoid_of_centresOver _ _ T₂ (hCentres j U₂ Y₂ T₂ hm₂)
        apply Set.disjoint_left.mpr
        intro x hx hxA
        exact Set.disjoint_left.mp (hWindow i j hij) hxA (hi hx.1)
  · apply avoiding_overlap_comparison U₁ U₂ T₁ T₂
    · apply centresAvoid_of_centresOver _ _ T₁ (hCentres i U₁ Y₁ T₁ hm₁)
      apply Set.disjoint_left.mpr
      intro x hx hxA
      exact (hj hx.2) (mem_iUnion.mpr ⟨i,hxA⟩)
    · exact empty_avoids _ T₂ hm₂
  · apply avoiding_overlap_comparison U₁ U₂ T₁ T₂
    · exact empty_avoids _ T₁ hm₁
    · apply centresAvoid_of_centresOver _ _ T₂ (hCentres j U₂ Y₂ T₂ hm₂)
      apply Set.disjoint_left.mpr
      intro x hx hxA
      exact (hi hx.1) (mem_iUnion.mpr ⟨j,hxA⟩)
  · exact avoiding_overlap_comparison U₁ U₂ T₁ T₂ (empty_avoids _ T₁ hm₁) (empty_avoids _ T₂ hm₂)

/-- Local components and their complement cover; the resulting native map is genuinely glued. -/
theorem exists_glued_disjoint_window_atlas {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (hLocal : ∀ i x, x ∈ A i → ∃ U : Opens X, x ∈ U ∧ U ≤ W i ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (disjointWindowClass A W K) Z P := by
  have hCov : Covers (disjointWindowClass A W K) := by
    intro x
    by_cases hx : x ∈ ⋃ i, A i
    · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      obtain ⟨U,hxU,hUW,Y,T,hT⟩ := hLocal i x hxi
      exact ⟨U,hxU,Y,T,Or.inl ⟨i,hUW,hT⟩⟩
    · let U : Opens X := ⟨(⋃ i, A i)ᶜ,(hLF.isClosed_iUnion hClosed).isOpen_compl⟩
      exact ⟨U,hx,CMfd.of (n := n) U,.refl,Or.inr ⟨Subset.rfl,trivial⟩⟩
  exact exists_isGluedFrom hCov (disjoint_window_comparisons A W K hWindow hCompare hCentres)
end
end Hironaka.HironakaG3DisjointLocalTowerAtlas
