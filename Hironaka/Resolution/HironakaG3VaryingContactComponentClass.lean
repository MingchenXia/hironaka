import Hironaka.Resolution.HironakaG3BoundaryDivisorBoundProducers
import Hironaka.Resolution.HironakaG3IndexedBoundaryWindowSupport
import Hironaka.Resolution.HironakaG3TowerCentresGood
import Hironaka.Resolution.HironakaG3IndexedContainedOriginalGood
import Hironaka.Resolution.HironakaG3SeparatedAvoidingGood
import Hironaka.Resolution.HironakaG3PhysicalClassComparisons
import Hironaka.Resolution.HironakaG3AvoidingLocalResolvedGeometry
import Hironaka.Resolution.HironakaG3ResidualLocalResolvedGeometry
import Hironaka.Resolution.HironakaG3TopContactBiholoEmptyClass
import Hironaka.Resolution.HironakaG3IndexedProperContactWindow
import Hironaka.Resolution.HironakaG3AvoidingSortedWindowGeometry
import Hironaka.Resolution.HironakaG3ResidualSortedWindowGeometry
import Hironaka.Resolution.HironakaG3TopReflSortedWindowGeometry
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingContactComponentClass
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3IndexedAvoidingCentresOver
  HironakaG3IndexedResidualFixedHeadClass HironakaG3IndexedProperContactWindow
  HironakaG3AvoidingLocalResolvedGeometry HironakaG3ResidualLocalResolvedGeometry
  HironakaG3TopContactBiholoEmptyClass HironakaG3TopContactEmptyClass HironakaG3PhysicalClassComparisons HironakaG3AllEmptyComparison
  HironakaG3DisjointLocalTowerAtlas HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower
  HironakaG3TowerCentresGood HironakaG3IndexedContainedOriginalGood HironakaG3SeparatedAvoidingGood
  HironakaG3SortedLocalWindowGeometry HironakaG3AvoidingSortedWindowGeometry
  HironakaG3ResidualSortedWindowGeometry HironakaG3TopReflSortedWindowGeometry
  HironakaG3BoundaryDivisorBoundClass HironakaG3BoundaryDivisorBoundProducers
  HironakaG3IndexedBoundaryWindowSupport

/-- The chosen component class records the actual avoiding, native proper
contact, or top-contact identity construction. -/
inductive ActualComponentResolutionClass {κ : Type*} [LinearOrder κ] (r : ℕ) :
    {n : ℕ} → {X : CMfd.{0} n} → (C : Set X) → (D : κ → Set X) →
    IsComplexAnalyticallyIrreducible (n := n) C → IsLocallyFiniteSNCDivisor n D →
    LocalTowerClass X → Prop where
  | avoiding {n : ℕ} {X : CMfd.{0} n} {C : Set X} {D : κ → Set X}
      {hC : IsComplexAnalyticallyIrreducible (n := n) C} {hD : IsLocallyFiniteSNCDivisor n D}
      (hS : containingLabels C D hC.nonempty hD.1 = ∅) :
      ActualComponentResolutionClass r C D hC hD (indexedAvoidingBoundaryClass C r D)
  | properContact {d t : ℕ} {X : CMfd.{0} (d+t)} {C : Set X} {D : κ → Set X}
      {hC : IsComplexAnalyticallyIrreducible (n := d+t) C} {hD : IsLocallyFiniteSNCDivisor (d+t) D}
      (ht : 0 < t) (hr : r < d)
      (hCard : (containingLabels C D hC.nonempty hD.1).card = t)
      (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
      (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
        RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d) :
      ActualComponentResolutionClass r C D hC hD
        (residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
          (containingLabels C D hC.nonempty hD.1))
  | topContact {n : ℕ} {X : CMfd.{0} n} {C : Set X} {D : κ → Set X}
      {hC : IsComplexAnalyticallyIrreducible (n := n) C} {hD : IsLocallyFiniteSNCDivisor n D}
      (ht : 0 < (containingLabels C D hC.nonempty hD.1).card)
      (htop : n - (containingLabels C D hC.nonempty hD.1).card ≤ r) :
      ActualComponentResolutionClass r C D hC hD (topReflClass (X := X))

theorem exists_actual_component_resolution_class_with_provenance {n r t : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (C : Set X) (D : κ → Set X) (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hCard : (containingLabels C D hC.nonempty hD.1).card = t)
    (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    ∃ K : LocalTowerClass X, ActualComponentResolutionClass r C D hC hD K ∧
      HasPhysicalComparisons K ∧ HasComparisons K ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C) T) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
          (if t = 0 ∨ r < n - t then C else ∅)) T) ∧
      HasBoundaryDivisorBound D K ∧
      HasSortedLocalWindowGeometry C D K ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T →
        T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C ∧
        ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C),
          RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C)) y r) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → IsIsomorphismOver n T.proj
          ((Subtype.val : U → X) ⁻¹' (C \ regularLocus (n := n) C r ∪ C ∩ ⋃ j, D j)ᶜ)) ∧
      (∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K U Y T) := by
  by_cases ht0 : t = 0
  · have hS : containingLabels C D hC.nonempty hD.1 = ∅ := Finset.card_eq_zero.mp (hCard.trans ht0)
    refine ⟨indexedAvoidingBoundaryClass C r D, .avoiding hS, indexed_avoiding_boundary_physical_overlap C D hC hD hS hr hpure,
      indexed_avoiding_boundary_comparisons C D hC hD hS hr hpure,?_,?_,
      avoiding_class_has_boundary_divisor_bound C D hC hD hS hr hpure,
      indexed_avoiding_sorted_local_window_geometry C D hC hD hS hr hpure,?_,?_,?_⟩
    · intro U Y T hT
      exact indexed_avoiding_centres_over C D hC.analytic hD hr hpure U Y T hT
    · intro U Y T hT
      simpa [ht0] using indexed_avoiding_centres_over C D hC.analytic hD hr hpure U Y T hT
    · intro U Y T hT
      exact indexed_avoiding_member_resolved_geometry C D hC hD hS hr hpure U T hT
    · intro U Y T hT
      exact indexed_avoiding_member_original_good C r D hC hD hS hr hpure U T hT
    · intro U L hL hUL
      exact indexed_avoiding_boundary_member_over_compact_window C D hC hD hr hpure U L hL hUL
  · have ht : 0 < t := Nat.pos_of_ne_zero ht0
    by_cases hStrict : r < n - t
    · have htn : t ≤ n := by
        have hh := (canonicalContact_geometry C D hC hD).2.2.2.2.1
        simpa only [hCard] using hh
      obtain ⟨d,hdn⟩ := Nat.exists_eq_add_of_le htn
      have hn : n = d+t := by omega
      clear hdn
      subst n
      have hd : 0 < d := by omega
      have hr' : r < d := by omega
      have hNc : IsClosed (canonicalContact C D hC.nonempty hD.1) :=
        (canonicalContact_geometry C D hC hD).2.2.1
      have hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
          RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d := by
        have hh := (canonicalContact_geometry C D hC hD).2.2.2.1
        have heq : d+t - (containingLabels C D hC.nonempty hD.1).card = d := by rw [hCard]; omega
        simpa only [heq] using hh
      refine ⟨residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
        (containingLabels C D hC.nonempty hD.1), .properContact ht hr' hCard hNc hN,
        canonical_residualFixedHead_physical_overlap hd C D hC hD hr' hpure hNc hN,
        canonical_residualFixedHead_comparisons hd C D hC hD hr' hpure hNc hN,?_,?_,?_,
        indexed_residual_sorted_local_window_geometry hd ht C D hC hD hr' hpure hNc hN,?_,?_,?_⟩
      · intro U Y T hT
        obtain ⟨R,_hDis,_hVis,hHead⟩ := hT
        exact HironakaG3FixedHeadTargetFootprint.fixed_head_centres_over_target _ hNc hN
          ((R.sort (· ≤ ·)).map D) C hC.analytic r U Y T hHead
      · intro U Y T hT
        obtain ⟨R,_hDis,_hVis,hHead⟩ := hT
        have hOver := HironakaG3FixedHeadTargetFootprint.fixed_head_centres_over_target _ hNc hN
          ((R.sort (· ≤ ·)).map D) C hC.analytic r U Y T hHead
        simpa [ht0,hr'] using hOver
      · have hpos : 0 < (containingLabels C D hC.nonempty hD.1).card := by rw [hCard]; exact ht
        apply class_has_boundary_divisor_bound_of_centres D _ C
          (positive_containing_labels_target_subset C D hC.nonempty hD.1 hpos)
        intro U Y T hT
        obtain ⟨R,_hDis,_hVis,hHead⟩ := hT
        exact HironakaG3FixedHeadTargetFootprint.fixed_head_centres_over_target _ hNc hN
          ((R.sort (· ≤ ·)).map D) C hC.analytic r U Y T hHead
      · intro U Y T hT
        exact indexed_residual_member_resolved_geometry hd ht C D hC hD hr' hpure hNc hN U T hT
      · intro U Y T hT
        obtain ⟨R,_hDis,_hVis,hHead⟩ := hT
        have hOver := HironakaG3FixedHeadTargetFootprint.fixed_head_centres_over_target _ hNc hN
          ((R.sort (· ≤ ·)).map D) C hC.analytic r U Y T hHead
        have hIso := tower_isomorphism_off_closed_footprint ((Subtype.val : U → X) ⁻¹' C)
          (hC.analytic.isClosed.preimage continuous_subtype_val) T hOver
        have hpos : 0 < (containingLabels C D hC.nonempty hD.1).card := by rw [hCard]; exact ht
        rw [indexed_original_bad_eq_target_of_positive_containing_count C D hC.nonempty hD.1 r hpos,preimage_compl]
        exact hIso
      · intro U L hL hUL
        obtain ⟨_hNc',_hN',R,Y,T,hDis,hVis,hHead⟩ :=
          indexed_proper_contact_head_over_compact_window hd ht C D hC hD hCard hr' hpure U L hL hUL
        exact ⟨Y,T,R,hDis,hVis,hHead⟩
    · have htop : n - (containingLabels C D hC.nonempty hD.1).card ≤ r := by rw [hCard]; omega
      obtain ⟨_hCmp,_hMem,hOver,hGeo,hNC⟩ := top_contact_biholo_empty_class_data C D hC hD hpure htop
      have hPhys : HasPhysicalComparisons (topReflClass (X := X)) := by
        intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
        exact exists_comparison_of_restricted_histories_avoiding_opens
          (nestedOpens U₁ (U₁ ⊓ U₂)) (nestedOpens U₂ (U₁ ⊓ U₂))
          (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) T₁ T₂
          (empty_avoids _ T₁ h₁.1.1) (empty_avoids _ T₂ h₂.1.1)
      have hGood : ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
          topReflClass U Y T → IsIsomorphismOver n T.proj
            ((Subtype.val : U → X) ⁻¹' (C \ regularLocus (n := n) C r ∪ C ∩ ⋃ j, D j)ᶜ) := by
        intro U Y T hT
        have hOver0 := empty_tower_class_centres_over (∅ : Set X) U Y T hT.1.1
        have hIso := tower_isomorphism_off_closed_footprint (∅ : Set (CMfd.of (n := n) U)) isClosed_empty T (by simpa using hOver0)
        apply iso_mono _ hIso
        simp
      have hActiveOver : ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
          topReflClass U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
            (if t = 0 ∨ r < n - t then C else ∅)) T := by
        intro U Y T hT
        simpa [ht0,hStrict] using empty_tower_class_centres_over (∅ : Set X) U Y T hT.1.1
      have hPositive : 0 < (containingLabels C D hC.nonempty hD.1).card := hCard.symm ▸ ht
      refine ⟨topReflClass,.topContact hPositive htop,hPhys,top_refl_class_comparisons,?_,hActiveOver,?_,
        top_refl_sorted_local_window_geometry C D hC.analytic.isClosed hD hNC,?_,hGood,?_⟩
      · intro U Y T hT
        exact hOver U Y T hT.1
      · apply class_has_boundary_divisor_bound_of_centres D _ ∅ (empty_subset _)
        intro U Y T hT
        exact empty_tower_class_centres_over (∅ : Set X) U Y T hT.1.1
      · intro U Y T hT
        exact hGeo U Y T hT.1
      · intro U _ _ _
        exact top_refl_class_member U

theorem exists_actual_component_resolution_class {n r t : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (C : Set X) (D : κ → Set X) (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hCard : (containingLabels C D hC.nonempty hD.1).card = t)
    (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    ∃ K : LocalTowerClass X, HasPhysicalComparisons K ∧ HasComparisons K ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C) T) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
          (if t = 0 ∨ r < n - t then C else ∅)) T) ∧
      HasBoundaryDivisorBound D K ∧
      HasSortedLocalWindowGeometry C D K ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T →
        T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C ∧
        ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C),
          RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C)) y r) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → IsIsomorphismOver n T.proj
          ((Subtype.val : U → X) ⁻¹' (C \ regularLocus (n := n) C r ∪ C ∩ ⋃ j, D j)ᶜ)) ∧
      (∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K U Y T) := by
  obtain ⟨K,_hKind,hRest⟩ :=
    exists_actual_component_resolution_class_with_provenance C D hC hD hCard hr hpure
  exact ⟨K,hRest⟩

end
end Hironaka.HironakaG3VaryingContactComponentClass
