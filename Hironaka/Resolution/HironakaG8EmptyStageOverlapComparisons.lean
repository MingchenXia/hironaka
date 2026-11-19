import Hironaka.Resolution.HironakaG8DisjointClockAtlas
import Hironaka.Resolution.HironakaG8FirstFootprintOrder

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8EmptyStageOverlapComparisons

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  ResolutionInvariantExt BlowupTowerSplit
  HironakaG8RankedGlobalTest HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveEmptyPadding MaxLocusLocal
  HironakaNormalCrossingsSeparationChoiceComparison

variable {n : ℕ}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Equal-length empty-centre towers compare strictly over any fixed base
biholomorphism, including on a nonempty base. -/
theorem strict_comparison_of_empty_towers {A B Y Z : CMfd.{0} n}
    (f : A ≃ₘ⟮𝓘c,𝓘c⟯ B) (S : BlowupTower A Y) (T : BlowupTower B Z)
    (hs : IsEmptyTower S) (ht : IsEmptyTower T) (hLen : S.length = T.length) :
    ∃ e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z, IsTowerIso f S T e := by
  induction S generalizing Z with
  | refl =>
    cases T with
    | refl => exact ⟨f,.refl⟩
    | step => simp [BlowupTower.length_step] at hLen
  | @step C Y S H π hπ ih =>
    cases T with
    | refl => simp [BlowupTower.length_step] at hLen
    | @step D Z T J ρ hρ =>
      obtain ⟨g,hg⟩ := ih T hs.1 ht.1 (Nat.succ.inj hLen)
      have hCentre : g ⁻¹' J = H := by rw [ht.2,hs.2,preimage_empty]
      obtain ⟨e,he,_⟩ := exists_unique_lift g hπ hρ hCentre
      exact ⟨e,.step hg hπ hρ e he hCentre⟩

/-- A tower is empty once every literal raw slot has empty source footprint. -/
theorem isEmptyTower_of_empty_footprints {A Y : CMfd.{0} n}
    (T : BlowupTower A Y) (h : ∀ k, slotFootprint T k = ∅) : IsEmptyTower T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    refine ⟨ih (fun k => ?_),?_⟩
    · by_cases hk : k = T.length
      · subst k
        apply not_nonempty_iff_eq_empty.mp
        intro hOcc
        exact (Nat.lt_irrefl _) (occupied_lt_length T ((slotFootprint_nonempty_iff T _).mp hOcc))
      · simpa [slotFootprint,hk] using h k
    · have hLast := h T.length
      simpa [slotFootprint] using hLast

/-- A pair of local towers compares strictly when all of their footprints
avoid the other tower's base. Each tower is padded to the common maximum. -/
theorem strict_comparison_of_empty_stage_overlap {X A B : CMfd.{0} n}
    (U V : Opens X)
    (S : BlowupTower (CMfd.of (n := n) U) A) (T : BlowupTower (CMfd.of (n := n) V) B)
    (hS : ∀ k, Disjoint (slotFootprint S k) ((Subtype.val : U → X) ⁻¹' (V : Set X)))
    (hT : ∀ k, Disjoint (slotFootprint T k) ((Subtype.val : V → X) ⁻¹' (U : Set X))) :
    ∃ e : localEndpoint U (U ⊓ V) .refl S ≃ₘ⟮𝓘c,𝓘c⟯ localEndpoint V (U ⊓ V) .refl T,
      IsTowerIso (commonOpenBase U V (U ⊓ V) inf_le_left inf_le_right)
        (localPaddedHistory U (U ⊓ V) .refl S (max S.length T.length))
        (localPaddedHistory V (U ⊓ V) .refl T (max S.length T.length)) e := by
  apply strict_comparison_of_empty_towers
  · simp only [localPaddedHistory,paddedHistory,isEmptyTower_append_iff]
    refine ⟨trivial,?_,identityEmptyTail_isEmptyTower _ _⟩
    apply isEmptyTower_of_empty_footprints
    intro k
    rw [slotFootprint_restrict]
    exact Set.eq_empty_of_forall_notMem fun x hx =>
      Set.disjoint_left.mp (hS k) hx x.property.2
  · simp only [localPaddedHistory,paddedHistory,isEmptyTower_append_iff]
    refine ⟨trivial,?_,identityEmptyTail_isEmptyTower _ _⟩
    apply isEmptyTower_of_empty_footprints
    intro k
    rw [slotFootprint_restrict]
    exact Set.eq_empty_of_forall_notMem fun x hx =>
      Set.disjoint_left.mp (hT k) hx x.property.1
  · simp only [localPaddedHistory,paddedHistory,BlowupTower.length_append,length_restrict,
      BlowupTower.length_refl,zero_add,identityEmptyTail_length]
    omega

/-- There is no bound on the individual chart lengths. Each pair is padded
only to its own maximum. Off the diagonal it suffices that every original
footprint on either chart misses the other chart. -/
theorem strictPairwiseComparisons_of_empty_stage_overlaps {I : Type} {X : CMfd.{0} n}
    (U : I → Opens X) {Y : I → CMfd.{0} n}
    (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (hAvoid : ∀ ⦃i j⦄, i ≠ j → ∀ k,
      Disjoint (slotFootprint (T i) k) ((Subtype.val : U i → X) ⁻¹' (U j : Set X))) :
    StrictPairwiseComparisons U T := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    let O := U i ⊓ U i
    let S := localPaddedHistory (U i) O .refl (T i) (max (T i).length (T i).length)
    refine ⟨Diffeomorph.refl 𝓘c (localEndpoint (U i) O .refl (T i)) ∞,?_⟩
    apply BlowupTowerSplitIso.IsTowerIso.congr_base (IsTowerIso.refl_self S)
    intro x
    rfl
  · exact strict_comparison_of_empty_stage_overlap (U i) (U j) (T i) (T j)
      (hAvoid hij) (hAvoid (Ne.symm hij))

#print axioms strictPairwiseComparisons_of_empty_stage_overlaps

end Hironaka.HironakaG8EmptyStageOverlapComparisons
