import Hironaka.Resolution.HironakaG8AlignedEmptyStrictComparison
import Hironaka.Resolution.HironakaG8NestedVisibleWordLift

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FootprintAlignedRestriction
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8OccupiedSlotComparison HironakaG8NestedVisibleWordLift
  HironakaG8AlignedEmptyStrictComparison HironakaG3EmptyAwareHistory
  BlowupTowerIsomorphism HironakaG8CofinalOccupiedAncestry

variable {n : ℕ} {B F G : CMfd.{0} n}

/-- Equality of raw ordered footprints determines each local raw length
and occupancy pattern after restriction to any literal base open. -/
theorem restricted_slots_aligned_of_footprints_eq
    (S : BlowupTower B F) (T : BlowupTower B G)
    (hFoot : footprints ⟨F,S⟩ = footprints ⟨G,T⟩) (U : Opens B) :
    (restrict U S).length = (restrict U T).length ∧
      ∀ i, Occupied (restrict U S) i ↔ Occupied (restrict U T) i := by
  have hLen : S.length = T.length := by simpa [footprints] using congrArg List.length hFoot
  have hLen' : (restrict U S).length = (restrict U T).length := by
    simpa only [length_restrict] using hLen
  refine ⟨hLen',fun i => ?_⟩
  by_cases hi : i < S.length
  · have hTi := hLen ▸ hi
    have hAt := congrArg (fun l : List (Set B) => l[i]?) hFoot
    have hEqual : slotFootprint S i = slotFootprint T i := by
      simpa [footprints,hi,hTi] using hAt
    rw [← slotFootprint_nonempty_iff,← slotFootprint_nonempty_iff,
      slotFootprint_restrict,slotFootprint_restrict,hEqual]
  · have hs : ¬ Occupied (restrict U S) i := by
      intro h
      apply hi
      simpa only [length_restrict] using occupied_lt_length (restrict U S) h
    have ht : ¬ Occupied (restrict U T) i := by
      intro h
      apply hi
      simpa only [length_restrict,← hLen] using occupied_lt_length (restrict U T) h
    exact iff_of_false hs ht

/-- A literal local empty-aware comparison between equal ordered raw
footprints is strict, retaining its specified terminal map. -/
theorem strict_restriction_of_footprints_eq
    (S : BlowupTower B F) (T : BlowupTower B G)
    (hFoot : footprints ⟨F,S⟩ = footprints ⟨G,T⟩)
    (U : Opens B)
    (e : CMfd.of (n := n) (openPreimage S U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U))
    (h : EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U S) (restrict U T) e) :
    IsTowerIso (Diffeomorph.refl _ _ _) (restrict U S) (restrict U T) e :=
  let hAligned := restricted_slots_aligned_of_footprints_eq S T hFoot U
  isTowerIso_of_emptyAware_aligned h hAligned.1 hAligned.2

end Hironaka.HironakaG8FootprintAlignedRestriction
