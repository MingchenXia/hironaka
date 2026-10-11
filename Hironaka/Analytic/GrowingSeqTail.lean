/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionCentreCounting
import Hironaka.Invariant.TowerRestrictionStep

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.ResolutionInvariantSeq.GrowingSeq
open Hironaka BlowupSequences BlowupTowers BlowupTowerTransforms TowerPreimageCompact ResolutionInvariantSpec
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

/-- **The restriction of a growing sequence to an open set `U` of the base**: the `i`-th tower is the restriction of the
`i`-th tower (`BlowupTowerTransforms.restrict`); it is again a growing sequence. -/
def restrict (s : GrowingSeq X) (U : Opens X) : GrowingSeq (CMfd.of (n := n) U) where
  stage i := ⟨CMfd.of (n := n) (openPreimage (s.stage i).2 U), BlowupTowerTransforms.restrict U (s.stage i).2⟩
  zero := by
    rw [s.zero]
    rfl
  succ i := by
    obtain ⟨C, π, hπ, heq⟩ := s.succ i
    show ∃ (C' : Set (openPreimage (s.stage i).2 U))
      (π' : openPreimage (s.stage (i + 1)).2 U → openPreimage (s.stage i).2 U)
      (hπ' : IsBlowupAlong n C' π'),
      BlowupTowerTransforms.restrict U (s.stage (i + 1)).2 =
        .step (BlowupTowerTransforms.restrict U (s.stage i).2) C' π' hπ'
    rw [heq]
    obtain ⟨π', hπ', h⟩ := exists_restrict_step U (s.stage i).2 C π hπ
    exact ⟨_, π', hπ', h⟩

theorem restrict_stage (s : GrowingSeq X) (U : Opens X) (i : ℕ) :
    (s.restrict U).stage i =
      ⟨CMfd.of (n := n) (openPreimage (s.stage i).2 U), BlowupTowerTransforms.restrict U (s.stage i).2⟩ := rfl

/-- **The counts along the restricted sequence** of a subset `K ⊆ U` are those along the sequence
(`ResolutionInvariantSegments.countCentresMeeting_restrict_of_subset`). -/
theorem count_restrict (s : GrowingSeq X) (U : Opens X) {K : Set X} (hKU : K ⊆ U) (i : ℕ) :
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) ((s.restrict U).stage i).2 =
      countCentresMeeting K (s.stage i).2 :=
  ResolutionInvariantSegments.countCentresMeeting_restrict_of_subset U hKU (s.stage i).2


/-- **Counts never decrease along a growing sequence.** -/
theorem count_mono (s : GrowingSeq X) (K : Set X) {i j : ℕ} (hij : i ≤ j) :
    countCentresMeeting K (s.stage i).2 ≤ countCentresMeeting K (s.stage j).2 := by
  induction hij with
  | refl => exact le_rfl
  | @step j _ ih =>
      obtain ⟨C, π, hπ, heq⟩ := s.succ j
      rw [heq]
      exact ih.trans (Nat.le_add_right _ _)


end
end Hironaka.ResolutionInvariantSeq.GrowingSeq
