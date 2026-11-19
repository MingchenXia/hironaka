import Hironaka.Resolution.HironakaCountableTowerPrefixes
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence

/-!
# Local finiteness from actual finite-block centre counts

The sequence need not be globally canonical for an invariant. Compact-set
count bounds imply local finiteness of the same native actual centre images.
For a sequence read from finite blocks, only boundary counts need checking.
The geometric construction of resolving blocks remains a separate obligation.

Blueprint: `hironaka-exhaustion-block-local-finiteness.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaExhaustionBlockLocalFiniteness

open BlowupTowers ResolutionInvariantSeq
  HironakaCountableTowerPrefixes HironakaLocallyFiniteResolutionSequence
open ResolutionInvariantSpec (countCentresMeeting)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Bounded actual counts force every later actual centre image to miss the set. -/
theorem exists_no_later_centres_of_count_bound (s : GrowingSeq X) (K : Set X)
    {m : ℕ} (hm : ∀ i, countCentresMeeting K (s.stage i).2 ≤ m) :
    ∃ N, ∀ i, N ≤ i → ¬ (centreImage s i ∩ K).Nonempty := by
  classical
  let f : ℕ → ℕ := fun i => countCentresMeeting K (s.stage i).2
  have hfin : (range f).Finite := (finite_Iic m).subset (by
    rintro _ ⟨i, rfl⟩
    exact hm i)
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ :=
    Set.exists_max_image (range f) id hfin ⟨f 0, mem_range_self 0⟩
  have hconstant (i : ℕ) (hi : N ≤ i) : f i = f N :=
    le_antisymm (hmax (f i) (mem_range_self i)) (monotone_countCentresMeeting s K hi)
  refine ⟨N, fun i hi hhit => ?_⟩
  have hcur := hconstant i hi
  have hnext := hconstant (i + 1) (by omega)
  change countCentresMeeting K (s.stage (i + 1)).2 = f N at hnext
  rw [countCentresMeeting_step, if_pos hhit] at hnext
  change countCentresMeeting K (s.stage i).2 = f N at hcur
  omega

/-- Bounds on an actual open cover suffice, with no global invariant or compactness. -/
theorem locallyFinite_of_open_cover_count_bounds {ι : Type*}
    (s : GrowingSeq X) (U : ι → Opens X) (hcover : ∀ x : X, ∃ a, x ∈ U a)
    (hbound : ∀ a, ∃ m, ∀ i, countCentresMeeting (U a : Set X) (s.stage i).2 ≤ m) :
    LocallyFinite (centreImage s) := by
  intro x
  obtain ⟨a, ha⟩ := hcover x
  obtain ⟨m, hm⟩ := hbound a
  obtain ⟨N, hN⟩ := exists_no_later_centres_of_count_bound s (U a) hm
  refine ⟨U a, (U a).isOpen.mem_nhds ha, (finite_Iio N).subset ?_⟩
  intro i hi
  exact lt_of_not_ge (fun hge => hN i hge hi)

/-- Any bounded count gives whole genuinely empty restricted tails over an open. -/
theorem exists_empty_tails_of_open_count_bound (s : GrowingSeq X) (U : Opens X)
    {m : ℕ} (hm : ∀ i, countCentresMeeting (U : Set X) (s.stage i).2 ≤ m) :
    ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
      (BlowupTowerTransforms.restrict
        (BlowupTowerTransforms.openPreimage (s.stage N).2 U) (tailTower s N r)) := by
  obtain ⟨N, hN⟩ := exists_no_later_centres_of_count_bound s U hm
  have hdisj : ∀ i, N ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)) := by
    intro i hi
    apply disjoint_left.mpr
    intro z hzC hzU
    exact hN i hi ⟨(s.stage i).2.proj z, ⟨z, hzC, rfl⟩, hzU⟩
  exact ⟨N, fun r => (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
    (centresAvoid_tailTower s N U hdisj r)⟩

section Blocks

variable (B : ℕ → Σ Y : CMfd.{u} n, BlowupTower X Y)
  (hB : ∀ j, ∃ Q : BlowupTower (B j).1 (B (j + 1)).1,
    (B (j + 1)).2 = (B j).2.append Q)
  (hUnbounded : ∀ i, ∃ j, i ≤ (B j).2.length)
  {ι : Type*} (U : ι → Opens X)
  (hbound : ∀ a, ∃ m, ∀ j, countCentresMeeting (U a : Set X) (B j).2 ≤ m)

include hbound

/-- Only finite-block boundary counts are needed to prove actual centre local finiteness. -/
theorem locallyFinite_sequenceOfBlocks (hcover : ∀ x : X, ∃ a, x ∈ U a) :
    LocallyFinite (centreImage (sequenceOfBlocks B hB hUnbounded)) := by
  apply locallyFinite_of_open_cover_count_bounds _ U hcover
  intro a
  obtain ⟨m, hm⟩ := hbound a
  exact ⟨m, (count_sequenceOfBlocks_le_iff B hB hUnbounded (U a) m).mpr hm⟩

/-- Every cover member has one stage after which ALL actual restricted tails are empty. -/
theorem sequenceOfBlocks_empty_tails (a : ι) :
    ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
      (BlowupTowerTransforms.restrict
        (BlowupTowerTransforms.openPreimage
          ((sequenceOfBlocks B hB hUnbounded).stage N).2 (U a))
        (tailTower (sequenceOfBlocks B hB hUnbounded) N r)) := by
  obtain ⟨m, hm⟩ := hbound a
  exact exists_empty_tails_of_open_count_bound (sequenceOfBlocks B hB hUnbounded) (U a)
    ((count_sequenceOfBlocks_le_iff B hB hUnbounded (U a) m).mpr hm)

end Blocks

section Policy

variable (next : ∀ (_j : ℕ) {Y : CMfd.{u} n}, BlowupTower X Y →
  Σ Z : CMfd.{u} n, BlowupTower Y Z)

/-- Select and append actual finite blocks recursively from the original identity. -/
def blockEndpoints : ℕ → Σ Y : CMfd.{u} n, BlowupTower X Y
  | 0 => ⟨X, .refl⟩
  | j + 1 =>
      let p := blockEndpoints j
      let q := next j p.2
      ⟨q.1, p.2.append q.2⟩

/-- Every successive boundary is extended by the actual selected block. -/
theorem blockEndpoints_extend (j : ℕ) :
    ∃ Q : BlowupTower (blockEndpoints next j).1 (blockEndpoints next (j + 1)).1,
      (blockEndpoints next (j + 1)).2 = (blockEndpoints next j).2.append Q :=
  ⟨(next j (blockEndpoints next j).2).2, rfl⟩

/-- The real length increment retains the selected block's full original length. -/
theorem blockEndpoints_length_succ (j : ℕ) :
    (blockEndpoints next (j + 1)).2.length = (blockEndpoints next j).2.length +
      (next j (blockEndpoints next j).2).2.length :=
  BlowupTower.length_append _ _

variable (M : MarkedIdeals.MarkedIdeal n X)
  (hnext : ∀ (j : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y),
    MarkedIdeals.MarkedIdeal.IsGeoTestTower M T →
      MarkedIdeals.MarkedIdeal.IsGeoTestTower
        (MarkedIdeals.MarkedIdeal.geoTransformAlong M T) (next j T).2)

include hnext

/-- Actual testness is proved by recursion along the selected blocks. -/
theorem isGeoTestTower_blockEndpoints (j : ℕ) :
    MarkedIdeals.MarkedIdeal.IsGeoTestTower M (blockEndpoints next j).2 := by
  induction j with
  | zero => trivial
  | succ j ih =>
      exact (MarkedIdeals.MarkedIdeal.isGeoTestTower_append_iff M _ _).mpr
        ⟨ih, hnext j _ ih⟩

/-- A finite-block rule with local count bounds constructs the complete schedule
or a literally stationary finite chain. No resolving-block existence is assumed. -/
theorem finite_or_locallyFinite_test_schedule {ι : Type*} (U : ι → Opens X)
    (hcover : ∀ x : X, ∃ a, x ∈ U a)
    (hbound : ∀ a, ∃ m, ∀ j,
      countCentresMeeting (U a : Set X) (blockEndpoints next j).2 ≤ m) :
    (∃ a, ∀ b, a ≤ b → blockEndpoints next b = blockEndpoints next a) ∨
      ∃ s : GrowingSeq X,
        (∀ j, s.stage (blockEndpoints next j).2.length = blockEndpoints next j) ∧
        (∀ i, MarkedIdeals.MarkedIdeal.IsGeoTestTower M (s.stage i).2) ∧
        LocallyFinite (centreImage s) ∧
        ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
          (BlowupTowerTransforms.restrict
            (BlowupTowerTransforms.openPreimage (s.stage N).2 (U a)) (tailTower s N r)) := by
  let B := blockEndpoints next
  have hB := blockEndpoints_extend next
  rcases unbounded_or_eventually_constant B hB with hUnbounded | hFinite
  · let s := sequenceOfBlocks B hB hUnbounded
    refine Or.inr ⟨s, sequenceOfBlocks_boundary B hB hUnbounded, ?_, ?_, ?_⟩
    · exact isGeoTestTower_sequenceOfBlocks B hB hUnbounded M
        (isGeoTestTower_blockEndpoints next M hnext)
    · exact locallyFinite_sequenceOfBlocks B hB hUnbounded U hbound hcover
    · exact sequenceOfBlocks_empty_tails B hB hUnbounded U hbound
  · exact Or.inl hFinite

end Policy

end

end Hironaka.HironakaExhaustionBlockLocalFiniteness
