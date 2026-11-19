import Hironaka.Resolution.HironakaG4CompactComponentPartition
import Hironaka.Resolution.HironakaG4CompactComponentBlocks
import Hironaka.Resolution.HironakaG4WindowSharpSchedule

/-! A locally finite schedule supported on compact original bad components. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactComponentSchedule
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower GlobalComponents
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4GeneralSharpBadLocus HironakaG4SharpBadFootprint HironakaG4SharpCountStability
  HironakaG4CompactComponentTasks HironakaG4CompactComponentPartition HironakaG4CompactComponentBlocks
  HironakaCountableTowerPrefixes HironakaExhaustionBlockLocalFiniteness
  HironakaLocallyFiniteResolutionSequence HironakaG4WindowSharpSchedule TowerPreimageCompact
  ResolutionInvariantSeq
open ResolutionInvariantSpec (countCentresMeeting)
variable {n : ℕ} {X : CMfd.{u} n}
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
  (hdisj : Pairwise (fun C D : globalComponents (n := n) (originalSharpBadLocus (n := n) W E) =>
    Disjoint C.val D.val)) (K : CompactExhaustion X)

abbrev originalBad := originalSharpBadLocus (n := n) W E
abbrev compactBad := compactComponentUnion (originalBad (W := W) (E := E))
abbrev noncompactBad := noncompactComponentUnion (originalBad (W := W) (E := E))

include hW hE hdense in
theorem bad_analytic : IsComplexAnalyticSubset (n := n) (originalBad (W := W) (E := E)) :=
  isComplexAnalyticSubset_originalSharpBadLocus hW hE hdense

def blocks (j : ℕ) : Σ Y : CMfd.{u} n, BlowupTower X Y :=
  ⟨(componentStates hn hW hE hdense hdisj K j).Y,
    (componentStates hn hW hE hdense hdisj K j).T⟩

private theorem blocks_extend (j : ℕ) :
    ∃ Q : BlowupTower (blocks hn hW hE hdense hdisj K j).1
        (blocks hn hW hE hdense hdisj K (j+1)).1,
      (blocks hn hW hE hdense hdisj K (j+1)).2 =
        (blocks hn hW hE hdense hdisj K j).2.append Q :=
  componentStates_extend hn hW hE hdense hdisj K j

private theorem blocks_prefix (a b : ℕ) (hab : a ≤ b) :
    ∃ Q : BlowupTower (blocks hn hW hE hdense hdisj K a).1
        (blocks hn hW hE hdense hdisj K b).1,
      (blocks hn hW hE hdense hdisj K b).2 =
        (blocks hn hW hE hdense hdisj K a).2.append Q := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨.refl,rfl⟩
  | succ b _ ih =>
    obtain ⟨S,hS⟩ := ih
    obtain ⟨Q,hQ⟩ := blocks_extend hn hW hE hdense hdisj K b
    refine ⟨S.append Q,?_⟩
    rw [hQ,hS,BlowupTower.append_assoc]

/-- An open cover: the compact-bad-free open, and exhaustion opens avoiding
all noncompact bad components. -/
def openTask : ℕ → Opens X
  | 0 => ⟨(compactBad (W := W) (E := E))ᶜ,
      (isClosed_compactComponentUnion (bad_analytic hW hE hdense)).isOpen_compl⟩
  | a+1 => ⟨interior (K a) \ noncompactBad (W := W) (E := E),
      isOpen_interior.inter (isClosed_noncompactComponentUnion (bad_analytic hW hE hdense)).isOpen_compl⟩

include hdisj in
private theorem openTask_cover : ∀ x : X, ∃ a, x ∈ openTask hW hE hdense K a := by
  intro x
  by_cases hx : x ∈ compactBad (W := W) (E := E)
  · have hxc : x ∉ noncompactBad (W := W) (E := E) := by
      intro hc
      exact Set.disjoint_left.mp (compact_noncompact_disjoint hdisj) hx hc
    obtain ⟨a,ha⟩ := K.exists_mem x
    exact ⟨a+2, K.subset_interior_succ a ha,hxc⟩
  · exact ⟨0,hx⟩

private theorem block_count_bound (a : ℕ) : ∃ m, ∀ j,
    countCentresMeeting (openTask hW hE hdense K a : Set X) (blocks hn hW hE hdense hdisj K j).2 ≤ m := by
  let B := blocks hn hW hE hdense hdisj K
  cases a with
  | zero =>
    refine ⟨0,fun j => ?_⟩
    have hD : Disjoint (openTask hW hE hdense K 0 : Set X) (compactBad (W := W) (E := E)) := by
      apply Set.disjoint_left.mpr
      intro x hx hA
      exact hx hA
    exact (count_zero_of_centresOver_disjoint hD (B j).2
      (componentStates hn hW hE hdense hdisj K j).support).le
  | succ a =>
    refine ⟨countCentresMeeting (openTask hW hE hdense K (a+1) : Set X) (B (a+1)).2,fun j => ?_⟩
    rcases le_total j (a+1) with hj | hj
    · obtain ⟨S,hS⟩ := blocks_prefix hn hW hE hdense hdisj K j (a+1) hj
      rw [hS,countCentresMeeting_append]
      exact Nat.le_add_right _ _
    · obtain ⟨S,hS⟩ := blocks_prefix hn hW hE hdense hdisj K (a+1) j hj
      have hSharp := (componentStates hn hW hE hdense hdisj K j).sharp
      change CurrentSharpCentres W E (B j).2 at hSharp
      rw [hS] at hSharp ⊢
      apply le_of_eq
      apply count_append_eq_of_sharp_resolved hW.1 hE.1 _ S hSharp
      intro z hz hzU
      by_cases hzA : (B (a+1)).2.proj z ∈ compactBad (W := W) (E := E)
      · exact (componentStates hn hW hE hdense hdisj K (a+1)).good a (Nat.lt_succ_self a)
          z hz ⟨interior_subset hzU.1,hzA⟩
      · have hznot : (B (a+1)).2.proj z ∉ originalBad (W := W) (E := E) := by
          intro hzB
          apply hzA
          have hzBA : (B (a+1)).2.proj z ∈
              originalBad (W := W) (E := E) ∩ (noncompactBad (W := W) (E := E))ᶜ := ⟨hzB,hzU.2⟩
          rwa [(compact_only_bad_slice (bad_analytic hW hE hdense) hdisj).2] at hzBA
        obtain ⟨hFoot,_⟩ := currentSharpCentres_original_footprint hW.1 hE.1 (B (a+1)).2
          (componentStates hn hW hE hdense hdisj K (a+1)).sharp
        by_contra hnc
        exact hznot (hFoot ⟨hz,hnc⟩)

/-- The compact bad components admit either a stationary finite chain or a
locally finite actual sharp sequence that serves each compact task on them. -/
theorem finite_or_locallyFinite_compact_component_schedule :
    (∃ a, ∀ b, a ≤ b → blocks hn hW hE hdense hdisj K b = blocks hn hW hE hdense hdisj K a) ∨
    ∃ s : GrowingSeq X,
      (∀ j, s.stage (blocks hn hW hE hdense hdisj K j).2.length = blocks hn hW hE hdense hdisj K j) ∧
      (∀ i, IsGeoTestTower (geometricTemplate W []) (s.stage i).2) ∧
      (∀ i, IsGeoTestTower (geometricTemplate (univ : Set X) E) (s.stage i).2) ∧
      (∀ i, CurrentSharpCentres W E (s.stage i).2) ∧
      (∀ i, CentresOver (compactBad (W := W) (E := E)) (s.stage i).2) ∧
      (∀ j, ∀ z ∈ strictAlong (s.stage (blocks hn hW hE hdense hdisj K (j+1)).2.length).2 W,
        (s.stage (blocks hn hW hE hdense hdisj K (j+1)).2.length).2.proj z ∈
          (K j : Set X) ∩ compactBad (W := W) (E := E) →
        normalCrossingsAt (n := n)
          (strictAlong (s.stage (blocks hn hW hE hdense hdisj K (j+1)).2.length).2 W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E)
            (s.stage (blocks hn hW hE hdense hdisj K (j+1)).2.length).2).E z) ∧
      LocallyFinite (centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (openTask hW hE hdense K a)) (tailTower s N r)) := by
  let B := blocks hn hW hE hdense hdisj K
  have hB := blocks_extend hn hW hE hdense hdisj K
  rcases unbounded_or_eventually_constant B hB with hUnbounded | hFinite
  · let s := sequenceOfBlocks B hB hUnbounded
    refine Or.inr ⟨s,sequenceOfBlocks_boundary B hB hUnbounded,?_,?_,?_,?_,?_,?_,?_⟩
    · apply isGeoTestTower_sequenceOfBlocks B hB hUnbounded
      intro j
      exact (componentStates hn hW hE hdense hdisj K j).test
    · apply isGeoTestTower_sequenceOfBlocks B hB hUnbounded
      intro j
      exact (componentStates hn hW hE hdense hdisj K j).full
    · intro i
      obtain ⟨j,hj⟩ := hUnbounded i
      rw [sequenceOfBlocks_stage B hB hUnbounded hj]
      exact sharp_takeSteps W E (B j).2 (componentStates hn hW hE hdense hdisj K j).sharp i
    · intro i
      obtain ⟨j,hj⟩ := hUnbounded i
      rw [sequenceOfBlocks_stage B hB hUnbounded hj]
      exact centresOver_head (compactBad (W := W) (E := E)) (B j).2 ((B j).2.length-i)
        (componentStates hn hW hE hdense hdisj K j).support
    · intro j
      rw [sequenceOfBlocks_boundary B hB hUnbounded (j+1)]
      exact (componentStates hn hW hE hdense hdisj K (j+1)).good j (Nat.lt_succ_self j)
    · exact locallyFinite_sequenceOfBlocks B hB hUnbounded (openTask hW hE hdense K)
        (block_count_bound hn hW hE hdense hdisj K) (openTask_cover hW hE hdense hdisj K)
    · intro a
      exact sequenceOfBlocks_empty_tails B hB hUnbounded (openTask hW hE hdense K)
        (block_count_bound hn hW hE hdense hdisj K) a
  · exact Or.inl hFinite
end
end Hironaka.HironakaG4CompactComponentSchedule
