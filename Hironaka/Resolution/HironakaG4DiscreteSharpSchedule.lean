import Hironaka.Resolution.HironakaG4DiscreteServiceBlocks
import Hironaka.Resolution.HironakaDisjointCompactExhaustionEscape

/-! Fair actual sharp histories for a discrete original bad locus. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4DiscreteSharpSchedule
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4DiscreteServiceBlocks HironakaG4SharpCountStability
  HironakaCountableTowerPrefixes HironakaExhaustionBlockLocalFiniteness
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq TowerPreimageCompact
open ResolutionInvariantSpec (countCentresMeeting)
variable {n : ℕ} {X : CMfd.{u} n}
variable (hn : 0 < n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
  (hdiscrete : IsDiscrete (originalSharpBadLocus (n := n) W E))
  (K : CompactExhaustion X)

def blocks (j : ℕ) : Σ Y : CMfd.{u} n, BlowupTower X Y :=
  ⟨(states hn hW hE hdense hdiscrete K j).Y,
    (states hn hW hE hdense hdiscrete K j).T⟩

private theorem blocks_extend (j : ℕ) :
    ∃ Q : BlowupTower (blocks hn hW hE hdense hdiscrete K j).1
        (blocks hn hW hE hdense hdiscrete K (j+1)).1,
      (blocks hn hW hE hdense hdiscrete K (j+1)).2 =
        (blocks hn hW hE hdense hdiscrete K j).2.append Q :=
  states_extend hn hW hE hdense hdiscrete K j

private theorem blocks_prefix (a b : ℕ) (hab : a ≤ b) :
    ∃ Q : BlowupTower (blocks hn hW hE hdense hdiscrete K a).1
        (blocks hn hW hE hdense hdiscrete K b).1,
      (blocks hn hW hE hdense hdiscrete K b).2 =
        (blocks hn hW hE hdense hdiscrete K a).2.append Q := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨.refl,rfl⟩
  | succ b _ ih =>
    obtain ⟨S,hS⟩ := ih
    obtain ⟨Q,hQ⟩ := blocks_extend hn hW hE hdense hdiscrete K b
    refine ⟨S.append Q,?_⟩
    rw [hQ,hS,BlowupTower.append_assoc]

def openTask (a : ℕ) : Opens X := ⟨interior (K a),isOpen_interior⟩

private theorem openTask_cover : ∀ x : X, ∃ a, x ∈ openTask K a := by
  intro x
  obtain ⟨a,ha⟩ := K.exists_mem x
  exact ⟨a+1,K.subset_interior_succ a ha⟩

private theorem block_count_bound (a : ℕ) : ∃ m, ∀ j,
    countCentresMeeting (openTask K a : Set X) (blocks hn hW hE hdense hdiscrete K j).2 ≤ m := by
  let B := blocks hn hW hE hdense hdiscrete K
  refine ⟨countCentresMeeting (openTask K a : Set X) (B (a+1)).2,fun j => ?_⟩
  rcases le_total j (a+1) with hj | hj
  · obtain ⟨S,hS⟩ := blocks_prefix hn hW hE hdense hdiscrete K j (a+1) hj
    rw [hS,countCentresMeeting_append]
    exact Nat.le_add_right _ _
  · obtain ⟨S,hS⟩ := blocks_prefix hn hW hE hdense hdiscrete K (a+1) j hj
    have hSharp := (states hn hW hE hdense hdiscrete K j).sharp
    change CurrentSharpCentres W E (B j).2 at hSharp
    rw [hS] at hSharp ⊢
    apply le_of_eq
    apply count_append_eq_of_sharp_resolved hW.1 hE.1 _ S hSharp
    intro z hz hzu
    exact (states hn hW hE hdense hdiscrete K (a+1)).good a (Nat.lt_succ_self a) z hz
      (interior_subset hzu)

private theorem sharp_head (N : Set X) (F : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CurrentSharpCentres N F T →
      ∀ k, CurrentSharpCentres N F (BlowupTowerSplit.head T k)
  | _,.refl,_,0 => trivial
  | _,.refl,_,_+1 => trivial
  | _,.step _ _ _ _,h,0 => h
  | _,.step T _ _ _,h,k+1 => sharp_head N F T h.1 k

private theorem sharp_takeSteps (N : Set X) (F : List (Set X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : CurrentSharpCentres N F T) (i : ℕ) :
    CurrentSharpCentres N F (takeSteps T i).2 := sharp_head N F T hT (T.length - i)

/-- The selected compact-task blocks yield a finite stationary history or a
locally finite actual growing sequence. Both original boundary tests and the
sharp-centre condition hold at every literal stage. -/
theorem finite_or_locallyFinite_discrete_sharp_schedule :
    (∃ a, ∀ b, a ≤ b → blocks hn hW hE hdense hdiscrete K b =
      blocks hn hW hE hdense hdiscrete K a) ∨
    ∃ s : GrowingSeq X,
      (∀ j, s.stage (blocks hn hW hE hdense hdiscrete K j).2.length =
        blocks hn hW hE hdense hdiscrete K j) ∧
      (∀ i, IsGeoTestTower (geometricTemplate W []) (s.stage i).2) ∧
      (∀ i, IsGeoTestTower (geometricTemplate (univ : Set X) E) (s.stage i).2) ∧
      (∀ i, CurrentSharpCentres W E (s.stage i).2) ∧
      (∀ j, ∀ z ∈ strictAlong (s.stage (blocks hn hW hE hdense hdiscrete K (j+1)).2.length).2 W,
        (s.stage (blocks hn hW hE hdense hdiscrete K (j+1)).2.length).2.proj z ∈ K j →
        normalCrossingsAt (n := n)
          (strictAlong (s.stage (blocks hn hW hE hdense hdiscrete K (j+1)).2.length).2 W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E)
            (s.stage (blocks hn hW hE hdense hdiscrete K (j+1)).2.length).2).E z) ∧
      LocallyFinite (centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (openTask K a)) (tailTower s N r)) := by
  let B := blocks hn hW hE hdense hdiscrete K
  have hB := blocks_extend hn hW hE hdense hdiscrete K
  rcases unbounded_or_eventually_constant B hB with hUnbounded | hFinite
  · let s := sequenceOfBlocks B hB hUnbounded
    refine Or.inr ⟨s,sequenceOfBlocks_boundary B hB hUnbounded,?_,?_,?_,?_,?_,?_⟩
    · apply isGeoTestTower_sequenceOfBlocks B hB hUnbounded
      intro j
      exact (states hn hW hE hdense hdiscrete K j).test
    · apply isGeoTestTower_sequenceOfBlocks B hB hUnbounded
      intro j
      exact (states hn hW hE hdense hdiscrete K j).full
    · intro i
      obtain ⟨j,hj⟩ := hUnbounded i
      rw [sequenceOfBlocks_stage B hB hUnbounded hj]
      exact sharp_takeSteps W E (B j).2 (states hn hW hE hdense hdiscrete K j).sharp i
    · intro j
      rw [sequenceOfBlocks_boundary B hB hUnbounded (j+1)]
      exact (states hn hW hE hdense hdiscrete K (j+1)).good j (Nat.lt_succ_self j)
    · exact locallyFinite_sequenceOfBlocks B hB hUnbounded (openTask K)
        (block_count_bound hn hW hE hdense hdiscrete K) (openTask_cover K)
    · intro a
      exact sequenceOfBlocks_empty_tails B hB hUnbounded (openTask K)
        (block_count_bound hn hW hE hdense hdiscrete K) a
  · exact Or.inl hFinite
end
end Hironaka.HironakaG4DiscreteSharpSchedule
