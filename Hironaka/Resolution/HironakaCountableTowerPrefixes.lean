import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Blowup.BlowupTowerSplit

/-!
# Reading every original step of a countable chain of finite blowup towers

An unbounded chain of actual finite extensions is read one original step at a
time. No extra empty step is inserted, and zero-length blocks are permitted.
This is a scheduling prerequisite; it does not construct the geometric blocks
needed to resolve an arbitrary noncompact analytic space.

Blueprint: `hironaka-countable-tower-prefixes.tex`.
-/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaCountableTowerPrefixes

open Hironaka.BlowupSequences BlowupTowers ResolutionInvariantSeq

noncomputable section

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The first `i` original steps, using the native split of the actual tower. -/
def takeSteps (T : BlowupTower X Y) (i : ℕ) :
    Σ Z : CMfd.{u} n, BlowupTower X Z :=
  ⟨(BlowupTowerSplit.split T (T.length - i)).1,
    BlowupTowerSplit.head T (T.length - i)⟩

/-- Truncation beyond the endpoint returns the entire dependent tower pair. -/
theorem takeSteps_eq_self (T : BlowupTower X Y) {i : ℕ} (hi : T.length ≤ i) :
    takeSteps T i = ⟨Y, T⟩ := by
  unfold takeSteps
  rw [Nat.sub_eq_zero_of_le hi]
  cases T <;> rfl

private theorem takeSteps_step_of_le (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) {i : ℕ} (hi : i ≤ T.length) :
    takeSteps (.step T C π hπ) i = takeSteps T i := by
  have he : T.length + 1 - i = (T.length - i) + 1 := by omega
  unfold takeSteps
  simp only [BlowupTower.length_step]
  rw [he]
  rfl

@[simp] theorem takeSteps_zero (T : BlowupTower X Y) :
    takeSteps T 0 = ⟨X, .refl⟩ := by
  induction T with
  | refl => rfl
  | step T C π hπ ih => rw [takeSteps_step_of_le T C π hπ (Nat.zero_le _)]; exact ih

/-- Appending any finite block leaves all earlier recorded truncations unchanged. -/
theorem takeSteps_append_of_le (T : BlowupTower X Y) (Q : BlowupTower Y Z)
    {i : ℕ} (hi : i ≤ T.length) : takeSteps (T.append Q) i = takeSteps T i := by
  induction Q with
  | refl => rfl
  | step Q C π hπ ih =>
      have hle : i ≤ (T.append Q).length := by
        rw [BlowupTower.length_append]
        omega
      rw [BlowupTower.append_step, takeSteps_step_of_le _ C π hπ hle]
      exact ih

/-- Adjacent truncations are joined by the original actual blowup. -/
theorem takeSteps_succ (T : BlowupTower X Y) {i : ℕ} (hi : i < T.length) :
    ∃ (C : Set (takeSteps T i).1)
      (π : (takeSteps T (i + 1)).1 → (takeSteps T i).1)
      (hπ : IsBlowupAlong n C π),
      (takeSteps T (i + 1)).2 = .step (takeSteps T i).2 C π hπ := by
  induction T with
  | refl => simp only [BlowupTower.length_refl] at hi; omega
  | @step Y Z T C π hπ ih =>
      by_cases hlt : i < T.length
      · rw [takeSteps_step_of_le T C π hπ hlt.le,
          takeSteps_step_of_le T C π hπ hlt]
        exact ih hlt
      · have heq : i = T.length := by simp only [BlowupTower.length_step] at hi; omega
        subst i
        rw [takeSteps_step_of_le T C π hπ le_rfl,
          takeSteps_eq_self T le_rfl,
          takeSteps_eq_self (.step T C π hπ) (i := T.length + 1) le_rfl]
        exact ⟨C, π, hπ, rfl⟩

/-- The native split gives the expected number of retained original steps. -/
theorem length_takeSteps (T : BlowupTower X Y) (i : ℕ) :
    (takeSteps T i).2.length = min i T.length := by
  change (BlowupTowerSplit.head T (T.length - i)).length = _
  rw [BlowupTowerSplit.length_head]
  omega

/-- A genuine truncation cannot increase any actual centre count. -/
theorem count_takeSteps_le (K : Set X) (T : BlowupTower X Y) (i : ℕ) :
    ResolutionInvariantSpec.countCentresMeeting K (takeSteps T i).2 ≤
      ResolutionInvariantSpec.countCentresMeeting K T := by
  classical
  induction T with
  | refl => rw [takeSteps_eq_self .refl (Nat.zero_le i)]
  | step T C π hπ ih =>
      by_cases hi : i ≤ T.length
      · rw [takeSteps_step_of_le T C π hπ hi]
        exact ih.trans (Nat.le_add_right _ _)
      · rw [takeSteps_eq_self (.step T C π hπ) (i := i) (by
          simp only [BlowupTower.length_step]
          omega)]

/-- Truncation retains canonicality for the unchanged original invariant. -/
theorem isCanonical_takeSteps {Λ : Type v} [LinearOrder Λ]
    (M : MarkedIdeals.MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (T : BlowupTower X Y) (hT : ResolutionInvariantSpec.IsCanonical M inv T) (i : ℕ) :
    ResolutionInvariantSpec.IsCanonical M inv (takeSteps T i).2 :=
  BlowupTowerSplit.isCanonical_head M inv T (T.length - i) hT

/-- The whole original marked-record test condition survives every truncation. -/
theorem isGeoTestTower_takeSteps (M : MarkedIdeals.MarkedIdeal n X)
    (T : BlowupTower X Y) (hT : MarkedIdeals.MarkedIdeal.IsGeoTestTower M T) (i : ℕ) :
    MarkedIdeals.MarkedIdeal.IsGeoTestTower M (takeSteps T i).2 :=
  ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M T (T.length - i)).mp hT).1

section Chain

variable (B : ℕ → Σ Y : CMfd.{u} n, BlowupTower X Y)
  (hB : ∀ j, ∃ Q : BlowupTower (B j).1 (B (j + 1)).1,
    (B (j + 1)).2 = (B j).2.append Q)

include hB

/-- The literal finite block lengths are nondecreasing, including zero blocks. -/
theorem monotone_length : Monotone (fun j => (B j).2.length) := by
  apply monotone_nat_of_le_succ
  intro j
  obtain ⟨Q, hQ⟩ := hB j
  rw [hQ, BlowupTower.length_append]
  omega

/-- Two boundaries containing a given step have the same entire prefix. -/
theorem takeSteps_chain_eq {a b i : ℕ} (hab : a ≤ b) (hi : i ≤ (B a).2.length) :
    takeSteps (B b).2 i = takeSteps (B a).2 i := by
  induction hab with
  | refl => rfl
  | @step b hab ih =>
      obtain ⟨Q, hQ⟩ := hB b
      rw [hQ, takeSteps_append_of_le _ Q (hi.trans (monotone_length B hB hab))]
      exact ih

private theorem takeSteps_agrees {a b i : ℕ}
    (ha : i ≤ (B a).2.length) (hb : i ≤ (B b).2.length) :
    takeSteps (B a).2 i = takeSteps (B b).2 i := by
  rcases le_total a b with hab | hba
  · exact (takeSteps_chain_eq B hB hab ha).symm
  · exact takeSteps_chain_eq B hB hba hb

variable (hUnbounded : ∀ i, ∃ j, i ≤ (B j).2.length)

private def readStage (i : ℕ) : Σ Y : CMfd.{u} n, BlowupTower X Y :=
  takeSteps (B (hUnbounded i).choose).2 i

private theorem readStage_eq_takeSteps {i j : ℕ} (hj : i ≤ (B j).2.length) :
    readStage B hUnbounded i = takeSteps (B j).2 i :=
  takeSteps_agrees B hB (hUnbounded i).choose_spec hj

/-- Read every original step of the blocks, without any additional padding. -/
def sequenceOfBlocks : GrowingSeq X where
  stage := readStage B hUnbounded
  zero := takeSteps_zero _
  succ i := by
    obtain ⟨j, hj⟩ := hUnbounded (i + 1)
    rw [readStage_eq_takeSteps B hB hUnbounded (Nat.le_trans (Nat.le_succ i) hj),
      readStage_eq_takeSteps B hB hUnbounded hj]
    exact takeSteps_succ (B j).2 hj

/-- Any sufficiently long boundary reads the same actual dependent stage. -/
theorem sequenceOfBlocks_stage {i j : ℕ} (hj : i ≤ (B j).2.length) :
    (sequenceOfBlocks B hB hUnbounded).stage i = takeSteps (B j).2 i :=
  readStage_eq_takeSteps B hB hUnbounded hj

/-- Every original finite boundary occurs literally, not just up to isomorphism. -/
theorem sequenceOfBlocks_boundary (j : ℕ) :
    (sequenceOfBlocks B hB hUnbounded).stage (B j).2.length = B j := by
  rw [sequenceOfBlocks_stage B hB hUnbounded le_rfl, takeSteps_eq_self _ le_rfl]

/-- A bound at block boundaries is exactly a bound on the full unrolled history. -/
theorem count_sequenceOfBlocks_le_iff (K : Set X) (m : ℕ) :
    (∀ i, ResolutionInvariantSpec.countCentresMeeting K
      ((sequenceOfBlocks B hB hUnbounded).stage i).2 ≤ m) ↔
    ∀ j, ResolutionInvariantSpec.countCentresMeeting K (B j).2 ≤ m := by
  constructor
  · intro h j
    have hj := h (B j).2.length
    rwa [sequenceOfBlocks_boundary] at hj
  · intro h i
    obtain ⟨j, hj⟩ := hUnbounded i
    rw [sequenceOfBlocks_stage B hB hUnbounded hj]
    exact (count_takeSteps_le K (B j).2 i).trans (h j)

/-- Endpoint testness implies testness at every original step of the new history. -/
theorem isGeoTestTower_sequenceOfBlocks (M : MarkedIdeals.MarkedIdeal n X)
    (hT : ∀ j, MarkedIdeals.MarkedIdeal.IsGeoTestTower M (B j).2) (i : ℕ) :
    MarkedIdeals.MarkedIdeal.IsGeoTestTower M ((sequenceOfBlocks B hB hUnbounded).stage i).2 := by
  obtain ⟨j, hj⟩ := hUnbounded i
  rw [sequenceOfBlocks_stage B hB hUnbounded hj]
  exact isGeoTestTower_takeSteps M (B j).2 (hT j) i

/-- This transfer uses the SAME original invariant; no current-stage rebasing occurs. -/
theorem isCanonical_sequenceOfBlocks {Λ : Type v} [LinearOrder Λ]
    (M : MarkedIdeals.MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hT : ∀ j, ResolutionInvariantSpec.IsCanonical M inv (B j).2) (i : ℕ) :
    ResolutionInvariantSpec.IsCanonical M inv ((sequenceOfBlocks B hB hUnbounded).stage i).2 := by
  obtain ⟨j, hj⟩ := hUnbounded i
  rw [sequenceOfBlocks_stage B hB hUnbounded hj]
  exact isCanonical_takeSteps M inv (B j).2 (hT j) i

/-- A bounded chain stabilizes as the SAME dependent tower, without padding. -/
theorem unbounded_or_eventually_constant :
    (∀ i, ∃ j, i ≤ (B j).2.length) ∨ ∃ a, ∀ b, a ≤ b → B b = B a := by
  classical
  by_cases h : ∀ i, ∃ j, i ≤ (B j).2.length
  · exact Or.inl h
  · push Not at h
    obtain ⟨m, hm⟩ := h
    let f : ℕ → ℕ := fun j => (B j).2.length
    have hfin : (range f).Finite := (finite_Iio m).subset (by
      rintro _ ⟨j, rfl⟩
      exact hm j)
    obtain ⟨_, ⟨a, rfl⟩, hmax⟩ :=
      Set.exists_max_image (range f) id hfin ⟨f 0, mem_range_self 0⟩
    refine Or.inr ⟨a, fun b hab => ?_⟩
    have hle : (B b).2.length ≤ (B a).2.length := hmax (f b) (mem_range_self b)
    have he := takeSteps_chain_eq B hB hab (i := (B a).2.length) le_rfl
    rw [takeSteps_eq_self _ hle, takeSteps_eq_self _ le_rfl] at he
    exact he

end Chain

end

end Hironaka.HironakaCountableTowerPrefixes
