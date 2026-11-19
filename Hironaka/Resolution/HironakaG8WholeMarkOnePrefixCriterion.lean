import Hironaka.Resolution.HironakaG8LabelledOriginalCanonicalPrefixes
import Hironaka.Invariant.GeneralValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8WholeMarkOnePrefixCriterion
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres GeneralValue NonmonomialOrderLocal
  HironakaStageCenters HironakaG8LabelledNativeHistory HironakaG8LabelledOriginalCanonicalPrefixes

private abbrev original {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ, E, vanishingIdeal (n := n) W, 1⟩

/-- On a nonempty physical center there is an anchor of top nonmonomial
order. The remaining original letter is constant on the center and
strictly drops off it within the top-order stratum. -/
def WholeMarkOneStageCriterion {n : ℕ} {X Y : CMfd.{0} (n + 1)}
    (W : Set X) (E : List (Set X)) (S : BlowupTower X Y) (C : Set Y) : Prop :=
  let P := original W E
  let A := (geoTransformAlong P S).cosupp
  let o := nmOrd (geoTransformAlong P S)
  let q := fun y => (ofLex ((canonicalInvariant (n + 1)).inv P S y)).2
  C = ∅ ∨ ∃ c ∈ C,
    (∀ y ∈ A, o y ≤ o c) ∧
    (∀ y ∈ C, o y = o c ∧ q y = q c) ∧
    (∀ y ∈ A, y ∉ C → o y = o c → q y < q c)

set_option maxHeartbeats 1300000 in
private theorem whole_stage_criterion_iff {n : ℕ} {X Y : CMfd.{0} (n + 1)}
    (W : Set X) (E : List (Set X)) (S : BlowupTower X Y) (C : Set Y)
    (hC : C ⊆ (geoTransformAlong (original W E) S).cosupp) :
    WholeMarkOneStageCriterion W E S C ↔
      C = ∅ ∨ C = maxLocus ((canonicalInvariant (n + 1)).inv (original W E) S)
        (geoTransformAlong (original W E) S).cosupp := by
  let P := original W E
  let A := (geoTransformAlong P S).cosupp
  let o := nmOrd (geoTransformAlong P S)
  let v := (canonicalInvariant (n + 1)).inv P S
  let q := fun y => (ofLex (v y)).2
  have hv (y : Y) : v y = toLex (o y, q y) := by
    change v y = toLex ((ofLex (v y)).1, (ofLex (v y)).2)
    rfl
  have hLt (x y : Y) : v x < v y ↔ o x < o y ∨ (o x = o y ∧ q x < q y) := by
    rw [hv x, hv y, Prod.Lex.toLex_lt_toLex]
  have hI {x y : Y} (hl : o x < o y) : v x < v y := (hLt x y).mpr (Or.inl hl)
  change (C = ∅ ∨ ∃ c ∈ C,
    (∀ y ∈ A, o y ≤ o c) ∧ (∀ y ∈ C, o y = o c ∧ q y = q c) ∧
    (∀ y ∈ A, y ∉ C → o y = o c → q y < q c)) ↔ _
  constructor
  · rintro (hEmpty | ⟨c, hc, hTop, hTie, hBelow⟩)
    · exact Or.inl hEmpty
    right
    have hStrict {y : Y} (hy : y ∈ A) (hyC : y ∉ C) : v y < v c := by
      by_cases hEq : o y = o c
      · exact (hLt _ _).mpr (Or.inr ⟨hEq, hBelow y hy hyC hEq⟩)
      · exact hI (lt_of_le_of_ne (hTop y hy) hEq)
    have hEqual {y : Y} (hy : y ∈ C) : v y = v c := by
      rw [hv y, hv c, (hTie y hy).1, (hTie y hy).2]
    have hcMax : c ∈ maxLocus v A := by
      refine ⟨hC hc, fun y hy => ?_⟩
      by_cases hyC : y ∈ C
      · exact le_of_eq (hEqual hyC)
      · exact le_of_lt (hStrict hy hyC)
    ext y
    constructor
    · intro hy
      exact ⟨hC hy, fun z hz => (hcMax.2 z hz).trans_eq (hEqual hy).symm⟩
    · intro hy
      by_contra hyC
      exact (not_lt.mpr (hy.2 c hcMax.1)) (hStrict hy.1 hyC)
  · rintro (hEmpty | hMax)
    · exact Or.inl hEmpty
    by_cases hNe : C.Nonempty
    · right
      obtain ⟨c, hc⟩ := hNe
      have hcMax : c ∈ maxLocus v A := hMax ▸ hc
      have hTop (y : Y) (hy : y ∈ A) : o y ≤ o c := by
        exact not_lt.mp fun h => (not_lt.mpr (hcMax.2 y hy)) (hI h)
      refine ⟨c, hc, hTop, ?_, ?_⟩
      · intro y hy
        have hyMax : y ∈ maxLocus v A := hMax ▸ hy
        have hEq := congrArg ofLex (le_antisymm (hcMax.2 y hyMax.1) (hyMax.2 c hcMax.1))
        exact ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
      · intro y hy hyC hEq
        have hStrict : v y < v c := by
          apply lt_of_le_of_ne (hcMax.2 y hy)
          intro he
          apply hyC
          rw [hMax]
          exact ⟨hy, fun z hz => (hcMax.2 z hz).trans_eq he.symm⟩
        exact ((hLt _ _).mp hStrict).resolve_left (not_lt.mpr hEq.ge) |>.2
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hNe)

set_option maxHeartbeats 1200000 in
/-- Original canonicality of the entire mark-one prefix is equivalent
to the order and remaining-letter criterion at every physical center
of that same tested tower. -/
theorem whole_markOne_canonical_iff_stage_criterion {n : ℕ}
    {X Y : CMfd.{0} (n + 1)} (W : Set X) (E : List (Set X)) (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (original W E) T) :
    IsCanonical (original W E) ((canonicalInvariant (n + 1)).inv (original W E)) T ↔
      StageCentres (WholeMarkOneStageCriterion W E) T := by
  induction T with
  | refl => exact Iff.rfl
  | step S C π hπ ih =>
    have hG := whole_stage_criterion_iff W E S C hTest.2.2.1
    have ihS := ih hTest.1
    exact and_congr ihS hG.symm

/-- A labelled singular history supplies the actual whole test tower
and the raw epoch chart certificates. The only whole-record comparison
left is the stage criterion on this same physical history. -/
theorem labelled_whole_markOne_canonical_criterion {n : ℕ}
    {X Y : CMfd.{0} (n + 1)} {W K : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (h : LabelledNativeTower (n + 1) W E K T L) :
    LabelledRawEpochPrefixes (Nat.succ_pos n) W E T L ∧
    (IsCanonical (original W E) ((canonicalInvariant (n + 1)).inv (original W E)) T ↔
      StageCentres (WholeMarkOneStageCriterion W E) T) :=
  ⟨labelled_native_raw_epoch_prefixes (Nat.succ_pos n) h,
    whole_markOne_canonical_iff_stage_criterion W E T h.test_and_singular.1⟩

end
end Hironaka.HironakaG8WholeMarkOnePrefixCriterion
