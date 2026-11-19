import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

/-! Exact labels and actual occupied lifts of the finite sheet schedule. -/
set_option autoImplicit false
open Set Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CofinalSheetScheduleLabels

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3RTowerClass HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
  HironakaG8OccupiedSlotComparison HironakaG8PhysicalChartOccupiedLifts G3UniversePhysicalClassComparisons
  HironakaG8SpatialCofinalPrecedence HironakaG8StageRankCoherence

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  (c : ℕ → TowerChart K Z P)

private abbrev Slots (i : ℕ) := {k // Occupied (c i).T k}

/-- Source clocks for the schedule have an initial occupied slot, one
occupied slot per leaf, and a last occupied terminal slot. -/
def HasFullSheetClock : Prop :=
  ∀ i k, Occupied (c i).T k ↔ k < i+3

/-- Across cutoffs, the common leaves retain their literal indices,
and the shared terminal slot moves to the larger cutoff's last slot. -/
def sheetScheduleLift (hFull : HasFullSheetClock c) {i j : ℕ} (h : i ≤ j) :
    Slots c i ↪o Slots c j := by
  let f (p : Slots c i) : Slots c j :=
    ⟨if p.val = i+2 then j+2 else p.val,(hFull _ _).mpr (by
      have hp := (hFull _ _).mp p.property
      split <;> omega)⟩
  have hStrict : StrictMono f := by
    intro p q hpq
    have hp := (hFull _ _).mp p.property
    have hq := (hFull _ _).mp q.property
    change p.val < q.val at hpq
    change (if p.val = i+2 then j+2 else p.val) < (if q.val = i+2 then j+2 else q.val)
    split <;> split <;> omega
  exact OrderEmbedding.ofStrictMono f hStrict

@[simp] theorem sheetScheduleLift_val
    (hFull : HasFullSheetClock c) {i j : ℕ} (h : i ≤ j) (p : Slots c i) :
    (sheetScheduleLift c hFull h p).val = if p.val = i+2 then j+2 else p.val := rfl

/-- The init uses some 0, leaf k uses some (k+1), and none denotes
the same terminal event independently of the cutoff. -/
def sheetScheduleEvents (hFull : HasFullSheetClock c) : CofinalEvents c (Option ℕ) where
  event i p := if p.val = i+2 then none else some p.val
  injective i := by
    intro p q h
    change (if p.val = i+2 then none else some p.val) =
      (if q.val = i+2 then none else some q.val) at h
    split at h <;> split at h
    · apply Subtype.ext; omega
    · contradiction
    · contradiction
    · exact Subtype.ext (Option.some.inj h)
  lift := fun h => sheetScheduleLift c hFull h
  lift_event := by
    intro i j h p
    change (if (if p.val = i+2 then j+2 else p.val) = j+2 then none
      else some (if p.val = i+2 then j+2 else p.val)) = (if p.val = i+2 then none else some p.val)
    have hp := (hFull _ _).mp p.property
    by_cases hEnd : p.val = i+2
    · simp [hEnd]
    · have hne' : p.val ≠ j+2 := by omega
      simp [hEnd,hne']
  lift_mono := by
    intro i j h p q hlt
    exact (sheetScheduleLift c hFull h).strictMono hlt

@[simp] theorem sheetScheduleEvents_label (hFull : HasFullSheetClock c) (i : ℕ) (p : Slots c i) :
    (sheetScheduleEvents c hFull).event i p = if p.val = i+2 then none else some p.val := rfl

/-- When the larger chart's literal restriction sees precisely the old
clock and its terminal, its actual occupied lift is the numeric schedule
lift. This applies to every genuine physical comparison. -/
theorem occupiedLiftOnOpen_eq_sheetScheduleLift
    (hFull : HasFullSheetClock c) {i j : ℕ} (hij : i ≤ j)
    (V : TopologicalSpace.Opens (c j).U)
    {f : CMfd.of (n := n) (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {e : (c i).Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (c j).T V)}
    (h : EmptyAwareTowerIso f (c i).T (restrict V (c j).T) e)
    (hVisible : ∀ k, Occupied (restrict V (c j).T) k ↔ k < i+2 ∨ k = j+2) :
    occupiedLiftOnOpen V (c j).T h = sheetScheduleLift c hFull hij := by
  apply occupied_orderEmbedding_unique_of_range
  ext q
  rw [mem_range_occupiedLiftOnOpen,hVisible]
  constructor
  · rintro (h | h)
    · let p : Slots c i := ⟨q.val,(hFull _ _).mpr (by omega)⟩
      refine ⟨p,Subtype.ext ?_⟩
      rw [sheetScheduleLift_val]
      exact if_neg (Nat.ne_of_lt h)
    · let p : Slots c i := ⟨i+2,(hFull _ _).mpr (by omega)⟩
      refine ⟨p,Subtype.ext ?_⟩
      rw [sheetScheduleLift_val]
      simpa [p] using h.symm
  · rintro ⟨p,rfl⟩
    rw [sheetScheduleLift_val]
    have hp := (hFull _ _).mp p.property
    split <;> omega

/-- The exact three occupied raw sheet traces give the visible-clock
formula on the union of sheets through the lower cutoff. -/
theorem occupied_restrict_iff_of_three_sheet_schedule
    {i j : ℕ} (hij : i ≤ j) (V : TopologicalSpace.Opens (c j).U)
    (sheet : Fin (j+1) → TopologicalSpace.Opens (c j).U)
    (hV : ∀ x : (c j).U, x ∈ V ↔ ∃ s, s.val ≤ i ∧ x ∈ sheet s)
    (hSheet : ∀ (s : Fin (j+1)) k,
      Occupied (restrict (sheet s) (c j).T) k ↔ k = s.val ∨ k = s.val+1 ∨ k = j+2)
    (k : ℕ) : Occupied (restrict V (c j).T) k ↔ k < i+2 ∨ k = j+2 := by
  have hLocal : Occupied (restrict V (c j).T) k ↔
      ∃ (s : Fin (j+1)), s.val ≤ i ∧ Occupied (restrict (sheet s) (c j).T) k := by
    constructor
    · intro h
      obtain ⟨x,hx,hxV⟩ := (occupied_restrict_iff_slotFootprint_meets _ _ _).mp h
      obtain ⟨s,hs,hxS⟩ := (hV x).mp hxV
      exact ⟨s,hs,(occupied_restrict_iff_slotFootprint_meets _ _ _).mpr ⟨x,hx,hxS⟩⟩
    · rintro ⟨s,hs,h⟩
      obtain ⟨x,hx,hxS⟩ := (occupied_restrict_iff_slotFootprint_meets _ _ _).mp h
      exact (occupied_restrict_iff_slotFootprint_meets _ _ _).mpr ⟨x,hx,(hV x).mpr ⟨s,hs,hxS⟩⟩
  rw [hLocal]
  constructor
  · rintro ⟨s,hs,h⟩
    rcases (hSheet s k).mp h with h | h | h <;> omega
  · rintro (hk | hk)
    · by_cases hki : k ≤ i
      · let s : Fin (j+1) := ⟨k,by omega⟩
        exact ⟨s,hki,(hSheet s k).mpr (Or.inl rfl)⟩
      · let s : Fin (j+1) := ⟨i,by omega⟩
        exact ⟨s,le_rfl,(hSheet s k).mpr (Or.inr (Or.inl (by change k = i+1; omega)))⟩
    · let s : Fin (j+1) := ⟨0,Nat.zero_lt_succ _⟩
      exact ⟨s,Nat.zero_le _, (hSheet s k).mpr (Or.inr (Or.inr hk))⟩

/-- On a completed cutoff, the sheet traces occupy every raw slot
through the terminal slot. -/
theorem hasFullSheetClock_of_sheet_traces
    (sheet : ∀ j, Fin (j+1) → TopologicalSpace.Opens (c j).U)
    (hCover : ∀ j (x : (c j).U), ∃ s, x ∈ sheet j s)
    (hSheet : ∀ j (s : Fin (j+1)) k,
      Occupied (restrict (sheet j s) (c j).T) k ↔ k = s.val ∨ k = s.val+1 ∨ k = j+2) :
    HasFullSheetClock c := by
  intro j k
  have hTop (x : (c j).U) : x ∈ (⊤ : TopologicalSpace.Opens (c j).U) ↔
      ∃ s : Fin (j+1), s.val ≤ j ∧ x ∈ sheet j s := by
    refine ⟨fun _ => ?_,fun _ => trivial⟩
    obtain ⟨s,hs⟩ := hCover j x
    exact ⟨s,Nat.le_of_lt_succ s.isLt,hs⟩
  have hOcc := occupied_restrict_iff_of_three_sheet_schedule c (le_refl j)
    ⊤ (sheet j) hTop (hSheet j) k
  have hRaw : Occupied (restrict (⊤ : TopologicalSpace.Opens (c j).U) (c j).T) k ↔ Occupied (c j).T k := by
    rw [occupied_restrict_iff_slotFootprint_meets,← slotFootprint_nonempty_iff]
    exact ⟨fun ⟨x,hx,_⟩ => ⟨x,hx⟩,fun ⟨x,hx⟩ => ⟨x,hx,trivial⟩⟩
  rw [← hRaw,hOcc]
  omega

/-- The numeric global labels use the actual counterpart of every
occupied occurrence for the class's chosen physical atlas comparisons. -/
theorem sheetScheduleEvents_lift_eq_chartOccupiedLift
    (hFull : HasFullSheetClock c) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hVisible : ∀ i j, i ≤ j → ∀ k,
      Occupied (restrict (nestedOpens (c j).U ((c i).U ⊓ (c j).U)) (c j).T) k ↔
        k < i+2 ∨ k = j+2)
    {i j : ℕ} (hij : i ≤ j) (p : Slots c i) :
    (sheetScheduleEvents c hFull).lift hij p = chartOccupiedLift cmp (c i) (c j) (hMono hij) p := by
  unfold chartOccupiedLift
  symm
  apply congrArg (fun g : Slots c i ↪o Slots c j => g p)
  exact occupiedLiftOnOpen_eq_sheetScheduleLift c hFull hij _ _ (hVisible i j hij)

theorem sheetScheduleEvents_occurs (hFull : HasFullSheetClock c) (a : Option ℕ) :
    ∃ i p, (sheetScheduleEvents c hFull).event i p = a := by
  cases a with
  | none =>
    exact ⟨0,⟨2,(hFull _ _).mpr (by decide)⟩,rfl⟩
  | some k =>
    let p : Slots c k := ⟨k,(hFull _ _).mpr (by omega)⟩
    refine ⟨k,p,?_⟩
    rw [sheetScheduleEvents_label]
    have h : p.val ≠ k+2 := by dsimp [p]; omega
    exact if_neg h

/-- The three real footprint hits on the last sheet of each cutoff
give unbounded directed height into the shared terminal event. -/
theorem no_weak_rank_of_scheduled_shared_sheet_hits
    (hFull : HasFullSheetClock c)
    (hHit : ∀ j, 0 < j → ∃ x : (c j).U,
      x ∈ slotFootprint (c j).T j ∧ x ∈ slotFootprint (c j).T (j+1) ∧
      x ∈ slotFootprint (c j).T (j+2)) :
    ¬ ∃ rank : Option ℕ → ℕ, ∀ ⦃a b⦄,
      SpatialBefore (sheetScheduleEvents c hFull) a b → rank a < rank b := by
  let E := sheetScheduleEvents c hFull
  have hEdges (k : ℕ) : SpatialBefore E (some (k+1)) (some (k+2)) ∧
      SpatialBefore E (some (k+2)) none := by
    let j := k+1
    obtain ⟨x,hx₀,hx₁,hx₂⟩ := hHit j (Nat.zero_lt_succ _)
    let p : Slots c j := ⟨j,(hFull _ _).mpr (by omega)⟩
    let q : Slots c j := ⟨j+1,(hFull _ _).mpr (by omega)⟩
    let r : Slots c j := ⟨j+2,(hFull _ _).mpr (by omega)⟩
    have hP : E.event j p = some (k+1) := by simp [E,p,j]
    have hQ : E.event j q = some (k+2) := by simp [E,q,j,Nat.add_assoc]
    have hR : E.event j r = none := by simp [E,r]
    have hp : x.val ∈ chartSlotFootprint (c j) p := ⟨x,hx₀,rfl⟩
    have hq : x.val ∈ chartSlotFootprint (c j) q := ⟨x,hx₁,rfl⟩
    have hr : x.val ∈ chartSlotFootprint (c j) r := ⟨x,hx₂,rfl⟩
    exact ⟨⟨j,p,q,hP,hQ,Nat.lt_succ_self _,x.val,hp,hq⟩,
      ⟨j,q,r,hQ,hR,Nat.lt_succ_self _,x.val,hq,hr⟩⟩
  have hChain (k : ℕ) : DependencyPath (SpatialBefore E) k (some (k+1)) := by
    induction k with
    | zero => exact .nil _
    | succ k ih => exact .step (hEdges k).1 ih
  intro h
  obtain ⟨cap,hCap⟩ := (exists_natural_rank_iff (SpatialBefore E)).mp h none
  have hOver := hCap _ (.step (hEdges cap).2 (hChain (cap+1)))
  omega


private theorem occupiedSlots_eq_sorted_of_iff {B C : CMfd.{0} n} (T : BlowupTower B C)
    (order : List ℕ) (hSorted : order.Pairwise (· < ·))
    (hOcc : ∀ k, Occupied T k ↔ k ∈ order) : occupiedSlots T = order := by
  have hSlots := occupiedSlots_pairwise T
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba) (hSlots.imp Nat.le_of_lt) (hSorted.imp Nat.le_of_lt)
  apply (List.perm_ext_iff_of_nodup (hSlots.imp Nat.ne_of_lt) (hSorted.imp Nat.ne_of_lt)).mpr
  intro k
  rw [mem_occupiedSlots]
  exact hOcc k

/-- Equality of the common raw leaf footprints and the separately
matched terminal footprint gives exact ordered occupied footprint equality.
The actual nested tower comparison is not needed for the footprint step. -/
theorem scheduled_orderedFootprints_eq_of_raw_readback
    (hFull : HasFullSheetClock c) {i j : ℕ} (hij : i ≤ j)
    (V : TopologicalSpace.Opens (c j).U)
    (f : CMfd.of (n := n) (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
    (hVisible : ∀ k, Occupied (restrict V (c j).T) k ↔ k < i+2 ∨ k = j+2)
    (hLeaf : ∀ k < i+2, slotFootprint (c i).T k = f ⁻¹' slotFootprint (restrict V (c j).T) k)
    (hTerminal : slotFootprint (c i).T (i+2) = f ⁻¹' slotFootprint (restrict V (c j).T) (j+2)) :
    occupiedFootprints (c i).T = (occupiedFootprints (restrict V (c j).T)).map (f ⁻¹' ·) := by
  have hSrc : occupiedSlots (c i).T = List.range (i+3) :=
    occupiedSlots_eq_sorted_of_iff (c i).T _ List.pairwise_lt_range
      (fun k => (hFull i k).trans List.mem_range.symm)
  have hTgt : occupiedSlots (restrict V (c j).T) = List.range (i+2) ++ [j+2] := by
    apply occupiedSlots_eq_sorted_of_iff
    · rw [List.pairwise_append]
      refine ⟨List.pairwise_lt_range,by simp,?_⟩
      intro a ha b hb
      have ha' := List.mem_range.mp ha
      have hb' : b = j+2 := by simpa using hb
      omega
    · intro k
      simpa only [List.mem_append,List.mem_range,List.mem_singleton] using hVisible k
  unfold occupiedFootprints
  rw [hSrc,hTgt,List.range_succ,List.map_append,List.map_append,List.map_append]
  simp only [List.map_cons,List.map_nil,← hTerminal]
  congr 1
  rw [List.map_map]
  exact List.map_congr_left (fun k hk => hLeaf k (List.mem_range.mp hk))

end Hironaka.HironakaG8CofinalSheetScheduleLabels
