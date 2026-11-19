import Hironaka.Resolution.HironakaG8OccupiedSlotComparison
import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence
import Mathlib.Data.List.Sort

/-! Ordered projected footprints without extra empty slots. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OrderedFootprintTraces

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison HironakaG3RTowerClass
  HironakaG8PhysicalChartOccupiedLifts HironakaG8SpatialCofinalPrecedence
  G3UniversePhysicalClassComparisons

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Literal restriction filters the occupied raw slots by visibility and
retains their order. -/
theorem occupiedSlots_restrict_eq_filter (T : BlowupTower X Y) (U : Opens X) :
    occupiedSlots (restrict U T) =
      (occupiedSlots T).filter (fun i => decide (Occupied (restrict U T) i)) := by
  have hLeft := occupiedSlots_pairwise (restrict U T)
  have hRight := (occupiedSlots_pairwise T).filter (fun i => decide (Occupied (restrict U T) i))
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (hLeft.imp Nat.le_of_lt) (hRight.imp Nat.le_of_lt)
  apply (List.perm_ext_iff_of_nodup (hLeft.imp Nat.ne_of_lt) (hRight.imp Nat.ne_of_lt)).mpr
  intro i
  simp only [List.mem_filter, mem_occupiedSlots, decide_eq_true_eq]
  exact ⟨fun hi => ⟨occupied_of_restrict U T hi,hi⟩, And.right⟩

/-- The ordered footprint list on an open is read from the original list
by deleting invisible footprints and taking the exact trace of each survivor. -/
theorem occupiedFootprints_restrict_eq_filterMap (T : BlowupTower X Y) (U : Opens X) :
    occupiedFootprints (restrict U T) = (occupiedFootprints T).filterMap
      (fun footprint => if (footprint ∩ (U : Set X)).Nonempty then
        some ((Subtype.val : U → X) ⁻¹' footprint) else none) := by
  unfold occupiedFootprints
  rw [occupiedSlots_restrict_eq_filter, List.filterMap_map]
  generalize occupiedSlots T = slots
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    by_cases hi : Occupied (restrict U T) i
    · have hMeet := (occupied_restrict_iff_slotFootprint_meets T U i).mp hi
      simp [hi,hMeet,slotFootprint_restrict,ih]
    · have hMiss := mt (occupied_restrict_iff_slotFootprint_meets T U i).mpr hi
      simp [hi,hMiss,ih]

/-- A physical history whose occupied slots are exactly the given list
has that whole ordered footprint list, including multiplicities. -/
theorem occupiedFootprints_eq_map_of_exact_slots {ι : Type*}
    (T : BlowupTower X Y) (order : List ι) (footprint : ι → Set X)
    (hRead : ∀ j e, order[j]? = some e → slotFootprint T j = footprint e)
    (hOcc : ∀ j, (slotFootprint T j).Nonempty ↔ j < order.length) :
    occupiedFootprints T = order.map footprint := by
  have hRange : occupiedSlots T = List.range order.length := by
    have hSorted := occupiedSlots_pairwise T
    apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
      (fun _ _ _ _ hab hba => le_antisymm hab hba)
      (hSorted.imp Nat.le_of_lt) List.pairwise_le_range
    apply (List.perm_ext_iff_of_nodup (hSorted.imp Nat.ne_of_lt) List.nodup_range).mpr
    intro j
    rw [mem_occupiedSlots, ← slotFootprint_nonempty_iff, List.mem_range, hOcc]
  unfold occupiedFootprints
  rw [hRange]
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map,List.getElem?_map]
  cases hj : order[j]? with
  | none =>
    have hMiss : order.length ≤ j := List.getElem?_eq_none_iff.mp hj
    have hRangeMiss : (List.range order.length)[j]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa using hMiss)
    rw [hRangeMiss]
    rfl
  | some e =>
    rw [List.getElem?_range (List.getElem?_eq_some_iff.mp hj).1]
    simp [hRead j e hj]

private theorem same_strict_rank_list {ι κ : Type*} [LinearOrder κ] {L M : List ι} (rank : ι → κ)
    (hRank : Function.Injective rank) (hL : L.Pairwise (fun a b => rank a < rank b))
    (hM : M.Pairwise (fun a b => rank a < rank b)) (hMem : ∀ a, a ∈ L ↔ a ∈ M) : L = M := by
  have hLne : L.Nodup := hL.imp (fun h he => (ne_of_lt h) (congrArg rank he))
  have hMne : M.Nodup := hM.imp (fun h he => (ne_of_lt h) (congrArg rank he))
  exact List.Perm.eq_of_pairwise (le := fun a b => rank a ≤ rank b)
    (fun _ _ _ _ hab hba => hRank (le_antisymm hab hba))
    (hL.imp le_of_lt) (hM.imp le_of_lt)
    ((List.perm_ext_iff_of_nodup hLne hMne).mpr hMem)

/-- Once each physical chart realizes the common event rank, its ordered
footprints agree with the corresponding trace of every larger chart. -/
theorem keyed_cofinal_footprint_traces_agree {κ : Type*} [LinearOrder κ]
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → κ) (hRank : Function.Injective rank)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    {A : ℕ → CMfd.{0} n} (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length)
    {i j : ℕ} (hij : i ≤ j) :
    (occupiedFootprints (R i)).map (fun F => (Subtype.val : (c i).U → X) '' F) =
      ((occupiedFootprints (R j)).map (fun F => (Subtype.val : (c j).U → X) '' F)).filterMap
        (fun F => if (F ∩ ((c i).U : Set X)).Nonempty then some (F ∩ ((c i).U : Set X)) else none) := by
  have hReal (k : ℕ) : (occupiedFootprints (R k)).map (fun F => (Subtype.val : (c k).U → X) '' F) =
      (order k).map (chartSlotFootprint (c k)) := by
    rw [occupiedFootprints_eq_map_of_exact_slots (R k) (order k)
      (fun p => slotFootprint (c k).T p.val) (hRead k) (hOcc k), List.map_map]
    rfl
  have hTrace (k : ℕ) (p : {l // Occupied (c k).T l}) : chartSlotFootprint (c k) p =
      cofinalEventFootprint E (E.event k p) ∩ ((c k).U : Set X) := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨k,p,rfl,hx⟩, by obtain ⟨y,_,rfl⟩ := hx; exact y.property⟩
    · rintro ⟨hx,hU⟩
      obtain ⟨q,hq,hqX⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift k (E.event k p) hU).mp hx
      rwa [E.injective k hq] at hqX
  let F (a : ι) := cofinalEventFootprint E a ∩ ((c i).U : Set X)
  let visible (a : ι) : Bool := decide (F a).Nonempty
  have hVisible (a : ι) : (F a).Nonempty ↔ ∃ p, E.event i p = a := by
    constructor
    · rintro ⟨x,hx,hU⟩
      obtain ⟨p,hp,_⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a hU).mp hx
      exact ⟨p,hp⟩
    · rintro ⟨p,rfl⟩
      have hMeet := ((slotFootprint_nonempty_iff (c i).T p.val).mpr p.property).image
        (Subtype.val : (c i).U → X)
      change (cofinalEventFootprint E (E.event i p) ∩ ((c i).U : Set X)).Nonempty
      rw [← hTrace i p]
      exact hMeet
  let labels (k : ℕ) := (order k).map (E.event k)
  have hLabels (k : ℕ) : (labels k).Pairwise (fun a b => rank a < rank b) :=
    List.pairwise_map.mpr (hSorted k)
  have hEqual : labels i = (labels j).filter visible := by
    apply same_strict_rank_list rank hRank (hLabels i) ((hLabels j).filter visible)
    intro a
    simp only [labels, List.mem_map, List.mem_filter, visible, decide_eq_true_eq]
    constructor
    · rintro ⟨p,_,rfl⟩
      exact ⟨⟨E.lift hij p,hComplete _ _,E.lift_event hij p⟩, (hVisible _).mpr ⟨p,rfl⟩⟩
    · rintro ⟨_,hVis⟩
      obtain ⟨p,hp⟩ := (hVisible a).mp hVis
      exact ⟨p,hComplete _ _,hp⟩
  have hLeft : (order i).map (chartSlotFootprint (c i)) = (labels i).map F := by
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => hTrace i p)
  have hRight : ∀ order' : List ι,
      order'.filterMap (fun a => if (F a).Nonempty then some (F a) else none) =
        (order'.filter visible).map F := by
    intro order'
    induction order' with
    | nil => rfl
    | cons a order' ih => by_cases ha : (F a).Nonempty <;> simp [ha,visible,ih]
  rw [hReal, hReal, hLeft, hEqual, ← hRight]
  simp only [labels,List.filterMap_map]
  apply List.filterMap_congr
  intro p _
  have hF : chartSlotFootprint (c j) p ∩ ((c i).U : Set X) = F (E.event j p) := by
    rw [hTrace j p,inter_assoc,inter_eq_right.mpr (hMono hij)]
  simp only [Function.comp_apply, hF]

/-- The natural-key specialization of ordered cofinal trace agreement. -/
theorem ranked_cofinal_footprint_traces_agree
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (hRank : Function.Injective rank)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    {A : ℕ → CMfd.{0} n} (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length)
    {i j : ℕ} (hij : i ≤ j) :
    (occupiedFootprints (R i)).map (fun F => (Subtype.val : (c i).U → X) '' F) =
      ((occupiedFootprints (R j)).map (fun F => (Subtype.val : (c j).U → X) '' F)).filterMap
        (fun F => if (F ∩ ((c i).U : Set X)).Nonempty then some (F ∩ ((c i).U : Set X)) else none) :=
  keyed_cofinal_footprint_traces_agree E cmp hMono hLift rank hRank order hComplete hSorted R hRead hOcc hij


end
end Hironaka.HironakaG8OrderedFootprintTraces
