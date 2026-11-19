import Hironaka.Resolution.HironakaG8CountableCuspSheets
import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! Exact common raw and ordered footprints of the finite cusp sheet schedules. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspSheetFootprintTraces
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG8CountableCuspSheets HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison

abbrev PrefixManifold (m : ℕ) := CMfd.of (n := 3) (prefixOpen m)

def prefixSheetOrigin (m : ℕ) (s : Fin (m+1)) : prefixSheetOpen m s.val :=
  ⟨⟨(s.val,0),Nat.le_of_lt_succ s.isLt⟩,⟨mem_singleton _,mem_univ _⟩⟩

/-- The footprint fields returned after padding and gluing the three-step
singleton sheet towers. -/
def ScheduledSingletonTraces {Y : CMfd.{0} 3} (m : ℕ) (T : BlowupTower (PrefixManifold m) Y) : Prop :=
  ∀ s : Fin (m+1),
    let O := prefixSheetOpen m s.val
    let x := prefixSheetOrigin m s
    slotFootprint (restrict O T) s.val = {x} ∧
    slotFootprint (restrict O T) (s.val+1) = {x} ∧
    slotFootprint (restrict O T) (m+2) = {x} ∧
    (∀ k, (slotFootprint (restrict O T) k).Nonempty → k = s.val ∨ k = s.val+1 ∨ k = m+2)

theorem scheduled_rawFootprint_mem {m : ℕ} {Y : CMfd.{0} 3}
    {T : BlowupTower (PrefixManifold m) Y} (h : ScheduledSingletonTraces m T)
    (k : ℕ) (x : prefixOpen m) :
    x ∈ slotFootprint T k ↔
      x.val.2 = 0 ∧ (k = x.val.1 ∨ k = x.val.1+1 ∨ k = m+2) := by
  let s : Fin (m+1) := ⟨x.val.1,Nat.lt_succ_of_le x.property⟩
  let O := prefixSheetOpen m s.val
  let y : O := ⟨x,⟨mem_singleton _,mem_univ _⟩⟩
  obtain ⟨h₀,h₁,h₂,hOther⟩ := h s
  have hTrace : y ∈ slotFootprint (restrict O T) k ↔ x ∈ slotFootprint T k := by
    rw [slotFootprint_restrict]
    rfl
  have hPoint : y ∈ ({prefixSheetOrigin m s} : Set O) ↔ x.val.2 = 0 := by
    rw [mem_singleton_iff]
    constructor
    · intro he
      exact congrArg (fun z : O => z.val.val.2) he
    · intro he
      exact Subtype.ext (Subtype.ext (Prod.ext rfl he))
  rw [← hTrace]
  constructor
  · intro hy
    have hCases := hOther k ⟨y,hy⟩
    refine ⟨?_,hCases⟩
    rcases hCases with rfl | rfl | rfl
    · exact hPoint.mp (h₀ ▸ hy)
    · exact hPoint.mp (h₁ ▸ hy)
    · exact hPoint.mp (h₂ ▸ hy)
  · rintro ⟨hx,hCases⟩
    have hy := hPoint.mpr hx
    change k = s.val ∨ k = s.val+1 ∨ k = m+2 at hCases
    rcases hCases with rfl | rfl | rfl
    · exact h₀.symm ▸ hy
    · exact h₁.symm ▸ hy
    · exact h₂.symm ▸ hy

variable {i j : ℕ} {Y Z : CMfd.{0} 3}
  {T : BlowupTower (PrefixManifold i) Y} {S : BlowupTower (PrefixManifold j) Z}

local notation "𝓘c" => 𝓘(ℂ, ComplexModel 3)
local notation "V" => nestedOpens (prefixOpen j) (prefixOpen i)

/-- Common init/leaves retain raw indices and the terminal moves. These
are set equalities on the actual literal nested base, before any comparison
of terminal objects is constructed. -/
theorem scheduled_footprints_cross_cutoff
    (hij : i ≤ j) (hT : ScheduledSingletonTraces i T) (hS : ScheduledSingletonTraces j S)
    (f : PrefixManifold i ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := 3) V)
    (hf : ∀ x : prefixOpen i, (f x).val.val = x.val) :
    (∀ k < i+2, slotFootprint T k = f ⁻¹' slotFootprint (restrict V S) k) ∧
      slotFootprint T (i+2) = f ⁻¹' slotFootprint (restrict V S) (j+2) := by
  constructor
  · intro k hk
    rw [slotFootprint_restrict]
    ext x
    change x ∈ slotFootprint T k ↔ (f x).val ∈ slotFootprint S k
    rw [scheduled_rawFootprint_mem hT,scheduled_rawFootprint_mem hS,hf x]
    apply and_congr_right
    intro _
    omega
  · rw [slotFootprint_restrict]
    ext x
    change x ∈ slotFootprint T (i+2) ↔ (f x).val ∈ slotFootprint S (j+2)
    rw [scheduled_rawFootprint_mem hT,scheduled_rawFootprint_mem hS,hf x]
    simp only [or_true,and_true]

/-- The smaller literal window sees exactly its original raw leaf clocks
and the larger chart's actual terminal. -/
theorem scheduled_occupied_restrict_cross_cutoff
    (hij : i ≤ j) (hS : ScheduledSingletonTraces j S) (k : ℕ) :
    Occupied (restrict V S) k ↔ k < i+2 ∨ k = j+2 := by
  rw [← slotFootprint_nonempty_iff,slotFootprint_restrict]
  constructor
  · rintro ⟨x,hx⟩
    have hi : x.val.val.1 ≤ i := x.property
    have hRead := (scheduled_rawFootprint_mem hS k x.val).mp hx
    rcases hRead.2 with h | h | h <;> omega
  · intro h
    let s := min k i
    let x : prefixOpen j := ⟨(s,0),(Nat.min_le_right _ _).trans hij⟩
    refine ⟨⟨x,Nat.min_le_right _ _⟩,?_⟩
    apply (scheduled_rawFootprint_mem hS k x).mpr
    change 0 = (0 : ComplexModel 3) ∧ (k = s ∨ k = s+1 ∨ k = j+2)
    refine ⟨rfl,?_⟩
    dsimp [s]
    omega


theorem scheduled_occupied_iff {m : ℕ} {B : CMfd.{0} 3} {R : BlowupTower (PrefixManifold m) B}
    (h : ScheduledSingletonTraces m R) (k : ℕ) :
    Occupied R k ↔ k < m+3 := by
  rw [← slotFootprint_nonempty_iff]
  constructor
  · rintro ⟨x,hx⟩
    have hxM : x.val.1 ≤ m := x.property
    rcases ((scheduled_rawFootprint_mem h k x).mp hx).2 with h | h | h <;> omega
  · intro hk
    let s := min k m
    let x : prefixOpen m := ⟨(s,0),Nat.min_le_right _ _⟩
    refine ⟨x,(scheduled_rawFootprint_mem h k x).mpr ⟨rfl,?_⟩⟩
    change k = min k m ∨ k = min k m + 1 ∨ k = m+2
    omega

private theorem occupiedSlots_eq_of_increasing_mem {B C : CMfd.{0} 3} (R : BlowupTower B C)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) (h : ∀ k, Occupied R k ↔ k ∈ l) :
    occupiedSlots R = l := by
  have hSort := occupiedSlots_pairwise R
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba) (hSort.imp Nat.le_of_lt) (hl.imp Nat.le_of_lt)
  apply (List.perm_ext_iff_of_nodup (hSort.imp Nat.ne_of_lt) (hl.imp Nat.ne_of_lt)).mpr
  intro k
  rw [mem_occupiedSlots]
  exact h k

/-- The full ordered occupied lists agree over the literal lower cutoff,
with the later terminal replacing the old last raw index. -/
theorem scheduled_occupiedFootprints_cross_cutoff
    (hij : i ≤ j) (hT : ScheduledSingletonTraces i T) (hS : ScheduledSingletonTraces j S)
    (f : PrefixManifold i ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := 3) V)
    (hf : ∀ x : prefixOpen i, (f x).val.val = x.val) :
    occupiedFootprints T = (occupiedFootprints (restrict V S)).map (f ⁻¹' ·) := by
  have hSrc : occupiedSlots T = List.range (i+3) :=
    occupiedSlots_eq_of_increasing_mem T _ List.pairwise_lt_range
      (fun k => (scheduled_occupied_iff hT k).trans List.mem_range.symm)
  have hTgt : occupiedSlots (restrict V S) = List.range (i+2) ++ [j+2] := by
    apply occupiedSlots_eq_of_increasing_mem
    · rw [List.pairwise_append]
      refine ⟨List.pairwise_lt_range,by simp,?_⟩
      intro a ha b hb
      have ha' := List.mem_range.mp ha
      have hb' : b = j+2 := by simpa using hb
      omega
    · intro k
      simpa only [List.mem_append,List.mem_range,List.mem_singleton] using
        scheduled_occupied_restrict_cross_cutoff hij hS k
  obtain ⟨hLeaf,hTerminal⟩ := scheduled_footprints_cross_cutoff hij hT hS f hf
  unfold occupiedFootprints
  rw [hSrc,hTgt,List.range_succ,List.map_append,List.map_append,List.map_append]
  simp only [List.map_cons,List.map_nil,← hTerminal]
  congr 1
  rw [List.map_map]
  exact List.map_congr_left (fun k hk => hLeaf k (List.mem_range.mp hk))

/-- The last sheet supplies a single original point through each of
the last three occupied source footprints. -/
theorem scheduled_shared_last_sheet_hits {m : ℕ} {B : CMfd.{0} 3}
    {R : BlowupTower (PrefixManifold m) B} (h : ScheduledSingletonTraces m R) :
    ∃ x : prefixOpen m, x ∈ slotFootprint R m ∧
      x ∈ slotFootprint R (m+1) ∧ x ∈ slotFootprint R (m+2) := by
  let x : prefixOpen m := ⟨(m,0),show m ≤ m from Nat.le_refl _⟩
  exact ⟨x,(scheduled_rawFootprint_mem h _ x).mpr ⟨rfl,Or.inl rfl⟩,
    (scheduled_rawFootprint_mem h _ x).mpr ⟨rfl,Or.inr (Or.inl rfl)⟩,
    (scheduled_rawFootprint_mem h _ x).mpr ⟨rfl,Or.inr (Or.inr rfl)⟩⟩

end
end Hironaka.HironakaG8CuspSheetFootprintTraces
