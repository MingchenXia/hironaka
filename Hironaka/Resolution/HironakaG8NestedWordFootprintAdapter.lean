import Hironaka.Resolution.HironakaG8NestedVisibleWordLift
import Hironaka.Resolution.HironakaG8NestedMoveReadback
import Hironaka.Resolution.HironakaG8RankedTestCompression

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NestedWordFootprintAdapter
open BlowupTowers BlowupTowerTransforms HironakaStageCenters
  HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry
  HironakaG8NestedVisibleWordLift HironakaG8RankedTestCompression
  HironakaG8VisibleSwapWord HironakaG8FiniteSpatialOrdering

variable {n : ℕ} {X : CMfd.{0} n}

private theorem sorted_eq {l m : List ℕ} (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·))
    (hMem : ∀ i, i ∈ l ↔ i ∈ m) : l = m :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ h₁ h₂ => Nat.le_antisymm h₁ h₂) (hl.imp Nat.le_of_lt) (hm.imp Nat.le_of_lt)
    ((List.perm_ext_iff_of_nodup (hl.imp Nat.ne_of_lt) (hm.imp Nat.ne_of_lt)).mpr hMem)

private theorem occupied_raw_range {Y : CMfd.{0} n} (S : BlowupTower X Y)
    (h : StageCentres (fun _ C => C.Nonempty) S) :
    occupiedSlots S = List.range S.length := by
  apply sorted_eq (occupiedSlots_pairwise S) List.pairwise_lt_range
  intro i
  rw [mem_occupiedSlots,List.mem_range]
  exact ⟨occupied_lt_length S,fun hi => occupied_of_empty_free S h ⟨i,hi⟩⟩

private noncomputable def traceIndices (U : Opens X) (L : TowerAt X) : List ℕ :=
  (List.range L.2.length).filter (fun i => visibleTrace (slotFootprint L.2 i ∩ (U : Set X)))

private theorem occupied_restrict_ranges (U : Opens X) (L : TowerAt X) :
    occupiedSlots (restrict U L.2) = traceIndices U L := by
  apply sorted_eq (occupiedSlots_pairwise _) (List.pairwise_lt_range.filter _)
  intro i
  rw [mem_occupiedSlots,occupied_restrict_iff_slotFootprint_meets]
  simp only [List.mem_filter,List.mem_range,visibleTrace,decide_eq_true_eq]
  refine ⟨fun h => ⟨?_,h⟩,fun h => h.2⟩
  exact occupied_lt_length L.2
    (occupied_of_restrict U L.2 ((occupied_restrict_iff_slotFootprint_meets L.2 U i).mpr h))

/-- The raw word input list is exactly the filtered trace list for every
empty-free smaller history with a literal nested comparison. -/
theorem footprintsIn_eq_filtered_traces (U : Opens X) (L : TowerAt X)
    (S : TowerAt (CMfd.of (n := n) U)) (h : LiteralNestedTower U L S) :
    footprintsIn S = (footprintTraces U L).filter visibleTrace := by
  obtain ⟨hOcc,e,hCmp⟩ := h
  have hList : occupiedFootprints S.2 = occupiedFootprints (restrict U L.2) := by
    simpa only [Diffeomorph.coe_refl,preimage_id,List.map_id'] using occupiedFootprints_emptyAware hCmp
  unfold footprintsIn footprints footprintTraces
  rw [← occupied_raw_range S.2 hOcc]
  change (occupiedFootprints S.2).map _ = _
  rw [hList]
  unfold occupiedFootprints
  rw [occupied_restrict_ranges U L,List.map_map]
  simp only [footprints,List.map_map,List.filter_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,slotFootprint_restrict,Set.image_preimage_eq_inter_range]
  have hRange : Set.range (Subtype.val : U → X) = (U : Set X) := by
    ext x
    exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  rw [hRange]

/-- If both original footprints are visible, the exact smaller trace
transposition has the index of the filtered prefix of the larger list. -/
theorem nested_trace_swap_at_filtered_index (U : Opens X)
    {i : ℕ} {L M : TowerAt X} {S T : TowerAt (CMfd.of (n := n) U)}
    (hLarge : SwapAt Disjoint i (footprintTraces U L) (footprintTraces U M))
    (hS : LiteralNestedTower U L S) (hT : LiteralNestedTower U M T)
    (hBoth : ((footprintTraces U L)[i]?.any visibleTrace &&
      (footprintTraces U L)[i+1]?.any visibleTrace) = true) :
    SwapAt Disjoint (((footprintTraces U L).take i).filter visibleTrace).length
      (footprintsIn S) (footprintsIn T) := by
  have hh := swapAt_filter_exact visibleTrace hLarge
  rw [if_pos hBoth] at hh
  rwa [← footprintsIn_eq_filtered_traces U L S hS,← footprintsIn_eq_filtered_traces U M T hT] at hh

open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG8DisjointSwapFullHistory HironakaG8NestedMoveReadback

/-- The both-visible physical branch for the word interface. Its small
successor is TEST, with the exact filtered adjacent trace index and
the literal comparison to the same larger successor. -/
theorem physical_nested_move_at_filtered_index
    (U : Opens X) (N : MarkedIdeal n X) (hN : N.IsWellFormed)
    {i : ℕ} {L M : TowerAt X} (e : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ M.1)
    (geom : AdjacentSwapGeometry L.2 M.2 e i) (hi : i+1 < L.2.length)
    (hL : IsGeoTestTower N L.2) (hM : IsGeoTestTower N M.2)
    (hTrace : SwapAt Disjoint i (footprintTraces U L) (footprintTraces U M))
    {S : TowerAt (CMfd.of (n := n) U)} (hS : LiteralNestedTower U L S)
    (hBoth : ((footprintTraces U L)[i]?.any visibleTrace &&
      (footprintTraces U L)[i+1]?.any visibleTrace) = true) :
    ∃ (T : TowerAt (CMfd.of (n := n) U))
      (η : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ T.1),
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) T.2 ∧
      T.2.proj ∘ η = S.2.proj ∧ LiteralNestedTower U M T ∧
      SwapAt Disjoint (((footprintTraces U L).take i).filter visibleTrace).length
        (footprintsIn S) (footprintsIn T) ∧
      footprintsIn T = (footprintTraces U M).filter visibleTrace := by
  have hi₀ : i < L.2.length := by omega
  have hVis : (slotFootprint L.2 i ∩ (U : Set X)).Nonempty ∧
      (slotFootprint L.2 (i+1) ∩ (U : Set X)).Nonempty := by
    simpa [footprintTraces,footprints,List.getElem?_map,List.getElem?_range hi₀,
      List.getElem?_range hi,visibleTrace] using hBoth
  obtain ⟨hOldOcc,ψ,hOld⟩ := hS
  let idU := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞
  obtain ⟨K,S',η,θ,hOcc,hTest,hProj,hNew,_,_,_⟩ :=
    visible_nested_move_readback N hN geom hL hM U hVis.1 hVis.2 S.2 idU ψ hOld
  let T : TowerAt (CMfd.of (n := n) U) := ⟨K,S'⟩
  have hT : LiteralNestedTower U M T := ⟨hOcc,θ,hNew⟩
  let N' := MarkedIdeal.pullback (Subtype.val : U → X) N
  have hN' := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN U
  have hid : MarkedIdeal.pullback idU N' = N' :=
    ContactCanonicalAlong.pullback_id N' hN'.isCoherent
  rw [hid] at hTest
  exact ⟨T,η,hTest,hProj,hT,nested_trace_swap_at_filtered_index U hTrace ⟨hOldOcc,ψ,hOld⟩ hT hBoth,
    footprintsIn_eq_filtered_traces U M T hT⟩

end Hironaka.HironakaG8NestedWordFootprintAdapter
