import Hironaka.Resolution.HironakaG8GeometricIndexedWord
import Hironaka.Resolution.HironakaG8NestedWordFootprintAdapter

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8GeometricNestedWordLift

open BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG8OccupiedSlotComparison HironakaG8NestedVisibleWordLift
  HironakaG8GeometricIndexedWord HironakaG8IndexedSwapTraceLift HironakaG8NestedWordFootprintAdapter
  HironakaG8FiniteSpatialOrdering G3UniverseEmptyAwareCore

variable {n : ℕ} {X : CMfd.{0} n}

/-- A smaller word step records its actual TEST successor and over-source
terminal map, alongside its exact visible transposition. -/
def PhysicalSmallerMove (U : Opens X) (N : MarkedIdeal n X) (i : ℕ)
    (S T : TowerAt (CMfd.of (n := n) U)) : Prop :=
  SwapAt Disjoint i (footprintsIn S) (footprintsIn T) ∧
  IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) T.2 ∧
  ∃ e : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ T.1, T.2.proj ∘ e = S.2.proj

private theorem visible_at_iff (U : Opens X) (L : TowerAt X)
    (i : ℕ) (hi : i < L.2.length) :
    ((footprintTraces U L)[i]?.any visibleTrace = true) ↔
      (slotFootprint L.2 i ∩ (U : Set X)).Nonempty := by
  simp [footprintTraces,footprints,List.getElem?_map,List.getElem?_range hi,visibleTrace]

private theorem nested_geometric_step
    (U : Opens X) (W : Set X) (N : MarkedIdeal n X) (hN : N.IsWellFormed)
    {i : ℕ} {L R : TowerAt X} {S : TowerAt (CMfd.of (n := n) U)}
    (hMove : GeometricIndexedMove W N i L R) (hS : LiteralNestedTower U L S) :
    if ((footprintTraces U L)[i]?.any visibleTrace &&
        (footprintTraces U L)[i+1]?.any visibleTrace) then
      ∃ T, PhysicalSmallerMove U N (((footprintTraces U L).take i).filter visibleTrace).length S T ∧
        LiteralNestedTower U R T ∧ footprintsIn T = (footprintTraces U R).filter visibleTrace
    else LiteralNestedTower U R S := by
  obtain ⟨hIdx,hL,hR,_,_,e,_,⟨geom⟩,hInvisible⟩ := hMove
  have hi : i+1 < L.2.length := hIdx.1
  have hi₀ : i < L.2.length := by omega
  by_cases hBoth : ((footprintTraces U L)[i]?.any visibleTrace &&
      (footprintTraces U L)[i+1]?.any visibleTrace) = true
  · rw [if_pos hBoth]
    obtain ⟨T,η,hTest,hProj,hComp,hTrace,hRead⟩ :=
      physical_nested_move_at_filtered_index U N hN e geom hi hL hR
        (indexed_readback_trace_swap U hIdx) hS hBoth
    exact ⟨T,⟨hTrace,hTest,η,hProj⟩,hComp,hRead⟩
  · rw [if_neg hBoth]
    have hMiss : Disjoint (U : Set X) (slotFootprint L.2 i) ∨
        Disjoint (U : Set X) (slotFootprint L.2 (i+1)) := by
      by_contra hn
      push Not at hn
      have h0 := (visible_at_iff U L i hi₀).mpr
        (Set.not_disjoint_iff_nonempty_inter.mp (fun h => hn.1 h.symm))
      have h1 := (visible_at_iff U L (i+1) hi).mpr
        (Set.not_disjoint_iff_nonempty_inter.mp (fun h => hn.2 h.symm))
      exact hBoth (by simp [h0,h1])
    obtain ⟨χ,_,hχ⟩ := hInvisible U hMiss
    obtain ⟨hOcc,ψ,hψ⟩ := hS
    have hComp := G3UniverseEmptyAwareCore.trans hψ hχ
    rw [Diffeomorph.refl_trans] at hComp
    exact ⟨hOcc,ψ.trans χ,hComp⟩

private theorem terminal_of_physical_word
    {U : Opens X} {N : MarkedIdeal n X} {v : List ℕ}
    {S T : TowerAt (CMfd.of (n := n) U)}
    (h : RealizedWord (PhysicalSmallerMove U N) v S T)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) S.2) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) T.2 ∧
      ∃ e : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ T.1, T.2.proj ∘ e = S.2.proj := by
  induction h with
  | nil => exact ⟨hTest,Diffeomorph.refl _ _ _,rfl⟩
  | cons hs _ ih =>
    obtain ⟨_,hMid,e,he⟩ := hs
    obtain ⟨hFinal,f,hf⟩ := ih hMid
    refine ⟨hFinal,e.trans f,?_⟩
    change _ ∘ (f ∘ e) = _
    rw [← Function.comp_assoc,hf,he]

/-- Any realized geometric larger word lifts to an actual smaller TEST
word. Invisible moves stutter, and the exact filtered indices and
literal nested comparison survive through the final state. -/
theorem lift_geometric_word_to_smaller_test
    (U : Opens X) (W : Set X) (N : MarkedIdeal n X) (hN : N.IsWellFormed)
    {w : List ℕ} {L R : TowerAt X}
    (h : RealizedWord (GeometricIndexedMove W N) w L R)
    {S : TowerAt (CMfd.of (n := n) U)} (hS : LiteralNestedTower U L S)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) S.2) :
    ∃ (v : List ℕ) (T : TowerAt (CMfd.of (n := n) U)), v.length ≤ w.length ∧
      RealizedWord (PhysicalSmallerMove U N) v S T ∧
      SwapWord Disjoint v (footprintsIn S) (footprintsIn T) ∧
      LiteralNestedTower U R T ∧ footprintsIn T = (footprintTraces U R).filter visibleTrace ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) T.2 ∧
      ∃ e : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ T.1, T.2.proj ∘ e = S.2.proj := by
  obtain ⟨v,T,hLen,hWord,hTrace,hComp,hRead⟩ :=
    lift_indexed_occupied_word U (GeometricIndexedMove W N) (PhysicalSmallerMove U N)
      (fun hs => hs.1) (fun hs ht _ => nested_geometric_step U W N hN hs ht)
      h hS (footprintsIn_eq_filtered_traces U L S hS)
  exact ⟨v,T,hLen,hWord,hTrace,hComp,hRead,terminal_of_physical_word hWord hTest⟩

end Hironaka.HironakaG8GeometricNestedWordLift
