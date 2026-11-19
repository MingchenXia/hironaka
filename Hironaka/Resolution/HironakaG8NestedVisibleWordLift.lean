import Hironaka.Resolution.HironakaG8VisibleSwapWord
import Hironaka.Resolution.HironakaG8IndexedDisjointSwap

set_option autoImplicit false
namespace Hironaka.HironakaG8NestedVisibleWordLift

open HironakaG8FiniteSpatialOrdering HironakaG8VisibleSwapWord

/-- A word retaining the realized states of every indexed move. -/
inductive RealizedWord {L : Type*} (move : ℕ → L → L → Prop) :
    List ℕ → L → L → Prop
  | nil (l : L) : RealizedWord move [] l l
  | cons {i : ℕ} {w : List ℕ} {l m t : L} :
      move i l m → RealizedWord move w m t → RealizedWord move (i :: w) l t

/-- Lift a realized larger word using a single-step nested move rule.
The relation `compatible` can retain the actual empty-aware comparison.
At every recursive step the small readout is the exact filtered large
readout, and each surviving move uses its compressed prefix index. -/
theorem lift_realized_word
    {L S α : Type*} {I : α → α → Prop} (visible : α → Bool)
    (large : L → List α) (small : S → List α)
    (largeMove : ℕ → L → L → Prop) (smallMove : ℕ → S → S → Prop)
    (compatible : L → S → Prop)
    (largeRead : ∀ {i l m}, largeMove i l m → SwapAt I i (large l) (large m))
    (nestedMove : ∀ {i l m s}, largeMove i l m → compatible l s →
      small s = (large l).filter visible →
      if ((large l)[i]?.any visible && (large l)[i+1]?.any visible) then
        ∃ t, smallMove (((large l).take i).filter visible).length s t ∧
          compatible m t ∧ small t = (large m).filter visible
      else compatible m s)
    {w : List ℕ} {l m : L} (h : RealizedWord largeMove w l m)
    {s : S} (hComp : compatible l s) (hRead : small s = (large l).filter visible) :
    ∃ (v : List ℕ) (t : S), v.length ≤ w.length ∧
      RealizedWord smallMove v s t ∧
      SwapWord I v (small s) (small t) ∧
      compatible m t ∧ small t = (large m).filter visible := by
  induction h generalizing s with
  | nil l =>
      exact ⟨[], s, Nat.le_refl _, .nil _, .nil _, hComp, hRead⟩
  | @cons i w l m f hMove _ ih =>
      have hNested := nestedMove hMove hComp hRead
      have hVisible := swapAt_filter_exact visible (largeRead hMove)
      split at hNested
      · rename_i hBoth
        rw [if_pos hBoth] at hVisible
        obtain ⟨s', hSmall, hComp', hRead'⟩ := hNested
        obtain ⟨v, t, hLen, hWord, hTrace, hEnd, hFinal⟩ := ih hComp' hRead'
        rw [← hRead, ← hRead'] at hVisible
        exact ⟨_ :: v, t, Nat.succ_le_succ hLen, .cons hSmall hWord,
          .cons hVisible hTrace, hEnd, hFinal⟩
      · rename_i hNotBoth
        rw [if_neg hNotBoth] at hVisible
        obtain ⟨v, t, hLen, hWord, hTrace, hEnd, hFinal⟩ :=
          ih hNested (hRead.trans hVisible)
        exact ⟨v, t, hLen.trans (Nat.le_succ _), hWord, hTrace, hEnd, hFinal⟩


open Set TopologicalSpace
noncomputable section
open scoped Manifold ContDiff
open BlowupTowers BlowupTowerTransforms RestrictEmptyTower HironakaG3EmptyAwareHistory
  HironakaStageCenters HironakaG8OccupiedSlotComparison

/-- The object and literal finite tower over one fixed source. -/
abbrev TowerAt {n : ℕ} (X : CMfd.{0} n) := Σ Y : CMfd.{0} n, BlowupTower X Y

/-- The exact original footprints in raw order, including empty slots. -/
def footprints {n : ℕ} {X : CMfd.{0} n} (T : TowerAt X) : List (Set X) :=
  (List.range T.2.length).map (slotFootprint T.2)

/-- The smaller chart's raw list embedded into the larger source. -/
def footprintsIn {n : ℕ} {X : CMfd.{0} n} {U : Opens X}
    (T : TowerAt (CMfd.of (n := n) U)) : List (Set X) :=
  (footprints T).map (Subtype.val '' ·)

/-- Exact cofinal-chart relation with the literal restricted larger tower. -/
def LiteralNestedTower {n : ℕ} {X : CMfd.{0} n} (U : Opens X)
    (L : TowerAt X) (S : TowerAt (CMfd.of (n := n) U)) : Prop :=
  StageCentres (fun _ C => C.Nonempty) S.2 ∧
    ∃ e : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage L.2 U),
      EmptyAwareTowerIso
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        S.2 (restrict U L.2) e

/-- Footprints read by the smaller source are literal intersections with
its open, so visibility is tested after taking that trace. -/
def footprintTraces {n : ℕ} {X : CMfd.{0} n} (U : Opens X) (T : TowerAt X) : List (Set X) :=
  (footprints T).map (fun A => A ∩ (U : Set X))

/-- True exactly when a footprint trace meets the open. -/
noncomputable def visibleTrace {X : Type*} (A : Set X) : Bool := by
  classical
  exact decide A.Nonempty

/-- Apply the indexed conditional lifting theorem to actual finite towers.
The supplied move relations may record the exact geometric indexed move,
including any additional properties of the exchanged towers. -/
theorem lift_nested_tower_word {n : ℕ} {X : CMfd.{0} n} (U : Opens X)
    (largeMove : ℕ → TowerAt X → TowerAt X → Prop)
    (smallMove : ℕ → TowerAt (CMfd.of (n := n) U) → TowerAt (CMfd.of (n := n) U) → Prop)
    (largeRead : ∀ {i L M}, largeMove i L M →
      SwapAt Disjoint i (footprintTraces U L) (footprintTraces U M))
    (nestedMove : ∀ {i L M S}, largeMove i L M → LiteralNestedTower U L S →
      footprintsIn S = (footprintTraces U L).filter visibleTrace →
      if ((footprintTraces U L)[i]?.any visibleTrace &&
          (footprintTraces U L)[i+1]?.any visibleTrace) then
        ∃ T, smallMove (((footprintTraces U L).take i).filter visibleTrace).length S T ∧
          LiteralNestedTower U M T ∧ footprintsIn T = (footprintTraces U M).filter visibleTrace
      else LiteralNestedTower U M S)
    {w : List ℕ} {L M : TowerAt X} (h : RealizedWord largeMove w L M)
    {S : TowerAt (CMfd.of (n := n) U)} (hComp : LiteralNestedTower U L S)
    (hRead : footprintsIn S = (footprintTraces U L).filter visibleTrace) :
    ∃ (v : List ℕ) (T : TowerAt (CMfd.of (n := n) U)), v.length ≤ w.length ∧
      RealizedWord smallMove v S T ∧ SwapWord Disjoint v (footprintsIn S) (footprintsIn T) ∧
      LiteralNestedTower U M T ∧ footprintsIn T = (footprintTraces U M).filter visibleTrace :=
  lift_realized_word visibleTrace (footprintTraces U) footprintsIn largeMove smallMove
    (LiteralNestedTower U) largeRead nestedMove h hComp hRead

end
end Hironaka.HironakaG8NestedVisibleWordLift
