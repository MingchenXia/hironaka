import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

/-! Actual local readbacks that force unbounded height in the three-stage sheet schedule. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ThreeStageSheetHeight

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3EmptyAwareHistory
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8SpatialCofinalPrecedence HironakaG8StageRankCoherence

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Two ordered local steps hitting one sheet point witness a real
spatial edge in the containing cofinal chart. -/
theorem spatialBefore_of_same_point_on_restricted_sheet
    (i : ℕ) (V : Opens (c i).U) {Y : CMfd.{0} n}
    {S : BlowupTower (CMfd.of (n := n) V) Y}
    {e : Y ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage (c i).T V)}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) V) ∞)
      S (restrict V (c i).T) e)
    (p q : {k // Occupied S k}) (hpq : p.val < q.val)
    (x : V) (hp : x ∈ slotFootprint S p.val) (hq : x ∈ slotFootprint S q.val) :
    SpatialBefore E
      (E.event i (occupiedLiftOnOpen V (c i).T h p))
      (E.event i (occupiedLiftOnOpen V (c i).T h q)) := by
  let lift := occupiedLiftOnOpen V (c i).T h
  have hHit (r : {k // Occupied S k}) (hr : x ∈ slotFootprint S r.val) :
      x.val.val ∈ chartSlotFootprint (c i) (lift r) := by
    have hTrace := slotFootprint_occupiedComparison h r
    rw [slotFootprint_restrict] at hTrace
    have hr' : x.val ∈ slotFootprint (c i).T (lift r).val := by
      rw [hTrace] at hr
      exact hr
    exact ⟨x.val,hr',rfl⟩
  exact ⟨i,lift p,lift q,rfl,rfl,lift.strictMono hpq,x.val.val,hHit p hp,hHit q hq⟩

/-- In sheet k+1, the first two occupied stages are represented by
leaves k,k+1, and the third by the common terminal event. All three
hit the same original point on the literal sheet open. -/
def HasThreeStageSheetReadback (leaf : ℕ → ι) (terminal : ι) (k : ℕ) : Prop :=
  ∃ (i : ℕ) (V : Opens (c i).U) (Y : CMfd.{0} n)
    (S : BlowupTower (CMfd.of (n := n) V) Y)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage (c i).T V))
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) V) ∞)
      S (restrict V (c i).T) e)
    (p q r : {l // Occupied S l}) (x : V),
    p.val < q.val ∧ q.val < r.val ∧
    x ∈ slotFootprint S p.val ∧ x ∈ slotFootprint S q.val ∧ x ∈ slotFootprint S r.val ∧
    E.event i (occupiedLiftOnOpen V (c i).T h p) = leaf k ∧
    E.event i (occupiedLiftOnOpen V (c i).T h q) = leaf (k+1) ∧
    E.event i (occupiedLiftOnOpen V (c i).T h r) = terminal

/-- A genuinely realized three-stage sheet schedule rules out even a
weak spatial rank on that physical cofinal atlas. -/
theorem no_weak_rank_of_three_stage_sheet_readbacks
    (leaf : ℕ → ι) (terminal : ι) (h : ∀ k, HasThreeStageSheetReadback E leaf terminal k) :
    ¬ ∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  have hEdges (k : ℕ) : SpatialBefore E (leaf k) (leaf (k+1)) ∧
      SpatialBefore E (leaf (k+1)) terminal := by
    obtain ⟨i,V,Y,S,e,hIso,p,q,r,x,hpq,hqr,hp,hq,hr,hP,hQ,hR⟩ := h k
    have hLeft := spatialBefore_of_same_point_on_restricted_sheet E i V hIso p q hpq x hp hq
    have hRight := spatialBefore_of_same_point_on_restricted_sheet E i V hIso q r hqr x hq hr
    rw [hP,hQ] at hLeft
    rw [hQ,hR] at hRight
    exact ⟨hLeft,hRight⟩
  have hChain (k : ℕ) : DependencyPath (SpatialBefore E) k (leaf k) := by
    induction k with
    | zero => exact .nil _
    | succ k ih => exact .step (hEdges k).1 ih
  intro hRank
  obtain ⟨cap,hCap⟩ := (exists_natural_rank_iff _).mp hRank terminal
  exact (Nat.not_succ_le_self (cap+1))
    (Nat.le_trans (hCap _ (.step (hEdges cap).2 (hChain (cap+1)))) (Nat.le_succ cap))

end Hironaka.HironakaG8ThreeStageSheetHeight
