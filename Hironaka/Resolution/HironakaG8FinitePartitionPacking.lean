import Hironaka.Resolution.HironakaG8ParallelBlocksJoin
import Hironaka.Resolution.HironakaG8DisjointWordLocalCover
import Hironaka.Resolution.HironakaG8NestedVisibleWordLift

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FinitePartitionPacking

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8FiniteParallelGeometry
  HironakaG8FiniteParallelLocalReadback HironakaG8ParallelBlocksJoin
  HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry HironakaG8FirstFootprintOrder
  HironakaG8DisjointWordLocalCover G3UniverseEmptyAwareCore BlowupTowerIsomorphism
  HironakaSharpActualFiniteChronologicalHistory MaxLocusLocal BlowupTowerIsoTail HironakaG8NestedVisibleWordLift

variable {n : ℕ} {X : CMfd.{0} n}

/-- Each entry records the actual union footprint of its literal grouped block. -/
inductive BlockPacking (X : CMfd.{0} n) :
    {Y : CMfd.{0} n} → BlowupTower X Y → BlowupTower X Y → List (Set X) → Prop
  | nil : BlockPacking X .refl .refl []
  | append {A Y : CMfd.{0} n} {P G : BlowupTower X A} {trace : List (Set X)}
      (hPrefix : BlockPacking X P G trace) (T : BlowupTower A Y)
      (hDisj : ∀ i j, i < j → j < T.length →
        Disjoint (P.proj '' slotFootprint T i) (P.proj '' slotFootprint T j))
      (h : IsBlowupAlong n (blockCentre T) T.proj) :
      BlockPacking X (P.append T) (.step G (blockCentre T) T.proj h)
        (trace ++ [P.proj '' blockCentre T])

/-- Forget the pointer to the packed tower, retaining a supplied finite
partition of the original history into successively admissible rank blocks. -/
inductive DisjointPartition (X : CMfd.{0} n) :
    {Y : CMfd.{0} n} → BlowupTower X Y → Prop
  | nil : DisjointPartition X .refl
  | append {A Y : CMfd.{0} n} {P : BlowupTower X A}
      (hPrefix : DisjointPartition X P) (T : BlowupTower A Y)
      (hDisj : ∀ i j, i < j → j < T.length →
        Disjoint (P.proj '' slotFootprint T i) (P.proj '' slotFootprint T j)) :
      DisjointPartition X (P.append T)

/-- A supplied finite block partition is physically grouped on the exact
original sequence of intermediate block endpoints. -/
theorem pack_partition {Y : CMfd.{0} n} {P : BlowupTower X Y}
    (h : DisjointPartition X P) : ∃ G trace, BlockPacking X P G trace := by
  induction h with
  | nil => exact ⟨.refl,[],.nil⟩
  | @append A Y P _ T hDisj ih =>
      obtain ⟨G,trace,hP⟩ := ih
      have hd (i j : ℕ) (hij : i < j) (hj : j < T.length) : Disjoint (slotFootprint T i) (slotFootprint T j) := by
        rw [Set.disjoint_left]
        intro y hyi hyj
        exact Set.disjoint_left.mp (hDisj i j hij hj)
          (mem_image_of_mem _ hyi) (mem_image_of_mem _ hyj)
      exact ⟨_,_,.append hP T hDisj (isBlowupAlong_blockCentre_of_disjoint T hd)⟩

theorem BlockPacking.proj_eq {Y : CMfd.{0} n} {P G : BlowupTower X Y} {trace : List (Set X)}
    (h : BlockPacking X P G trace) : G.proj = P.proj := by
  induction h with
  | nil => rfl
  | append _ T _ _ ih =>
      rw [BlowupTower.proj_step,BlowupTower.proj_append,ih]


private theorem carry_equal_open {A Y : CMfd.{0} n} (S T : BlowupTower A Y)
    (U V : Opens A) (hUV : U = V)
    (h : ∃ e : CMfd.of (n := n) (openPreimage S U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U),
        (∀ y, (e y).val = y.val) ∧
        EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U S) (restrict U T) e) :
    ∃ e : CMfd.of (n := n) (openPreimage S U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T V),
        (∀ y, (e y).val = y.val) ∧
        EmptyAwareTowerIso (opensCongr (n := n) hUV) (restrict U S) (restrict V T) e := by
  subst V
  obtain ⟨e,he,hIso⟩ := h
  have hh : opensCongr (n := n) (rfl : U = U) = Diffeomorph.refl _ _ _ := by
    apply Diffeomorph.ext
    intro y
    apply Subtype.ext
    rfl
  exact ⟨e,he,hh.symm ▸ hIso⟩

/-- Pick a neighborhood seeing at most one slot of this block, even after
passing to the saturated open on the actual prefix endpoint. -/
private theorem exists_isolating_open {A Y : CMfd.{0} n}
    (P : BlowupTower X A) (T : BlowupTower A Y)
    (hDisj : ∀ i j, i < j → j < T.length →
      Disjoint (P.proj '' slotFootprint T i) (P.proj '' slotFootprint T j))
    (x : X) :
    ∃ V : Opens X, x ∈ V ∧ ∀ U : Opens X, U ≤ V →
      ∀ i j, Occupied (restrict (openPreimage P U) T) i →
        Occupied (restrict (openPreimage P U) T) j → i = j := by
  classical
  let F (i : ℕ) := P.proj '' slotFootprint T i
  let Bad (i : Fin T.length) : Set X := if x ∈ F i.val then ∅ else F i.val
  have hClosed (i : Fin T.length) : IsClosed (Bad i) := by
    unfold Bad
    split
    · exact isClosed_empty
    · exact (HironakaLocalPrincipalization.isProperMap_proj P).isClosedMap _
        (isClosed_slotFootprint T i.val)
  let V : Opens X := ⟨(⋃ i, Bad i)ᶜ,(isClosed_iUnion_of_finite hClosed).isOpen_compl⟩
  have hx : x ∈ V := by
    intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    by_cases hxi : x ∈ F i.val <;> simp [Bad,hxi] at hi
  refine ⟨V,hx,?_⟩
  intro U hUV i j hi hj
  have hLength k (hk : Occupied (restrict (openPreimage P U) T) k) : k < T.length :=
    occupied_lt_length T (occupied_of_restrict _ T hk)
  have hHit k (hk : Occupied (restrict (openPreimage P U) T) k) : x ∈ F k := by
    obtain ⟨y,hy⟩ := (occupied_restrict_iff_slotFootprint_meets T (openPreimage P U) k).mp hk
    by_contra hMiss
    have hOut : P.proj y ∈ V := hUV hy.2
    apply hOut
    exact mem_iUnion.mpr ⟨⟨k,hLength k hk⟩,by
      change P.proj y ∈ (if x ∈ F k then ∅ else F k)
      rw [if_neg hMiss]
      exact mem_image_of_mem P.proj hy.1⟩
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (Set.disjoint_left.mp (hDisj _ _ hij (hLength _ hj)) (hHit _ hi) (hHit _ hj)).elim
  · exact hij
  · exact (Set.disjoint_left.mp (hDisj _ _ hji (hLength _ hi)) (hHit _ hj) (hHit _ hi)).elim

/-- The exact local comparisons hold on every smaller open of the chosen window. -/
theorem BlockPacking.local_cover_stable {Y : CMfd.{0} n} {P G : BlowupTower X Y}
    {trace : List (Set X)} (h : BlockPacking X P G trace) (x : X) (O : Opens X) (hx : x ∈ O) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ O ∧
      ∀ V : Opens X, V ≤ U →
      ∃ e : CMfd.of (n := n) (openPreimage P V)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage G V),
        (∀ y, (e y).val = y.val) ∧
        EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict V P) (restrict V G) e := by
  induction h generalizing O with
  | nil =>
      exact ⟨O,hx,le_rfl,fun _ _ => ⟨Diffeomorph.refl _ _ _,fun _ => rfl,
        emptyAware_of_isTowerIso (IsTowerIso.refl_self _)⟩⟩
  | @append A Y P G trace hPrefix T hDisj hπ ih =>
      obtain ⟨V,hxV,hV⟩ := exists_isolating_open P T hDisj x
      obtain ⟨U,hxU,hUV,hB⟩ := ih (O ⊓ V) ⟨hx,hxV⟩
      refine ⟨U,hxU,hUV.trans inf_le_left,?_⟩
      intro Q hQU
      obtain ⟨β,hβ,hPrefixComparison⟩ := hB Q hQU
      let S := BlowupTower.step .refl (blockCentre T) T.proj hπ
      have hOpen : openPreimage P Q = openPreimage G Q := by
        ext y
        change P.proj y ∈ Q ↔ G.proj y ∈ Q
        rw [hPrefix.proj_eq]
      have hBase : β = opensCongr (n := n) hOpen := by
        apply Diffeomorph.ext
        intro y
        apply Subtype.ext
        exact hβ y
      let M : MarkedIdeal n A := geometricTemplate univ []
      have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
        IdealWeightPowers.isCoherent_unitIdeal, NormalCrossings.isSNCDivisor_nil,
        SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor NormalCrossings.isSNCDivisor_nil⟩
      have hStep := local_grouped_step_comparison M hM T hπ (openPreimage P Q)
        (hV Q (hQU.trans (hUV.trans inf_le_right)))
      obtain ⟨χ,hχ,hC⟩ := carry_equal_open T S _ _ hOpen hStep
      rw [← hBase] at hC
      exact append_local_parallel_comparisons Q P G T S hPrefixComparison hC hχ

/-- Local comparison at the selected open of the stable cover. -/
theorem BlockPacking.local_cover {Y : CMfd.{0} n} {P G : BlowupTower X Y}
    {trace : List (Set X)} (h : BlockPacking X P G trace) (x : X) (O : Opens X) (hx : x ∈ O) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ O ∧
      ∃ e : CMfd.of (n := n) (openPreimage P U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage G U),
        (∀ y, (e y).val = y.val) ∧
        EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U P) (restrict U G) e := by
  obtain ⟨U,hxU,hU,hLocal⟩ := h.local_cover_stable x O hx
  exact ⟨U,hxU,hU,hLocal U le_rfl⟩

/-- A supplied disjoint block partition produces an actual regrouping of
the entire original TEST, on its exact original endpoint and projection. -/
theorem pack_partition_preserves_test {Y : CMfd.{0} n} (P : BlowupTower X Y)
    (hP : DisjointPartition X P) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : IsGeoTestTower M P) :
    ∃ G trace, BlockPacking X P G trace ∧ G.proj = P.proj ∧ IsGeoTestTower M G := by
  classical
  obtain ⟨G,trace,hG⟩ := pack_partition hP
  have hLoc (x : X) := hG.local_cover x ⊤ trivial
  choose U hU _ hData using hLoc
  refine ⟨G,trace,hG,hG.proj_eq,grouped_test_of_local_comparisons M hM P G hTest U
    (fun x => ⟨x,hU x⟩) ?_⟩
  intro x
  obtain ⟨e,_,he⟩ := hData x
  exact ⟨e,he⟩


/-- The packed raw footprint list is exactly the list of successive block
unions in the supplied partition certificate. -/
theorem BlockPacking.footprints_eq {Y : CMfd.{0} n} {P G : BlowupTower X Y}
    {trace : List (Set X)} (h : BlockPacking X P G trace) :
    footprints (⟨Y,G⟩ : TowerAt X) = trace := by
  induction h with
  | nil => simp [footprints]
  | @append A Y P G trace hPrefix T hDisj hπ ih =>
      change ((List.range (G.length + 1)).map
        (slotFootprint (.step G (blockCentre T) T.proj hπ))) = _
      rw [List.range_succ,List.map_append]
      have hMap : (List.range G.length).map (slotFootprint (.step G (blockCentre T) T.proj hπ)) =
          (List.range G.length).map (slotFootprint G) := by
        apply List.map_congr_left
        intro i hi
        simp [slotFootprint,ne_of_lt (List.mem_range.mp hi)]
      rw [hMap]
      change footprints (⟨A,G⟩ : TowerAt X) ++ _ = _
      rw [ih]
      simp [slotFootprint,hPrefix.proj_eq]

end Hironaka.HironakaG8FinitePartitionPacking
