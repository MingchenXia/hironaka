import Hironaka.Resolution.HironakaG8ConsecutiveNestedReorderings
import Hironaka.Resolution.HironakaG8CofinalRoundFootprints
import Hironaka.Resolution.HironakaG8OrderedFootprintTraces
import Hironaka.Resolution.HironakaG8ReorderedComparisonRank
import Hironaka.Resolution.HironakaG8RankedNestedGlobalTest

/-! Exact labels of packed weak-rank chart rounds. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable
namespace Hironaka.HironakaG8PackedRoundRanks

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons HironakaG3EmptyAwareHistory
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8OccupiedSlotComparison HironakaG8OrderedFootprintTraces HironakaG8ReorderedComparisonRank
  HironakaG8CofinalRoundFootprints HironakaG8RankedNestedGlobalTest HironakaG8ConsecutiveNestedReorderings

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)

private theorem same_sorted_nat_list (l m : List ℕ)
    (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·)) (hMem : ∀ a, a ∈ l ↔ a ∈ m) :
    l = m :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba)
    (hl.imp Nat.le_of_lt) (hm.imp Nat.le_of_lt)
    ((List.perm_ext_iff_of_nodup (hl.imp Nat.ne_of_lt) (hm.imp Nat.ne_of_lt)).mpr hMem)

/-- Labels visible in the smaller chart are exactly the surviving labels
of the larger chart, in the same increasing order. -/
theorem packed_round_labels_eq_filter
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (order : ℕ → List ℕ)
    (hSorted : ∀ i, (order i).Pairwise (· < ·))
    (hPresent : ∀ i k, k ∈ order i ↔ (chartRoundFootprint E rank k i).Nonempty)
    {i j : ℕ} (hij : i ≤ j) :
    order i = (order j).filter (fun k => decide (chartRoundFootprint E rank k i).Nonempty) := by
  classical
  apply same_sorted_nat_list _ _ (hSorted i) ((hSorted j).filter _)
  intro k
  simp only [List.mem_filter,decide_eq_true_eq]
  constructor
  · intro h
    have hSmall := (hPresent i k).mp h
    refine ⟨(hPresent j k).mpr ?_,hSmall⟩
    obtain ⟨x,hx⟩ := hSmall
    have hGlobal : x.val ∈ cofinalRoundFootprint E rank k := by
      have hEq := cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k i
      change x ∈ (Subtype.val : (c i).U → X) ⁻¹' cofinalRoundFootprint E rank k
      rwa [hEq]
    let y : (c j).U := ⟨x.val,hMono hij x.property⟩
    refine ⟨y,?_⟩
    rw [← cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k j]
    exact hGlobal
  · exact fun h => (hPresent i k).mpr h.2

variable {A : ℕ → CMfd.{0} n}

/-- Exact physical footprint readback of packed rounds agrees on
nested charts after removing absent rounds. -/
theorem packed_round_occupiedFootprint_traces_agree
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (order : ℕ → List ℕ) (hSorted : ∀ i, (order i).Pairwise (· < ·))
    (hPresent : ∀ i k, k ∈ order i ↔ (chartRoundFootprint E rank k i).Nonempty)
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (hRead : ∀ i l k, (order i)[l]? = some k → slotFootprint (R i) l = chartRoundFootprint E rank k i)
    (hOcc : ∀ i l, (slotFootprint (R i) l).Nonempty ↔ l < (order i).length)
    {i j : ℕ} (hij : i ≤ j) :
    (occupiedFootprints (R i)).map (fun F => (Subtype.val : (c i).U → X) '' F) =
      ((occupiedFootprints (R j)).map (fun F => (Subtype.val : (c j).U → X) '' F)).filterMap
        (fun F => if (F ∩ ((c i).U : Set X)).Nonempty then some (F ∩ ((c i).U : Set X)) else none) := by
  classical
  let F (k t : ℕ) := cofinalRoundFootprint E rank k ∩ ((c t).U : Set X)
  have hReal (t : ℕ) : (occupiedFootprints (R t)).map (fun Q => (Subtype.val : (c t).U → X) '' Q) =
      (order t).map (fun k => F k t) := by
    rw [occupiedFootprints_eq_map_of_exact_slots (R t) (order t)
      (fun k => chartRoundFootprint E rank k t) (hRead t) (hOcc t),List.map_map]
    exact List.map_congr_left fun k _ =>
      (cofinalRoundFootprint_inter_chart_eq E cmp hMono hLift rank k t).symm
  have hVis (k : ℕ) : (F k i).Nonempty ↔ (chartRoundFootprint E rank k i).Nonempty := by
    change (cofinalRoundFootprint E rank k ∩ ((c i).U : Set X)).Nonempty ↔ _
    rw [cofinalRoundFootprint_inter_chart_eq E cmp hMono hLift rank k i]
    exact Set.image_nonempty
  have hTrace (k : ℕ) : F k j ∩ ((c i).U : Set X) = F k i := by
    simp only [F,inter_assoc,inter_eq_right.mpr (hMono hij)]
  rw [hReal i,hReal j,packed_round_labels_eq_filter E cmp hMono hLift rank order hSorted hPresent hij]
  generalize order j = labels
  induction labels with
  | nil => rfl
  | cons k l ih =>
    by_cases hk : (chartRoundFootprint E rank k i).Nonempty
    · have hk' := (hVis k).mpr hk
      simp [hk,hk',hTrace,ih]
    · have hk' := mt (hVis k).mp hk
      simp [hk,hk',hTrace,ih]


/-- The occupied physical subslots carry the exact labels of the
restricted larger tower in increasing rank order. -/
theorem round_rank_preserved_by_nested_comparison
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (order : ℕ → List ℕ) (hSorted : ∀ i, (order i).Pairwise (· < ·))
    (hPresent : ∀ i k, k ∈ order i ↔ (chartRoundFootprint E rank k i).Nonempty)
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (hRead : ∀ i l k, (order i)[l]? = some k → slotFootprint (R i) l = chartRoundFootprint E rank k i)
    (hOcc : ∀ i l, (slotFootprint (R i) l).Nonempty ↔ l < (order i).length)
    {i j : ℕ}
    {f : CMfd.of (n := n) (c i).U ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens (c j).U (c i).U)}
    (hf : ∀ x : (c i).U, (f x).val.val = x.val)
    {e : A i ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (R j) (nestedOpens (c j).U (c i).U))}
    (h : EmptyAwareTowerIso f (R i) (restrict (nestedOpens (c j).U (c i).U) (R j)) e) :
    ∀ p, listedOccupiedEvent (R i) (order i) (hOcc i) p =
      listedOccupiedEvent (R j) (order j) (hOcc j)
        (occupiedLiftOnOpen (nestedOpens (c j).U (c i).U) (R j) h p) := by
  let V := nestedOpens (c j).U (c i).U
  let label (t : ℕ) := listedOccupiedEvent (R t) (order t) (hOcc t)
  have hLabel (t : ℕ) (p : {k // Occupied (R t) k}) :
      slotFootprint (R t) p.val = chartRoundFootprint E rank (label t p) t := by
    apply hRead
    rw [List.getElem?_eq_getElem ((hOcc _ _).mp ((slotFootprint_nonempty_iff (R t) _).mpr p.property))]
    rfl
  have hListed (t : ℕ) {k : ℕ} (hk : k ∈ order t) : ∃ p, label t p = k := by
    obtain ⟨l,hl⟩ := List.mem_iff_get.mp hk
    exact ⟨⟨l.val,(slotFootprint_nonempty_iff (R t) _).mp ((hOcc _ _).mpr l.isLt)⟩,hl⟩
  have hTrace (k : ℕ) : (chartRoundFootprint E rank k i).Nonempty ↔
      (chartRoundFootprint E rank k j ∩ (V : Set (c j).U)).Nonempty := by
    rw [chartRoundFootprint_nested_eq E cmp hMono hLift rank k i j f hf]
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨(f x).val,hx,(f x).property⟩
    · rintro ⟨y,hy,hyV⟩
      obtain ⟨x,hx⟩ := f.surjective ⟨y,hyV⟩
      change f x = ⟨y,hyV⟩ at hx
      exact ⟨x,by change (f x).val ∈ chartRoundFootprint E rank k j; rwa [hx]⟩
  let right := label j ∘ occupiedRestrictionEmbedding V (R j)
  have hRange : range (label i) = range right := by
    ext k
    constructor
    · rintro ⟨p,rfl⟩
      have hp := ((slotFootprint_nonempty_iff (R i) _).mpr p.property)
      rw [hLabel i p] at hp
      obtain ⟨y,hy,hyV⟩ := (hTrace (label i p)).mp hp
      have hRound : (chartRoundFootprint E rank (label i p) j).Nonempty := ⟨y,hy⟩
      obtain ⟨q,hq⟩ := hListed j ((hPresent j _).mpr hRound)
      have hqV : Occupied (restrict V (R j)) q.val := by
        apply (occupied_restrict_iff_slotFootprint_meets (R j) V q.val).mpr
        exact ⟨y,by rwa [hLabel j q,hq],hyV⟩
      exact ⟨⟨q.val,hqV⟩,hq⟩
    · rintro ⟨p,rfl⟩
      let q := occupiedRestrictionEmbedding V (R j) p
      obtain ⟨y,hy,hyV⟩ := (occupied_restrict_iff_slotFootprint_meets (R j) V p.val).mp p.property
      have hy' : y ∈ chartRoundFootprint E rank (label j q) j := by
        rw [← hLabel j q]
        exact hy
      exact hListed i ((hPresent i _).mpr ((hTrace _).mpr ⟨y,hy',hyV⟩))
  have hLeft : StrictMono (label i) := strictMono_listedRank (R i) (order i) (hOcc i) id (hSorted i)
  have hRight : StrictMono right :=
    (strictMono_listedRank (R j) (order j) (hOcc j) id (hSorted j)).comp (occupiedRestrictionEmbedding V (R j)).strictMono
  have hTransport : range (right ∘ occupiedComparison h) = range right := by
    rw [Set.range_comp,(occupiedComparison h).surjective.range_eq,Set.image_univ]
  have hSame := (StrictMono.range_inj hLeft (hRight.comp (occupiedComparison h).strictMono)).mp
    (hRange.trans hTransport.symm)
  intro p
  exact congrFun hSame p

/-- The actual packed nested comparison has the rank condition used by
the padded global assembler. -/
theorem nestedRankComparison_of_packed_rounds
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (order : ℕ → List ℕ) (hSorted : ∀ i, (order i).Pairwise (· < ·))
    (hPresent : ∀ i k, k ∈ order i ↔ (chartRoundFootprint E rank k i).Nonempty)
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (hRead : ∀ i l k, (order i)[l]? = some k → slotFootprint (R i) l = chartRoundFootprint E rank k i)
    (hOcc : ∀ i l, (slotFootprint (R i) l).Nonempty ↔ l < (order i).length)
    {i j : ℕ} (hij : i ≤ j) (hNested : NestedGeometry (R i) (R j)) :
    NestedRankComparison (O := (c i).U ⊓ (c j).U) (R i) (R j)
      (listedOccupiedEvent (R i) (order i) (hOcc i))
      (listedOccupiedEvent (R j) (order j) (hOcc j)) := by
  rw [inf_eq_left.mpr (hMono hij)]
  obtain ⟨f,hf,e,h⟩ := hNested
  exact ⟨f,hf,e,h,round_rank_preserved_by_nested_comparison E cmp hMono hLift rank order
    hSorted hPresent R hRead hOcc hf h⟩

end Hironaka.HironakaG8PackedRoundRanks
