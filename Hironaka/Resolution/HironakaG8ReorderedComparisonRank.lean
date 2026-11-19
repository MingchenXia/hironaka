import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence
import Mathlib.Order.Hom.Set

/-! Event identities survive actual nested comparisons of ranked reorderings. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ReorderedComparisonRank

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3EmptyAwareHistory MaxLocusLocal HironakaG8CofinalOccupiedAncestry
  HironakaG8OccupiedSlotComparison HironakaG8PhysicalChartOccupiedLifts
  G3UniversePhysicalClassComparisons HironakaG8SpatialCofinalPrecedence

variable {n : ℕ} {A B : CMfd.{0} n} {ι : Type*}

/-- The original occurrence listed at a physically occupied slot of a reordered tower. -/
def listedOccupiedEvent (R : BlowupTower A B) (order : List ι)
    (hOcc : ∀ j, (slotFootprint R j).Nonempty ↔ j < order.length)
    (p : {j // Occupied R j}) : ι :=
  order.get ⟨p.val, (hOcc _).mp ((slotFootprint_nonempty_iff R _).mpr p.property)⟩

private theorem listedOccupiedEvent_getElem? (R : BlowupTower A B) (order : List ι)
    (hOcc : ∀ j, (slotFootprint R j).Nonempty ↔ j < order.length)
    (p : {j // Occupied R j}) :
    order[p.val]? = some (listedOccupiedEvent R order hOcc p) := by
  rw [List.getElem?_eq_getElem ((hOcc _).mp ((slotFootprint_nonempty_iff R _).mpr p.property))]
  rfl

private theorem exists_listedOccupiedEvent (R : BlowupTower A B) (order : List ι)
    (hOcc : ∀ j, (slotFootprint R j).Nonempty ↔ j < order.length)
    {a : ι} (ha : a ∈ order) :
    ∃ p, listedOccupiedEvent R order hOcc p = a := by
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp ha
  refine ⟨⟨k.val,(slotFootprint_nonempty_iff R _).mp ((hOcc _).mpr k.isLt)⟩,?_⟩
  exact hk

theorem strictMono_listedRank (R : BlowupTower A B) (order : List ι)
    (hOcc : ∀ j, (slotFootprint R j).Nonempty ↔ j < order.length)
    (rank : ι → ℕ) (hSorted : order.Pairwise (fun a b => rank a < rank b)) :
    StrictMono (rank ∘ listedOccupiedEvent R order hOcc) := by
  intro p q hpq
  exact List.pairwise_iff_get.mp hSorted _ _ hpq

variable {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P}

/-- If two ranked reorderings have an actual empty-aware comparison over a
nested open, its ordered occupied match preserves the original event rank. -/
theorem rank_preserved_by_reordered_comparison
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    {Y : ℕ → CMfd.{0} n} (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (Y i))
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length)
    {i j : ℕ} (hij : i ≤ j) :
    let V := nestedOpens (c j).U ((c i).U ⊓ (c j).U)
    ∀ {φ : CMfd.of (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of V}
      {ψ : Y i ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (openPreimage (R j) V)}
      (hCmp : EmptyAwareTowerIso φ (R i) (restrict V (R j)) ψ)
      (p : {k // Occupied (R i) k}),
      rank (E.event i (listedOccupiedEvent (R i) (order i) (hOcc i) p)) =
        rank (E.event j (listedOccupiedEvent (R j) (order j) (hOcc j)
          (occupiedLiftOnOpen V (R j) hCmp p))) := by
  dsimp only
  intro φ ψ hCmp p
  let V := nestedOpens (c j).U ((c i).U ⊓ (c j).U)
  let label (k : ℕ) (q : {l // Occupied (R k) l}) := listedOccupiedEvent (R k) (order k) (hOcc k) q
  have hLabel (k : ℕ) (q : {l // Occupied (R k) l}) :
      slotFootprint (R k) q.val = slotFootprint (c k).T (label k q).val :=
    hRead k _ _ (listedOccupiedEvent_getElem? (R k) (order k) (hOcc k) q)
  have hSurj (k : ℕ) : Surjective (label k) := fun a =>
    exists_listedOccupiedEvent (R k) (order k) (hOcc k) (hComplete k a)
  let leftRank := (rank ∘ E.event i) ∘ label i
  let rightRank := ((rank ∘ E.event j) ∘ label j) ∘ occupiedRestrictionEmbedding V (R j)
  have hLeft : StrictMono leftRank := strictMono_listedRank (R i) _ (hOcc i) _ (hSorted i)
  have hRight : StrictMono rightRank :=
    (strictMono_listedRank (R j) _ (hOcc j) _ (hSorted j)).comp
      (occupiedRestrictionEmbedding V (R j)).strictMono
  have hRange : range leftRank = range rightRank := by
    ext r
    constructor
    · rintro ⟨a,rfl⟩
      let b := E.lift hij (label i a)
      obtain ⟨q,hq⟩ := hSurj j b
      obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c i).T _).mpr (label i a).property
      have hxA : x.val ∈ chartSlotFootprint (c i) (label i a) := ⟨x,hx,rfl⟩
      have hTrace := chartSlotFootprint_lift cmp (c i) (c j) (hMono hij) (label i a)
      rw [← hLift hij] at hTrace
      rw [hTrace] at hxA
      obtain ⟨y,hy,hyx⟩ := hxA.1
      have hyV : y ∈ V := ⟨hyx ▸ x.property,y.property⟩
      have hqV : Occupied (restrict V (R j)) q.val := by
        apply (occupied_restrict_iff_slotFootprint_meets (R j) V q.val).mpr
        exact ⟨y,by rwa [hLabel j q,hq],hyV⟩
      refine ⟨⟨q.val,hqV⟩,?_⟩
      change rank (E.event j (label j q)) = rank (E.event i (label i a))
      rw [hq,E.lift_event]
    · rintro ⟨q,rfl⟩
      let b := occupiedRestrictionEmbedding V (R j) q
      obtain ⟨y,hy,hyV⟩ := (occupied_restrict_iff_slotFootprint_meets (R j) V q.val).mp q.property
      change y ∈ slotFootprint (R j) b.val at hy
      rw [hLabel j b] at hy
      have hyC : y.val ∈ (c i).U := hyV.1
      have hEvent : y.val ∈ cofinalEventFootprint E (E.event j (label j b)) :=
        ⟨j,label j b,rfl,y,hy,rfl⟩
      obtain ⟨a,ha,_⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i _ hyC).mp hEvent
      obtain ⟨p,hp⟩ := hSurj i a
      refine ⟨p,?_⟩
      change rank (E.event i (label i p)) = rank (E.event j (label j b))
      rw [hp,ha]
  have hTransport : range (rightRank ∘ occupiedComparison hCmp) = range rightRank := by
    rw [Set.range_comp,(occupiedComparison hCmp).surjective.range_eq,Set.image_univ]
  have hSame := (StrictMono.range_inj hLeft (hRight.comp (occupiedComparison hCmp).strictMono)).mp
    (hRange.trans hTransport.symm)
  exact congrFun hSame p

end Hironaka.HironakaG8ReorderedComparisonRank
