import Hironaka.Resolution.HironakaG8DisjointCentreGrouping
import Hironaka.Resolution.HironakaG8FirstFootprintOrder

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteParallelGeometry

open Hironaka.BlowupSequences BlowupTowers HironakaG8OccupiedSlotComparison
  HironakaG8FirstFootprintOrder HironakaG8DisjointMarkedSwap HironakaG3RSimultaneousBlowup
  HironakaLocalPrincipalization MarkedIdealBiholomorphism HironakaEmbeddedAnalytic
  HironakaStageCenters

variable {n : ℕ} {X : CMfd.{0} n}

/-- All actual projected centres of the finite block, on its initial object. -/
def blockCentre {Y : CMfd.{0} n} (T : BlowupTower X Y) : Set X :=
  ⋃ i, slotFootprint T i

private theorem blockCentre_step {Y Z : CMfd.{0} n} (T : BlowupTower X Y)
    (D : Set Y) (q : Z → Y) (hq : IsBlowupAlong n D q) :
    blockCentre (.step T D q hq) = blockCentre T ∪ T.proj '' D := by
  ext x
  simp only [blockCentre, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i,hi⟩
    by_cases h : i = T.length
    · exact Or.inr (by simpa [slotFootprint,h] using hi)
    · exact Or.inl ⟨i,by simpa [slotFootprint,h] using hi⟩
  · rintro (⟨i,hi⟩ | h)
    · exact ⟨i,by simpa [slotFootprint,ne_of_lt (hit_slot_lt_length T hi)] using hi⟩
    · exact ⟨T.length,by simpa [slotFootprint] using h⟩

private theorem prefix_and_last_disjoint {Y Z : CMfd.{0} n}
    (T : BlowupTower X Y) (D : Set Y) (q : Z → Y) (hq : IsBlowupAlong n D q)
    (hDisj : ∀ i j, i < j → j < (BlowupTower.step T D q hq).length →
      Disjoint (slotFootprint (.step T D q hq) i) (slotFootprint (.step T D q hq) j)) :
    (∀ i j, i < j → j < T.length → Disjoint (slotFootprint T i) (slotFootprint T j)) ∧
      Disjoint (blockCentre T) (T.proj '' D) := by
  constructor
  · intro i j hij hj
    simpa [slotFootprint,ne_of_lt (hij.trans hj),ne_of_lt hj] using
      hDisj i j hij (by simpa using hj.trans (Nat.lt_succ_self T.length))
  · rw [Set.disjoint_left]
    intro x hx hD
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    have hiL := hit_slot_lt_length T hi
    have h := hDisj i T.length hiL (by simp)
    apply (Set.disjoint_left.mp h) (by simpa [slotFootprint,ne_of_lt hiL] using hi)
    simpa [slotFootprint] using hD

/-- A finite block of disjoint projected footprints is a single blowup
along their union, with exactly the original composite projection. -/
theorem isBlowupAlong_blockCentre_of_disjoint :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      (∀ i j, i < j → j < T.length → Disjoint (slotFootprint T i) (slotFootprint T j)) →
      IsBlowupAlong n (blockCentre T) T.proj
  | _, .refl, _ => by
      rw [show blockCentre (.refl : BlowupTower X X) = ∅ by simp [blockCentre,slotFootprint]]
      exact isBlowupAlong_empty_of_inverse contMDiff_id contMDiff_id (fun _ => rfl) (fun _ => rfl)
  | _, .step T D q hq, hDisj => by
      obtain ⟨hPrefix,hApart⟩ := prefix_and_last_disjoint T D q hq hDisj
      have hOld := isBlowupAlong_blockCentre_of_disjoint T hPrefix
      let F := T.proj '' D
      have hPre : T.proj ⁻¹' F = D := preimage_image_eq_of_disjoint_centre hOld D hApart
      have hClosed := closedSubmanifold_of_disjoint_preimage hOld hApart (hPre.symm ▸ hq.1)
      have hInterior : interior F = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨y,rfl⟩ := surjective_of_isBlowupAlong hOld x
        have hOpen : IsOpen (T.proj ⁻¹' interior F) :=
          isOpen_interior.preimage T.contMDiff_proj.continuous
        have hSub : T.proj ⁻¹' interior F ⊆ D := (preimage_mono interior_subset).trans hPre.subset
        have hy := (interior_maximal hSub hOpen) hx
        rw [hq.2.1] at hy
        exact hy
      rw [blockCentre_step]
      exact isBlowupAlong_union_comp hOld hClosed hInterior hApart (hPre.symm ▸ hq)

/-- For a block of intrinsic singular steps, the grouped centre is inside
the singular set on the literal initial object. -/
theorem blockCentre_subset_singular {W : Set X} (hW : IsClosed W) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      (∀ i j, i < j → j < T.length → Disjoint (slotFootprint T i) (slotFootprint T j)) →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      blockCentre T ⊆ singularSet (n := n) W
  | _, .refl, _, _ => by simp [blockCentre,slotFootprint]
  | _, .step T D q hq, hDisj, hStage => by
      obtain ⟨hPrefix,hApart⟩ := prefix_and_last_disjoint T D q hq hDisj
      have hOld := isBlowupAlong_blockCentre_of_disjoint T hPrefix
      rw [blockCentre_step]
      refine union_subset (blockCentre_subset_singular hW T hPrefix hStage.1) ?_
      rintro _ ⟨y,hy,rfl⟩
      exact (singularSet_at_disjoint_second_centre hOld hW hApart
        (show y ∈ T.proj ⁻¹' (T.proj '' D) from ⟨y,hy,rfl⟩)).mp (hStage.2 hy)

end Hironaka.HironakaG8FiniteParallelGeometry
