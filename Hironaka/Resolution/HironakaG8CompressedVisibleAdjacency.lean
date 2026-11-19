import Hironaka.Resolution.HironakaG8RankedTestCompression

/-! Raw adjacency after literal open restriction and empty-free compression. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompressedVisibleAdjacency

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaStageCenters HironakaG8RankedTestCompression HironakaG8OccupiedSlotComparison
  HironakaG8CofinalOccupiedAncestry HironakaG3EmptyAwareHistory

variable {n : ℕ} {X Y Z : CMfd.{0} n}
variable (T : BlowupTower X Y) (U : Opens X)
  {Q : BlowupTower (CMfd.of (n := n) U) Z}
  {e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
    CMfd.of (n := n) (openPreimage T U)}
  (hQ : StageCentres (fun _ C => C.Nonempty) Q)
  (h : EmptyAwareTowerIso
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) Q (restrict U T) e)

/-- The compressed clock embeds into the original occupied clock using the
actual open restriction. Membership in the image means visibility on the open. -/
noncomputable def compressedVisibleSlots : Fin Q.length ↪o {i // Occupied T i} :=
  (compressedRawOccupiedIso hQ h).toOrderEmbedding.trans (occupiedRestrictionEmbedding U T)

theorem compressedVisibleSlots_range {k : ℕ} (hk : Occupied T k) :
    (⟨k,hk⟩ : {i // Occupied T i}) ∈ Set.range (compressedVisibleSlots T U hQ h) ↔
      (slotFootprint T k ∩ (U : Set X)).Nonempty := by
  constructor
  · rintro ⟨i,hi⟩
    have hv := (compressedRawOccupiedIso hQ h i).property
    have he := congrArg Subtype.val hi
    change (compressedRawOccupiedIso hQ h i).val = k at he
    exact (occupied_restrict_iff_slotFootprint_meets T U k).mp (he ▸ hv)
  · intro hVisible
    have hOcc := (occupied_restrict_iff_slotFootprint_meets T U k).mpr hVisible
    obtain ⟨i,hi⟩ := (compressedRawOccupiedIso hQ h).surjective ⟨k,hOcc⟩
    refine ⟨i,Subtype.ext ?_⟩
    change (compressedRawOccupiedIso hQ h i).val = k
    exact congrArg Subtype.val hi

theorem compressedVisibleSlots_footprint (i : Fin Q.length) :
    slotFootprint Q i.val =
      (Subtype.val : U → X) ⁻¹' slotFootprint T (compressedVisibleSlots T U hQ h i).val := by
  rw [slotFootprint_compressedRawOccupiedIso hQ h,slotFootprint_restrict]
  rfl

/-- Two ordered compressed slots are consecutive exactly when every
strictly intermediate original raw slot misses the restriction open. -/
theorem compressedVisibleSlots_adjacent_iff {i j : Fin Q.length} (hij : i < j) :
    j.val = i.val + 1 ↔
      ∀ k : ℕ, (compressedVisibleSlots T U hQ h i).val < k →
        k < (compressedVisibleSlots T U hQ h j).val →
        ¬ (slotFootprint T k ∩ (U : Set X)).Nonempty := by
  let f := compressedVisibleSlots T U hQ h
  change j.val = i.val + 1 ↔ ∀ k, (f i).val < k → k < (f j).val → _
  constructor
  · intro hNext k hi hj hVisible
    have hK : Occupied T k := occupied_of_restrict U T
      ((occupied_restrict_iff_slotFootprint_meets T U k).mpr hVisible)
    obtain ⟨u,hu⟩ := (compressedVisibleSlots_range T U hQ h hK).mpr hVisible
    have hiu : i < u := f.lt_iff_lt.mp (by rw [hu]; exact hi)
    have huj : u < j := f.lt_iff_lt.mp (by rw [hu]; exact hj)
    change i.val < u.val at hiu
    change u.val < j.val at huj
    omega
  · intro hNo
    by_contra hNext
    have hlt : i.val + 1 < j.val := by
      change i.val < j.val at hij
      omega
    let u : Fin Q.length := ⟨i.val+1,hlt.trans j.isLt⟩
    have hi : i < u := Nat.lt_succ_self _
    have hj : u < j := hlt
    exact hNo _ (f.strictMono hi) (f.strictMono hj)
      ((compressedVisibleSlots_range T U hQ h (f u).property).mp ⟨u,rfl⟩)

theorem visibleEndpoints_compressed_adjacent_iff {a b : ℕ}
    (hab : a < b)
    (ha : (slotFootprint T a ∩ (U : Set X)).Nonempty)
    (hb : (slotFootprint T b ∩ (U : Set X)).Nonempty) :
    let i := (compressedRawOccupiedIso hQ h).symm
      ⟨a,(occupied_restrict_iff_slotFootprint_meets T U a).mpr ha⟩
    let j := (compressedRawOccupiedIso hQ h).symm
      ⟨b,(occupied_restrict_iff_slotFootprint_meets T U b).mpr hb⟩
    (compressedVisibleSlots T U hQ h i).val = a ∧
      (compressedVisibleSlots T U hQ h j).val = b ∧
      (j.val = i.val + 1 ↔ ∀ k, a < k → k < b →
        ¬ (slotFootprint T k ∩ (U : Set X)).Nonempty) := by
  intro i j
  have hi : (compressedVisibleSlots T U hQ h i).val = a :=
    congrArg Subtype.val ((compressedRawOccupiedIso hQ h).apply_symm_apply _)
  have hj : (compressedVisibleSlots T U hQ h j).val = b :=
    congrArg Subtype.val ((compressedRawOccupiedIso hQ h).apply_symm_apply _)
  have hij : i < j := (compressedVisibleSlots T U hQ h).lt_iff_lt.mp (by
    change (compressedVisibleSlots T U hQ h i).val < (compressedVisibleSlots T U hQ h j).val
    rwa [hi,hj])
  refine ⟨hi,hj,?_⟩
  simpa only [hi,hj] using compressedVisibleSlots_adjacent_iff T U hQ h hij

end Hironaka.HironakaG8CompressedVisibleAdjacency
#print axioms Hironaka.HironakaG8CompressedVisibleAdjacency.compressedVisibleSlots
#print axioms Hironaka.HironakaG8CompressedVisibleAdjacency.compressedVisibleSlots_range
#print axioms Hironaka.HironakaG8CompressedVisibleAdjacency.compressedVisibleSlots_footprint
#print axioms Hironaka.HironakaG8CompressedVisibleAdjacency.compressedVisibleSlots_adjacent_iff
#print axioms Hironaka.HironakaG8CompressedVisibleAdjacency.visibleEndpoints_compressed_adjacent_iff
