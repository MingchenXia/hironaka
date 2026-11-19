import Hironaka.Resolution.HironakaG8FiniteParallelGeometry
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG8RankedTestCompression
import Hironaka.Resolution.HironakaG8DisjointWordLocalCover

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8FiniteParallelTest

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  MarkedIdealBiholomorphism.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8FiniteParallelGeometry HironakaG8EmptyAwareTestTransport HironakaG8RankedTestCompression
  HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry HironakaG8FirstFootprintOrder
  HironakaG8DisjointWordLocalCover ResolutionInvariantDriver MarkedIdealOperationsAlong.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem blockCentre_restrict (T : BlowupTower X Y) (U : Opens X) :
    blockCentre (restrict U T) = (Subtype.val : U → X) ⁻¹' blockCentre T := by
  simp only [blockCentre,slotFootprint_restrict,preimage_iUnion]

private theorem blockCentre_as_occupied (T : BlowupTower X Y) :
    blockCentre T = ⋃ C ∈ occupiedFootprints T, C := by
  ext x
  simp only [blockCentre,mem_iUnion,occupiedFootprints,List.mem_map,mem_occupiedSlots]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨slotFootprint T i,⟨i,(slotFootprint_nonempty_iff T i).mp ⟨x,hi⟩,rfl⟩,hi⟩
  · rintro ⟨C,⟨i,_,rfl⟩,hi⟩
    exact ⟨i,hi⟩

private theorem admissible_block_of_length_le_one (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), T.length ≤ 1 → IsGeoTestTower M T →
      M.IsAdmissibleCentre (blockCentre T)
  | _, .refl, _, _ => by simpa [blockCentre,slotFootprint] using M.isAdmissibleCentre_empty
  | _, .step .refl D q hq, _, hT => by
      have hd : blockCentre (.step .refl D q hq) = D := by
        ext x
        simp only [blockCentre,mem_iUnion]
        constructor
        · rintro ⟨i,hi⟩
          by_cases h : i = 0
          · simpa [slotFootprint,h] using hi
          · simp [slotFootprint,h] at hi
        · intro hx
          exact ⟨0,by simpa [slotFootprint] using hx⟩
      rw [hd]
      exact ((isGeoTestTower_step_iff M _ _ _ hq).mp hT).2
  | _, .step (.step P C π hπ) D q hq, hLen, _ => by
      simp at hLen

private theorem admissible_block_of_at_most_one_occupied
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hSingle : ∀ i j, Occupied T i → Occupied T j → i = j) :
    M.IsAdmissibleCentre (blockCentre T) := by
  obtain ⟨Z,Q,e,hOcc,_,hCmp,hTest⟩ := test_empty_free_compression M hM T
  have hLen : Q.length ≤ 1 := by
    by_contra! h
    let i : {j // Occupied Q j} := ⟨0,occupied_of_empty_free Q hOcc ⟨0,by omega⟩⟩
    let j : {j // Occupied Q j} := ⟨1,occupied_of_empty_free Q hOcc ⟨1,by omega⟩⟩
    let χ := occupiedComparison hCmp
    have hSame : χ i = χ j := Subtype.ext (hSingle _ _ (χ i).property (χ j).property)
    exact (by decide : (0 : ℕ) ≠ 1) (congrArg Subtype.val (χ.injective hSame))
  have he : occupiedFootprints Q = occupiedFootprints T := by
    simpa only [Diffeomorph.coe_refl,preimage_id,List.map_id'] using occupiedFootprints_emptyAware hCmp
  have hCentre : blockCentre Q = blockCentre T := by
    rw [blockCentre_as_occupied Q,blockCentre_as_occupied T,he]
  rw [← hCentre]
  exact admissible_block_of_length_le_one M Q hLen (hTest.mpr hT)

/-- Disjoint projected footprints make the union admissible for the original
marked record. Near each point all but one relevant slot have empty trace. -/
theorem blockCentre_admissible_of_disjoint
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hDisj : ∀ i j, i < j → j < T.length → Disjoint (slotFootprint T i) (slotFootprint T j)) :
    M.IsAdmissibleCentre (blockCentre T) := by
  classical
  apply isAdmissibleCentre_of_forall_exists_opens (hol_of_isCoherent hM.isCoherent)
  intro x
  let Bad (i : Fin T.length) : Set X :=
    if x ∈ slotFootprint T i.val then ∅ else slotFootprint T i.val
  have hClosed (i : Fin T.length) : IsClosed (Bad i) := by
    unfold Bad
    split
    · exact isClosed_empty
    · exact isClosed_slotFootprint T i.val
  let U : Opens X := ⟨(⋃ i, Bad i)ᶜ,(isClosed_iUnion_of_finite hClosed).isOpen_compl⟩
  have hx : x ∈ U := by
    intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    by_cases hxi : x ∈ slotFootprint T i.val <;> simp [Bad,hxi] at hi
  have hHit i (hi : Occupied (restrict U T) i) : x ∈ slotFootprint T i := by
    have hiL := occupied_lt_length T (occupied_of_restrict U T hi)
    obtain ⟨y,hy⟩ := (occupied_restrict_iff_slotFootprint_meets T U i).mp hi
    by_contra hMiss
    apply hy.2
    exact mem_iUnion.mpr ⟨⟨i,hiL⟩,by simpa [Bad,hMiss] using hy.1⟩
  have hSingle i j (hi : Occupied (restrict U T) i) (hj : Occupied (restrict U T) j) : i = j := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (Set.disjoint_left.mp (hDisj _ _ hlt (hit_slot_lt_length T (hHit j hj)))
        (hHit i hi) (hHit j hj)).elim
    · exact heq
    · exact (Set.disjoint_left.mp (hDisj _ _ hgt (hit_slot_lt_length T (hHit i hi)))
        (hHit j hj) (hHit i hi)).elim
  let MU := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M
  have hMU : MU.IsWellFormed := IsWellFormed.pullback_val hM U
  have hTU : IsGeoTestTower MU (restrict U T) :=
    isGeoTestTower_restrict U hM.isClosedSubmanifold_N hM.isCoherent T hT
  refine ⟨U,hx,?_⟩
  rw [← blockCentre_restrict T U]
  exact admissible_block_of_at_most_one_occupied MU hMU (restrict U T) hTU hSingle

/-- Compress a finite disjoint intrinsic TEST block to one actual TEST
blowup on its original terminal object and map, with singular union centre. -/
theorem grouped_finite_disjoint_test
    (W : Set X) (hW : IsClosed W) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hDisj : ∀ i j, i < j → j < T.length → Disjoint (slotFootprint T i) (slotFootprint T j)) :
    ∃ h : IsBlowupAlong n (blockCentre T) T.proj,
      IsGeoTestTower M (.step .refl (blockCentre T) T.proj h) ∧
      blockCentre T ⊆ singularSet (n := n) W := by
  let h := isBlowupAlong_blockCentre_of_disjoint T hDisj
  exact ⟨h,(isGeoTestTower_step_iff M _ _ _ h).mpr
    ⟨trivial,blockCentre_admissible_of_disjoint M hM T hT hDisj⟩,
    blockCentre_subset_singular hW T hDisj hStage⟩

end Hironaka.HironakaG8FiniteParallelTest
