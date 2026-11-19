import Hironaka.Resolution.HironakaG8CofinalSpatialRankEndpoint
import Hironaka.Resolution.HironakaG8CofinalRoundFootprints
import Hironaka.Resolution.HironakaG8SortedRankExactPacking

/-! The local rank label groups precisely the literal cofinal round traces. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG8KeyedRoundReadback

open BlowupTowers MarkedIdeals HironakaG3RTowerClass
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8CofinalSpatialRankEndpoint HironakaG8CofinalRoundFootprints
  HironakaG8SortedRankExactPacking

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  {c : ℕ → TowerChart K Z P} {ι κ : Type*} [LinearOrder κ]

/-- The union of sorted physical slots labelled by a round is the
original chart trace of that round. -/
theorem chartRankFootprint_eq
    (E : CofinalEvents c ι) {key : ι → κ} {M : MarkedIdeal n X} {W : Set X}
    (D : CofinalKeyedSingularWords E key M W) (rank : ι → ℕ) (i k : ℕ) :
    rankFootprint (D.R i)
      (fun j => (((D.order i)[j]?).map (fun p => rank (E.event i p))).getD 0) k =
      chartRoundFootprint E rank k i := by
  ext x
  simp only [rankFootprint,chartRoundFootprint,mem_iUnion]
  constructor
  · rintro ⟨p,hp⟩
    let j : Fin (D.order i).length := ⟨p.val,D.length_eq_order i ▸ p.property.1⟩
    let a := (D.order i).get j
    have hRead : (D.order i)[p.val]? = some a := List.getElem?_eq_getElem j.isLt
    have hRank : rank (E.event i a) = k := by simpa [hRead] using p.property.2
    refine ⟨⟨a,hRank⟩,?_⟩
    rwa [D.readback i _ _ hRead] at hp
  · rintro ⟨p,hp⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp (D.complete i p.val)
    have hRead : (D.order i)[j.val]? = some p.val :=
      (List.getElem?_eq_getElem j.isLt).trans (congrArg some hj)
    have hLen : j.val < (D.R i).length := (D.length_eq_order i).symm ▸ j.isLt
    have hRank : (((D.order i)[j.val]?).map (fun a => rank (E.event i a))).getD 0 = k := by
      rw [hRead]
      exact p.property
    refine ⟨⟨j.val,hLen,hRank⟩,?_⟩
    rwa [D.readback i _ _ hRead]

end Hironaka.HironakaG8KeyedRoundReadback
