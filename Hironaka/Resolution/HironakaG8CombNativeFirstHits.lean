import Hironaka.Resolution.HironakaG8CombAnchorProfiles
import Hironaka.Resolution.HironakaG8CountableArrangementNoClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CombNativeFirstHits

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerIsomorphism HironakaG8FirstFootprintOrder
  HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry
  HironakaG8CorrectedOrderedEndpoint HironakaG8NoncompactInitialBoundaryAtlas
  HironakaG8LabelledEmbeddedAtlas HironakaG8LabelledNativeHistory HironakaG3RTowerClass
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  HironakaResolutionSpaceLocal HironakaEmbeddedAnalytic HironakaG8PhysicalChartOccupiedLifts
  HironakaG8VariableCombArrangement HironakaG8CombExactLocalArrangement
  HironakaG8CombAnchorProfiles

noncomputable section
def combManifold : CMfd.{0} 3 := CMfd.of (n := 3) Ambient

variable {Z : CMfd.{0} 3} {P : Z → combManifold}

abbrev CombChart :=
  TowerChart (orderedInitialBoundaryClass (X := combManifold) comb []) Z P

def firstHit (c : CombChart (P := P)) (x : c.U) (k : ℕ) : Prop :=
  x ∈ slotFootprint c.T k ∧ ∀ j < k, x ∉ slotFootprint c.T j

/-- On every actual certified native chart that sees two comb anchors,
the higher anchor has a strictly earlier physical first hit. Both
hits are witnessed in the chart's original full tower. -/
theorem comb_ordered_native_first_hits (c : CombChart (P := P))
    (hC : InitialBoundaryChartEpochs c) {i j : ℕ} (hij : i < j)
    (hi : anchor i ∈ c.U) (hj : anchor j ∈ c.U) :
    ∃ a b : ℕ, a < b ∧ firstHit c ⟨anchor j,hj⟩ a ∧ firstHit c ⟨anchor i,hi⟩ b := by
  let x : c.U := ⟨anchor i,hi⟩
  let y : c.U := ⟨anchor j,hj⟩
  let W := (Subtype.val : c.U → Ambient) ⁻¹' comb
  obtain ⟨B,D,S,Q,χ,L,hS,_,_,hIso⟩ := hC
  have hSing (k : ℕ) (h : anchor k ∈ c.U) :
      (⟨anchor k,h⟩ : c.U) ∈ singularSet (n := 3) W := by
    dsimp only [W]
    rw [singularSet_preimage_val]
    exact anchor_mem_singularSet k
  have hProfile :
      toLex (hilbertSamuelAt (vanishingIdeal (n := 3) W) x) <
      toLex (hilbertSamuelAt (vanishingIdeal (n := 3) W) y) := by
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any c.U comb x),
      funext (hilbertSamuelAt_vanishing_actual_open_any c.U comb y)]
    exact comb_anchor_profile_strictMono hij
  obtain ⟨a,b,hab,ha,hb,hDa,hDb⟩ := exists_ordered_first_hits_of_original_profiles
    hS (mem_univ x) (mem_univ y) (hSing i hi) (hSing j hj) hProfile
  have hTransfer (u : c.U) {r : ℕ} (hu : u ∈ slotFootprint S r)
      (hFirst : ∀ q < r, u ∉ slotFootprint S q) : firstHit c u r := by
    have hR := hit_slot_lt_length S hu
    have hRead (q : ℕ) (hq : q < S.length) :
        slotFootprint c.T q = slotFootprint S q := by
      rw [slotFootprint_of_isTowerIso hIso,slotFootprint_append,if_pos hq]
      rfl
    exact ⟨(hRead r hR).symm ▸ hu,fun q hq => (hRead q (hq.trans hR)).symm ▸ hFirst q hq⟩
  exact ⟨a,b,hab,hTransfer y ha hDa,hTransfer x hb hDb⟩

end
end Hironaka.HironakaG8CombNativeFirstHits

#print axioms Hironaka.HironakaG8CombNativeFirstHits.comb_ordered_native_first_hits
