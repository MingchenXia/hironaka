import Hironaka.Resolution.HironakaActualRetainedBoundaryMaskBlock
import Hironaka.Resolution.HironakaActualDefectProfileWindows

/-! Pointwise sharp joint-profile data at a genuine retained distinct defect. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4PointwiseJointProfile
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  NormalCrossingsComparison NormalCrossingsInvariance
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBoundaryMaskBlock
  HironakaActualRetainedBornResidualSeed HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaG4CompactWholeMonomialMaskPhase HironakaActualDefectProfileWindows
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualDynamicDistinctCentre

variable {n : ℕ} {X : CMfd.{u} n}

theorem retained_joint_profile_controls_near_defect (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {x : X} (hx : x ∈ actualFamilyDistinctDefect N (oldResidualPart N old born)) :
    let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
    let q := ∑ i,r i
    let P := inactiveCanonicalRows N old born r x
    1 ≤ q ∧ (∀ i ∈ P,r i = 0) ∧
      ∀ᶠ y in 𝓝 x,
        (∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ r i) ∧
        actualDistinctProperCount (oldResidualPart N old born) y < q ∧
        inactiveCanonicalRows N old born r y ⊆ P := by
  classical
  intro r q P
  let J := oldResidualPart N old born
  let D := oldMonomialPart N old born
  have hSeed (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hC (i : Fin old.length) : (J i).IsCoherent := (hSeed i).1.isCoherent
  have hDC (i : Fin old.length) : (D i).IsCoherent :=
    (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
  have hMeaning : (canonicalProductMarked N old born q).ideal =
      relativeIdealListProduct N (List.ofFn J) := by
    have hList : canonicalResidualFamily N old born = List.ofFn J := by
      unfold canonicalResidualFamily
      conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
      rfl
    change relativeIdealListProduct N (canonicalResidualFamily N old born) =
      relativeIdealListProduct N (List.ofFn J)
    rw [hList]
  have hOrder := (retained_product_geometry hn hN hE hTr hdense q
    (.refl : BlowupTower X X) trivial).2.2.2 x hx.1
  change ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x = q at hOrder
  have hCount : actualDistinctProperCount J x < q := by
    have h := hx.2
    change actualDistinctProperCount J x <
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn J)) x at h
    rwa [←hMeaning,hOrder] at h
  have hRows : ∀ᶠ y in 𝓝 x,∀ i,ordinaryTraceOrder N (J i) y ≤ r i :=
    eventually_all.mpr (fun i => eventually_ordinaryTraceOrder_le hn hN (hC i) (hSeed i).2.1 hx.1)
  have hMask : ∀ᶠ y in 𝓝 x,inactiveCanonicalRows N old born r y ⊆ P := by
    change ∀ᶠ y in 𝓝 x,∀ i ∈ inactiveCanonicalRows N old born r y,i ∈ P
    apply eventually_all.mpr
    intro i
    by_cases hi : i ∈ P
    · exact Eventually.of_forall (fun _ _ => hi)
    by_cases hr : r i = 0
    · have hUnit : (D i).mem x 1 := by
        by_contra hu
        apply hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,hu⟩
      filter_upwards [HomogenizedGlueing.eventually_mem (hDC i) hUnit] with y hy hiy
      exact False.elim ((Finset.mem_filter.mp hiy).2.2 hy)
    · exact Eventually.of_forall (fun _ hiy => False.elim (hr (Finset.mem_filter.mp hiy).2.1))
  refine ⟨by omega,fun i hi => (Finset.mem_filter.mp hi).2.1,?_⟩
  filter_upwards [hRows,eventually_actualDistinctProperCount_le hC x,hMask] with y hRow hCt hMaskY
  exact ⟨hRow,hCt.trans_lt hCount,hMaskY⟩

end
end Hironaka.HironakaG4PointwiseJointProfile
