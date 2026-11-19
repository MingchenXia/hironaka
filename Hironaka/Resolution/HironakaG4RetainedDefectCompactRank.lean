import Hironaka.Resolution.HironakaG4PointwiseJointProfile
import Mathlib.Topology.Semicontinuity.Basic

/-! The genuine retained-defect order and inactive count attain a maximum
near an arbitrary compact enclosure, without requiring a compact defect. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedDefectCompactRank
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HironakaG4PointwiseJointProfile HironakaG4PreparedCentreCoordinates
  HironakaActualRetainedBoundaryJointStep HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaActualRetainedBornResidualSeed
  RelativePrincipalizationSpan DivisorExponentAlong GermIdealOrder

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual retained total order, followed by the number of inactive nonunit
old positions. This rank is used on the true chronological distinct defect. -/
def retainedDefectRank (N : Set X) (old born : List (Set X)) (x : X) : ℕ ×ₗ ℕ :=
  let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
  toLex (∑ i,r i,(inactiveCanonicalRows N old born r x).card)

/-- The total order and inactive count cannot increase sufficiently near a
point of the actual retained distinct defect. The profile is unchanged if
the total stays equal. -/
theorem eventually_retainedDefectRank_le (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {x : X} (hx : x ∈ actualFamilyDistinctDefect N (oldResidualPart N old born)) :
    ∀ᶠ y in 𝓝 x,retainedDefectRank N old born y ≤ retainedDefectRank N old born x := by
  have hControls := (retained_joint_profile_controls_near_defect hn hN hE hTr hdense hx).2.2
  let r (y : X) := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) y
  filter_upwards [hControls] with y hY
  obtain ⟨hOrd,_hCount,hMask⟩ := hY
  have hSum : ∑ i,r y i ≤ ∑ i,r x i := Finset.sum_le_sum (fun i _ => hOrd i)
  change toLex (∑ i,r y i,(inactiveCanonicalRows N old born (r y) y).card) ≤
    toLex (∑ i,r x i,(inactiveCanonicalRows N old born (r x) x).card)
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases hSum.eq_or_lt with hEq | hLt
  · have hProfile : r y = r x := funext fun i =>
      (Finset.sum_eq_sum_iff_of_le (fun i _ => hOrd i)).mp hEq i (Finset.mem_univ i)
    right
    exact ⟨hEq,by rw [hProfile]; exact Finset.card_le_card hMask⟩
  · exact Or.inl hLt

/-- A locally upper-bounded rank on a closed set attains a maximum on its
nonempty intersection with a compact enclosure. That bound holds on the
closed set in some open neighborhood of the entire enclosure. -/
theorem exists_rank_max_near_compact {A α : Type*} [TopologicalSpace A] [LinearOrder α]
    (rank : A → α) {K D : Set A} (hK : IsCompact K) (hClosed : IsClosed D)
    (hNonempty : (K ∩ D).Nonempty)
    (hLocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, rank y ≤ rank x) :
    ∃ x ∈ K ∩ D, ∃ U : Opens A, K ⊆ U ∧
      ∀ y ∈ U, y ∈ D → rank y ≤ rank x := by
  have hUpper : UpperSemicontinuousOn rank (K ∩ D) := by
    intro x hx
    apply UpperSemicontinuousAt.upperSemicontinuousWithinAt
    intro a ha
    exact (hLocal x hx.2).mono
      (fun _ hy => hy.trans_lt ha)
  obtain ⟨x,hx,hMax⟩ := hUpper.exists_isMaxOn hNonempty (hK.inter_right hClosed)
  let B : Set A := {y | y ∈ D → rank y ≤ rank x}
  let U : Opens A := ⟨interior B,isOpen_interior⟩
  refine ⟨x,hx,U,?_,fun _ hy => interior_subset hy⟩
  intro y hy
  apply mem_interior_iff_mem_nhds.mpr
  by_cases hyD : y ∈ D
  · have hyRank : rank y ≤ rank x := hMax ⟨hy,hyD⟩
    exact (hLocal y hyD).mono
      (fun _ hz _ => hz.trans hyRank)
  · exact Filter.mem_of_superset (hClosed.isOpen_compl.mem_nhds hyD)
      (fun _ hz hD => False.elim (hz hD))

/-- For an arbitrary compact enclosure meeting the closed true defect, an
actual lexicographic maximum on the enclosure bounds the entire defect in
a neighbourhood of the enclosure. -/
theorem exists_retained_defect_rank_max_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      ∃ U : Opens X,K ⊆ U ∧
        ∀ y ∈ U, y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectRank N old born y ≤ retainedDefectRank N old born x := by
  exact exists_rank_max_near_compact (retainedDefectRank N old born) hK hClosed hNonempty
    (fun _ hx => eventually_retainedDefectRank_le hn hN hE hTr hdense hx)

/-- The candidate crest consists of closed order thresholds on the actual
defect and the vanishing of the selected native old factors. -/
def retainedDefectCrest (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (P : Finset (Fin old.length)) : Set X :=
  (actualFamilyDistinctDefect N (oldResidualPart N old born) ∩
    ⋂ i : Fin old.length,cosupport n N (oldResidualPart N old born i) (profile i)) ∩
      ⋂ i : P,(oldMonomialPart N old born i).zeroLocus

/-- The actual ordered row profile and inactive mask put a true defect
point on the selected closed crest. -/
theorem mem_retainedDefectCrest_of_profile_mask_eq (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (r : Fin old.length → ℕ) (P : Finset (Fin old.length)) {y : X}
    (hy : y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born))
    (hRows : ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y = r i)
    (hMask : inactiveCanonicalRows N old born r y = P) :
    y ∈ retainedDefectCrest N old born r P := by
  classical
  have hSeed (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hDC (i : Fin old.length) : (oldMonomialPart N old born i).IsCoherent :=
    (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
  refine ⟨⟨hy,mem_iInter.mpr fun i => ?_⟩,mem_iInter.mpr fun i => ?_⟩
  · exact (ordinaryTraceOrder_cosupport_iff hN (hSeed i).1.isCoherent
      (hSeed i).2.1 hy.1 (r i)).mpr (hRows i).ge
  · have hi : i.val ∈ inactiveCanonicalRows N old born r y := hMask.symm ▸ i.property
    have hNotUnit := (Finset.mem_filter.mp hi).2.2
    exact (actual_proper_iff_zeroLocus hDC i.val y).mp
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hNotUnit⟩)

/-- The actual retained crest is closed when its true distinct-defect
part is closed. -/
theorem isClosed_retainedDefectCrest (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (r : Fin old.length → ℕ) (P : Finset (Fin old.length)) :
    IsClosed (retainedDefectCrest N old born r P) := by
  refine (hClosed.inter (isClosed_iInter fun i => ?_)).inter (isClosed_iInter fun i => ?_)
  · have hSeed := retainedResidualMarked_geometry hn hN hE hTr hdense i
    exact GiraudAlong.isClosed_cosupport_along hSeed.1.isCoherent hN (r i)
  · exact OrderTaylor.isClosed_zeroLocus_of_isCoherent
      (actual_old_parts_geometry hn hN hE hTr hdense i.val).2.2.2.2.1

/-- With a specified maximizer, the same closed crest and its profile
open are determined without making another choice of a maximal stamp. -/
theorem exists_retained_defect_crest_of_rank_bound (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (U : Opens X) {x : X} (hx : x ∈ actualFamilyDistinctDefect N (oldResidualPart N old born))
    (hMax : ∀ y ∈ U, y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
      retainedDefectRank N old born y ≤ retainedDefectRank N old born x) :
    ∃ V : Opens X, V ≤ U ∧
      let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
      let q := ∑ i,r i
      let P := inactiveCanonicalRows N old born r x
      let C := retainedDefectCrest N old born r P
      1 ≤ q ∧ IsClosed C ∧ x ∈ C ∧ C ∩ (U : Set X) ⊆ V ∧
      (∀ y ∈ U,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
        retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧
      (∀ y ∈ V,(∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ r i) ∧
        actualDistinctProperCount (oldResidualPart N old born) y < q ∧
        inactiveCanonicalRows N old born r y ⊆ P) ∧
      ∀ y ∈ U,y ∈ C ↔
        y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
        (∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y = r i) ∧
        inactiveCanonicalRows N old born r y = P := by
  classical
  let J := oldResidualPart N old born
  let D := oldMonomialPart N old born
  let r := fun i => ordinaryTraceOrder N (J i) x
  let q := ∑ i,r i
  let P := inactiveCanonicalRows N old born r x
  let C := retainedDefectCrest N old born r P
  have hSeed (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hDC (i : Fin old.length) : (D i).IsCoherent :=
    (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
  have hOrd {y : X} (hy : y ∈ N) (i : Fin old.length) :
      y ∈ cosupport n N (J i) (r i) ↔ r i ≤ ordinaryTraceOrder N (J i) y :=
    ordinaryTraceOrder_cosupport_iff hN (hSeed i).1.isCoherent (hSeed i).2.1 hy (r i)
  have hProper (i : Fin old.length) (y : X) :
      ¬(D i).mem y 1 ↔ y ∈ (D i).zeroLocus := by
    simpa only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and] using
      actual_proper_iff_zeroLocus hDC i y
  have hC : IsClosed C := isClosed_retainedDefectCrest hn hN hE hTr hdense hClosed r P
  have hPzero (i : Fin old.length) (hi : i ∈ P) : r i = 0 :=
    (Finset.mem_filter.mp hi).2.1
  have hCFrom {y : X} (hy : y ∈ actualFamilyDistinctDefect N J)
      (hRows : ∀ i,ordinaryTraceOrder N (J i) y = r i)
      (hMask : inactiveCanonicalRows N old born r y = P) : y ∈ C :=
    mem_retainedDefectCrest_of_profile_mask_eq hn hN hE hTr hdense r P hy hRows hMask
  have hExact (y : X) (hyU : y ∈ U) : y ∈ C ↔
      y ∈ actualFamilyDistinctDefect N J ∧
      (∀ i,ordinaryTraceOrder N (J i) y = r i) ∧ inactiveCanonicalRows N old born r y = P := by
    refine ⟨?_,fun hy => hCFrom hy.1 hy.2.1 hy.2.2⟩
    intro hy
    have hyD := hy.1.1
    let ry := fun i => ordinaryTraceOrder N (J i) y
    have hLe (i : Fin old.length) : r i ≤ ry i := (hOrd hyD.1 i).mp (mem_iInter.mp hy.1.2 i)
    have hSum : q ≤ ∑ i,ry i := Finset.sum_le_sum (fun i _ => hLe i)
    have hRank := hMax y hyU hyD
    change toLex (∑ i,ry i,(inactiveCanonicalRows N old born ry y).card) ≤ toLex (q,P.card) at hRank
    rcases Prod.Lex.toLex_le_toLex.mp hRank with hLt | ⟨hEq,hMaskBound⟩
    · exact False.elim ((not_lt_of_ge hSum) hLt)
    · have hRows : ∀ i,ry i = r i := fun i =>
        ((Finset.sum_eq_sum_iff_of_le (fun i _ => hLe i)).mp hEq.symm i (Finset.mem_univ i)).symm
      rw [funext hRows] at hMaskBound
      have hSub : P ⊆ inactiveCanonicalRows N old born r y := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hPzero i hi,
          (hProper i y).mpr (mem_iInter.mp hy.2 ⟨i,hi⟩)⟩
      exact ⟨hyD,hRows,(Finset.eq_of_subset_of_card_le hSub hMaskBound).symm⟩
  let S : Set X := {y | (∀ i,ordinaryTraceOrder N (J i) y ≤ r i) ∧
    actualDistinctProperCount J y < q ∧ inactiveCanonicalRows N old born r y ⊆ P}
  let V : Opens X := U ⊓ ⟨interior S,isOpen_interior⟩
  have hq : 1 ≤ q := (retained_joint_profile_controls_near_defect hn hN hE hTr hdense hx).1
  refine ⟨V,inf_le_left,hq,hC,hCFrom hx (fun _ => rfl) rfl,?_,hMax,?_,hExact⟩
  · intro y hy
    have hY := (hExact y hy.2).mp hy.1
    refine ⟨hy.2,mem_interior_iff_mem_nhds.mpr ?_⟩
    have hRy : (fun i => ordinaryTraceOrder N (J i) y) = r := funext hY.2.1
    have hLocal := (retained_joint_profile_controls_near_defect hn hN hE hTr hdense hY.1).2.2
    rwa [hRy,hY.2.2] at hLocal
  · intro y hy
    have hS : y ∈ S := interior_subset (s := S) hy.2
    exact hS

/-- A maximizer on any compact enclosure produces a closed true retained
crest and an actual fixed-profile open domain containing the entire crest
inside a neighbourhood of the enclosure. The crest need not be compact. -/
theorem exists_retained_defect_crest_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K, ∃ U V : Opens X,K ⊆ U ∧ V ≤ U ∧
      let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
      let q := ∑ i,r i
      let P := inactiveCanonicalRows N old born r x
      let C := retainedDefectCrest N old born r P
      1 ≤ q ∧ IsClosed C ∧ x ∈ C ∧ C ∩ (U : Set X) ⊆ V ∧
      (∀ y ∈ U,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
        retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧
      (∀ y ∈ V,(∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ r i) ∧
        actualDistinctProperCount (oldResidualPart N old born) y < q ∧
        inactiveCanonicalRows N old born r y ⊆ P) ∧
      ∀ y ∈ U,y ∈ C ↔
        y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
        (∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y = r i) ∧
        inactiveCanonicalRows N old born r y = P := by
  obtain ⟨x,hx,U,hKU,hMax⟩ :=
    exists_retained_defect_rank_max_near_compact hn hN hE hTr hdense hK hClosed hNonempty
  obtain ⟨V,hVU,hRest⟩ :=
    exists_retained_defect_crest_of_rank_bound hn hN hE hTr hdense hClosed U hx.2 hMax
  exact ⟨x,hx.1,U,V,hKU,hVU,hRest⟩

end
end Hironaka.HironakaG4RetainedDefectCompactRank
