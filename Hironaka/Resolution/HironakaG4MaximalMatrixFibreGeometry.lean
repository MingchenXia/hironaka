import Hironaka.Resolution.HironakaG4ExactMatrixWindow
import Hironaka.Resolution.HironakaG4TraceExponentClosed
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre
import Hironaka.Resolution.HironakaG4SingleBornTrace
import Hironaka.Resolution.HironakaG4CanonicalZeroRowUnit
import Hironaka.Resolution.HironakaG4ZeroMaskFixedQFold
import Hironaka.Resolution.HironakaG4ProcessedSupportHighCountStep
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4MaximalMatrixFibreGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings NormalCrossingsComparison HomogenizedGlueingTower BoundaryCount
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4ActualMonomialPairWindows DivisorExponentAlong HironakaG4SingleBornTrace
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalAllBoundaryCentre
  HironakaG4ExactMatrixWindow HironakaG4TraceExponentClosed HironakaG4CanonicalZeroRowUnit HironakaG4ZeroMaskFixedQFold HironakaG4ProcessedSupportHighCountStep
variable {n : ℕ} {X : CMfd.{u} n}

/-- Every nonunit old row is hit by the set of all born slots through the point. -/
theorem all_incident_born_hit_nonunit (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) {x : X} (hx : x ∈ N) :
    let K : Finset (Fin born.length) := Finset.univ.filter fun j => x ∈ born.get j
    ∀ i : Fin old.length,¬(oldMonomialPart N old born i).mem x 1 →
      1 ≤ ∑ j ∈ K,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x := by
  let K : Finset (Fin born.length) := Finset.univ.filter fun j => x ∈ born.get j
  change ∀ i : Fin old.length,¬(oldMonomialPart N old born i).mem x 1 →
    1 ≤ ∑ j ∈ K,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  intro i hNot
  by_contra hfail
  have hSum : (∑ j ∈ K,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=0 := by omega
  have hZero (j : Fin born.length) : divExpAlong n N (oldMonomialPart N old born i) (born.get j) x=0 := by
    by_cases hj : j ∈ K
    · have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)) hj
      rw [hSum] at hle
      exact Nat.eq_zero_of_le_zero hle
    · have hNotMem : x ∉ born.get j := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      exact exponent_zero_off_trace (hN.1.inter (hBorn.1 _ (List.get_mem born j))) (fun h => hNotMem h.2)
  have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
  exact hNot (one_mem_of_zero_canonical_row hn hN hBorn hTr hParts.2.2.2.2.1
    hParts.2.2.2.2.2.1 hParts.2.2.2.2.2.2.1 hx hZero)

/-- Normal-crossings at a point depends only on the carrier germ. -/
theorem normalCrossingsAt_of_eventually_carrier_iff {C D : Set X} {E : List (Set X)} {x : X}
    (h : ∀ᶠ y in 𝓝 x,y ∈ D ↔ y ∈ C) (hNC : normalCrossingsAt (n := n) D E x) :
    normalCrossingsAt (n := n) C E x := by
  obtain ⟨U,hUsub,hUopen,hxU⟩ := mem_nhds_iff.mp h
  let V : Opens X := ⟨U,hUopen⟩
  let z : V := ⟨x,hxU⟩
  have heq : (Subtype.val : V → X) ⁻¹' D = (Subtype.val : V → X) ⁻¹' C := by
    ext y
    exact hUsub y.property
  apply (normalCrossingsAt_preimage_val_iff (U := V) (x := z)).mp
  rw [←heq]
  exact normalCrossingsAt_preimage_val_iff.mpr hNC

/-- Positive actual proper-row count lies inside the literal sharp-bad locus. -/
theorem positive_tau_in_sharp_bad (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) {x : X} (hx : x ∈ N)
    (hPos : 0<tauD (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)) :
    x ∈ originalSharpBadLocus (n := n) N (old ++ born) := by
  let A : Fin old.length → Fin born.length → ℕ := fun i j =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  have hne : (properRows A).Nonempty := Finset.card_pos.mp hPos
  obtain ⟨i,hi⟩ := hne
  have hRow : 0<rowOrder A i := (Finset.mem_filter.mp hi).2
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hNot : ¬(oldMonomialPart N old born i).mem x 1 := by
    intro hOne
    have hz (j : Fin born.length) : A i j=0 :=
      exponent_zero_of_one_mem (hN.1.inter (hBorn.1 _ (List.get_mem born j))) hOne
    have hzero : rowOrder A i=0 := by simp [rowOrder,hz]
    omega
  exact canonical_proper_subset_bad hn hN hE hdense i ⟨hx,hNot⟩


/-- A maximal actual matrix on a closed equal-native-pair locus has a closed
smooth exact fibre with full-boundary normal crossings and sharp footprint.
Its local centre uses all nonzero source columns, which need not equal a
strategic selected set. -/
theorem maximal_top_matrix_fibre_geometry (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x) (p : X) (hp : p ∈ N) :
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
    let L : Set X := {x | x ∈ N ∧ tauD (A x)=tauD (A p) ∧ nuOne (A x)=nuOne (A p)}
    let C : Set X := {x | x ∈ N ∧ A x=A p}
    IsClosed L → 0<tauD (A p) →
    (∀ x ∈ L,(∀ i j,A p i j ≤ A x i j) → A x=A p) →
    C.Nonempty ∧ IsClosedSubmanifold n C ∧ HasNormalCrossings n C (old++born) ∧
      C ⊆ originalSharpBadLocus (n := n) N (old++born) ∧
      ∀ x ∈ C, ∀ᶠ y in 𝓝 x, y ∈ N ∩ memberInter born (nonzeroColumns (A p)) ↔ y ∈ C := by
  let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  let L : Set X := {x | x ∈ N ∧ tauD (A x)=tauD (A p) ∧ nuOne (A x)=nuOne (A p)}
  let C : Set X := {x | x ∈ N ∧ A x=A p}
  change IsClosed L → 0<tauD (A p) → _
  intro hL hPos hMax
  have hEq : C={x | x ∈ L ∧ A x=A p} := by
    ext x
    constructor
    · rintro ⟨hx,hA⟩
      exact ⟨⟨hx,by rw [hA],by rw [hA]⟩,hA⟩
    · rintro ⟨hx,hA⟩
      exact ⟨hx.1,hA⟩
  have hClosed : IsClosed C := by
    rw [hEq]
    exact actual_maximal_matrix_fibre_closed hn hN hE hTr hdense L hL (A p) hMax
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  let S := nonzeroColumns (A p)
  have hSmooth := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hBorn hTr S
  have hGerm : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, y ∈ N ∩ memberInter born S ↔ y ∈ C := by
    intro x hx
    obtain ⟨U,hxU,hWindow⟩ := exact_matrix_window hn hN hE hTr hdense hx.1
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    constructor
    · rintro ⟨hyN,hyS⟩
      have hyS' : y ∈ memberInter born (nonzeroColumns (A x)) := by simpa [S,hx.2] using hyS
      exact ⟨hyN,((hWindow y hyN hy).mpr hyS').trans hx.2⟩
    · rintro ⟨hyN,hyA⟩
      have hyS := (hWindow y hyN hy).mp (hyA.trans hx.2.symm)
      change y ∈ memberInter born (nonzeroColumns (A x)) at hyS
      rw [hx.2] at hyS
      exact ⟨hyN,hyS⟩
  have hxS : ∀ x ∈ C,x ∈ N ∩ memberInter born S := by
    intro x hx
    have he := (hGerm x hx).self_of_nhds
    exact he.mpr hx
  have hCS : IsClosedSubmanifold n C := by
    refine ⟨hClosed,?_⟩
    intro x hx
    obtain ⟨k,hk⟩ := hSmooth.2 x (hxS x hx)
    exact ⟨k,CodimOneSupport.regularAtDim_of_eventually_mem_iff (hGerm x hx) hk⟩
  have hNC : HasNormalCrossings n C (old++born) := by
    intro x hx
    let K : Finset (Fin born.length) := Finset.univ.filter fun j => x ∈ born.get j
    have hSub : S ⊆ K := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hxS x hx).2 j hj⟩
    have hHit := all_incident_born_hit_nonunit hn hN hE hTr hdense hx.1
    have hHitS : ∀ i : Fin old.length,¬(oldMonomialPart N old born i).mem x 1 →
        1 ≤ ∑ j ∈ S,A x i j := by
      intro i hi
      have hSum : (∑ j ∈ S,A x i j) = ∑ j ∈ K,A x i j := by
        apply Finset.sum_subset hSub
        intro j _ hjS
        have hj0 : A p i j=0 := by
          by_contra hh
          exact hjS (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i,hh⟩⟩)
        rw [hx.2]
        exact hj0
      rw [hSum]
      exact hHit i hi
    have hNC' := prepared_selected_born_centre_nc_at hn hN hE hTr hdense hOrd hPrepared S (hxS x hx) hHitS
    exact normalCrossingsAt_of_eventually_carrier_iff (hGerm x hx) hNC'
  refine ⟨⟨p,hp,rfl⟩,hCS,hNC,?_,hGerm⟩
  intro x hx
  apply positive_tau_in_sharp_bad hn hN hE hdense hx.1
  change 0<tauD (A x)
  have hxEq : A x=A p := hx.2
  rw [hxEq]
  exact hPos
end
end Hironaka.HironakaG4MaximalMatrixFibreGeometry
