import Hironaka.Resolution.HironakaSharpBadProcessedWindowGeometry

/-! Whole actual sharp-bad old-row containment on a genuine lower prepared open.
No future history, exponent presentation or dynamic invariant comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaProcessedWindowSharpBadOldContainment
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  RestrictedIdealExtension GermIdealOrder HironakaG4PreparedCentreCoordinates
  InvertibleIdealQuotient MonomialPartAlong DivisorExponentAlong GiraudAlong
  HironakaSharpOriginalProductTraceOrder
  HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualTraceIncidence
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsSNCBlockCarrier
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumNativeFields
  HironakaActualProtectedOtherRowLocalStep HironakaG4LowerPreparedNeighborhood
open HironakaSharpNormalCrossingsOpenLocus MarkedIdealRestrictOpen HironakaOriginalNCCountHistory
  HironakaOriginalNCMarkedStratum MarkedIdealBiholomorphism
open HomogenizedGlueingTower (strictAlong)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem prepared_all_units_nc {N : Set Y} {old born : List (Set Y)}
    (hn : 0<n) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N⊆closure (N \ ⋃H∈old++born,H)) {x : Y} (hx : x∈N)
    (hOrd : ∀a,ordinaryTraceOrder N (oldResidualPart N old born a) x≤1)
    (hPrep : IsPreparedResidualSNCAt N old born x)
    (hUnit : ∀a,(oldMonomialPart N old born a).mem x 1) :
    normalCrossingsAt (n:=n) N (old++born) x := by
  have h := normalCrossingsAt_prepared_selected_born_intersection hn hN hE hTr hdense
    (∅ : Finset (Fin born.length)) (by simpa [BoundaryCount.memberInter] using hx)
    hOrd hPrep (List.Sublist.refl _) (fun H hH => ?_) (fun _ h => List.mem_append_right _ h)
  · simpa [BoundaryCount.memberInter] using h
  · rcases List.mem_append.mp hH with hOld | hBorn
    · obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hOld
      exact Or.inr ⟨a,rfl,hUnit a⟩
    · exact Or.inl hBorn

private theorem pullback_one_mem {U : Opens Y} {I : GermIdeal n Y} {x : U}
    (h : I.mem x.val (1 : Y→ℂ)) :
    (GermIdeal.pullback (m:=n) (Subtype.val : U→Y) I).mem x (1 : U→ℂ) := by
  apply GermIdeal.mem_pullback_iff.mpr
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,h,rfl⟩ (holomorphicAt_const 1)

theorem actual_processed_window_sharp_bad_old_containment
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (j : Fin E.length) (hne : j ≠ i) {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Bj := originalSharpBadLocus (n := n) Sj (old.eraseIdx j.val ++ A.E)
    ∃ U : Opens Y, x ∈ U ∧
      (∀ y ∈ U, y ∈ Bj → y ∈ strictAlong T (E.get i)) ∧
      (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i))).Le
        (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' Bj)) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let L := A.N ∩ (J j).zeroLocus
  let Bj := originalSharpBadLocus (n := n) L (old.eraseIdx j.val ++ A.E)
  let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let Di := monomialPartAlong n A.N I A.E
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  obtain ⟨U,hxU,hLc,hEc,hTc,hDc,hRows,hPrep⟩ :=
    actual_original_lower_prepared_neighborhood hn hW hE hdense i T hT hFull hOrd hNC hDenseS j hne hxi hxj
  let LU : Set U := (Subtype.val : U → Y) ⁻¹' L
  let oldU := (old.eraseIdx j.val).map ((Subtype.val : U → Y) ⁻¹' ·)
  let bornU := A.E.map ((Subtype.val : U → Y) ⁻¹' ·)
  have hContain : ∀ y ∈ U, y ∈ Bj → y ∈ strictAlong T (E.get i) := by
    intro y hyU hyBad
    by_contra hyNot
    let yU : U := ⟨y,hyU⟩
    have hOneH : (vanishingIdeal (n := n) (strictAlong T (E.get i))).mem y 1 := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      have hClosed : IsClosed (strictAlong T (E.get i)) := by
        have hOld := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left old A.E)
        have hMem : strictAlong T (E.get i) ∈ old :=
          List.mem_map.mpr ⟨E.get i,List.get_mem E i,rfl⟩
        exact hOld.1 _ hMem
      filter_upwards [hClosed.isOpen_compl.mem_nhds hyNot] with z hz hzH
      exact False.elim (hz hzH)
    have hcI : I.IsCoherent := (hRecorded.2.2.2.2 i).1
    have hOneI : I.mem y 1 := by
      apply le_restrictOn _ y 1 hOneH
      have hOld := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left old A.E)
      have hGet : old.get ⟨i.val,by simp [old]⟩ = strictAlong T (E.get i) := by simp [old]
      rw [←hGet]
      exact VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hOld _)
    have hOneD : Di.mem y 1 := le_monomialPartAlong hn
      (isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_right old A.E))
      hRecorded.2.2.1 hcI y 1 hOneI
    have hDiC : Di.IsCoherent := by
      let oi : Fin old.length := ⟨i.val,by simp [old]⟩
      have hGet : old.get oi = strictAlong T (E.get i) := by simp [old,oi]
      have h := (actual_old_parts_geometry hn hRecorded.1 hRecorded.2.1 hRecorded.2.2.1
        hRecorded.2.2.2.1 oi).2.2.2.2.1
      change (monomialPartAlong n A.N (restrictOn n A.N
        (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).IsCoherent
      rw [←hGet]
      exact h
    have hMi : (restrictOn n LU (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Di)).mem yU 1 :=
      le_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hDiC)
        yU 1 (pullback_one_mem hOneD)
    have hAll : ∀ a : Fin oldU.length,
        (oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU a).mem yU 1 := by
      intro a
      obtain ⟨H,hH,hHa⟩ := List.mem_map.mp (List.get_mem oldU a)
      obtain ⟨v,hv,hvj,hvH⟩ := List.mem_eraseIdx_iff_getElem.mp hH
      let k : Fin E.length := ⟨v,by simpa only [old,List.length_map] using hv⟩
      have hkj : k ≠ j := fun heq => hvj (congrArg Fin.val heq)
      obtain ⟨b,hb,hbRow⟩ := hRows k hkj
      have hkget : old.get ⟨v,hv⟩ = strictAlong T (E.get k) := by simp [old,k]
      have hab : oldU.get a = oldU.get b := by
        rw [hb,←hHa,←hkget]
        exact congrArg ((Subtype.val : U → Y) ⁻¹' ·) hvH.symm
      have hparts : oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU a =
          oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU b := by
        simp only [oldMonomialPart,oldTraceIdeal,hab]
      rw [hparts]
      by_cases hki : k = i
      · rw [if_pos hki] at hbRow
        rw [hbRow.1]
        exact hMi
      · rw [if_neg hki] at hbRow
        exact hbRow.1 yU hyBad.1
    have hNCU := prepared_all_units_nc hn hLc hEc hTc hDc
      (show yU ∈ LU from hyBad.1) (hPrep yU hyBad.1).1 (hPrep yU hyBad.1).2 hAll
    have hNCY : normalCrossingsAt (n := n) L (old.eraseIdx j.val ++ A.E) y := by
      apply (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff
        (C := L) (E := old.eraseIdx j.val ++ A.E) (U := U) (x := yU)).mp
      simpa only [List.map_append] using hNCU
    exact hyBad.2 hNCY
  refine ⟨U,hxU,hContain,?_⟩
  intro y g hg
  refine ⟨hg.1,?_⟩
  filter_upwards [hg.2] with z hz hzBad
  exact hz (hContain z.val z.property hzBad)

end
end Hironaka.HironakaProcessedWindowSharpBadOldContainment
