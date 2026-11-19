import Hironaka.Resolution.HironakaG4OriginalSelectedLowerBoundaryHistory
import Hironaka.Resolution.HironakaG4ResidualInductionInputs
import Hironaka.Resolution.HironakaG4RetainedPreparedLocalSupport
import Hironaka.Resolution.HironakaG4EquimultipleRelativeOrder

/-! Physical lift of a true lower sharp tower through the selected native retained row. -/

set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedSelectedLowerLift
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterLocusAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings DropMembers CoefficientIdealRestriction
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualChronologicalStrictStep
  HironakaG4PreparedCentreCoordinates HironakaG4ResidualInductionInputs
  HironakaG4OriginalSelectedResidualTail HironakaG4OriginalSelectedLowerBoundaryHistory
  HironakaG4SmoothSubcarrierRecordedHistory HironakaActualRetainedBornResidualHistory
  HironakaActualRetainedBornResidualSeed HironakaActualRetainedBoundaryMaskBlock
  HironakaG4RetainedPreparedLocalSupport HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4EquimultipleRelativeOrder RestrictEmptyTower
  HironakaSharpOriginalMultiBoundaryBadLocus
  RelativePrincipalizationSpan RestrictedIdealExtension NonmonomialTransformAlong GermIdealOrder

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 500000 in
/-- The selected order-one native residual ideal is the whole reduced
vanishing ideal of its smooth support, including its unit germs. -/
theorem actual_retained_selected_support_whole (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (hOrd : ∀ x ∈ N,∀ j,ordinaryTraceOrder N (oldResidualPart N old born j) x ≤ 1)
    (i : Fin old.length) :
    let J := oldResidualPart N old born i
    let L := N ∩ J.zeroLocus
    IsClosedSubmanifold n L ∧ L ⊆ old.get i ∧ J = vanishingIdeal (n := n) L := by
  intro J L
  obtain ⟨hL,hOwn,hPoint⟩ := actual_residual_support_local_geometry hn hN hE hTr hdense hOrd i
  obtain ⟨hTraceCoh,_hTraceNZ,hJ,_hRest⟩ := actual_old_parts_geometry hn hN hE hTr hdense i
  have hNLe : (vanishingIdeal (n := n) N).Le J :=
    fun x g hg => (le_nonmonomialPartAlong_self hTraceCoh) x g (vanishingIdeal_le_restrictOn x g hg)
  have hSupp : J.zeroLocus ⊆ L := by
    intro x hx
    have hxN : x ∈ (vanishingIdeal (n := n) N).zeroLocus :=
      fun g hg => hx g (hNLe x g hg)
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hN.1] at hxN
    exact ⟨hxN,hx⟩
  exact ⟨hL,hOwn,coherent_ideal_eq_vanishingIdeal_of_local_reduced hJ hL.1 hSupp
    (fun x hx => (hPoint x hx).2.1)⟩

set_option maxHeartbeats 650000 in
/-- A true lower test through the selected support is an upper test for
both literal ordered records. The one omitted old slot contains every
strict lower centre. The selected original row stays exactly reduced. -/
theorem actual_retained_selected_lower_boundary_history (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (hOrd : ∀ x ∈ N,∀ j,ordinaryTraceOrder N (oldResidualPart N old born j) x ≤ 1)
    (i : Fin old.length) :
    let J := oldResidualPart N old born i
    let L := N ∩ J.zeroLocus
    let F := remainingBoundary old born i
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y), IsGeoTestTower (geometricTemplate L F) R →
      IsGeoTestTower (geometricTemplate N born) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R ∧
      IsClosedSubmanifold n (strictAlong R L) ∧
      retainedRowSupport N old born i R = strictAlong R L ∧
      (chronologicalMarked (retainedResidualMarked N old born i) R).ideal =
        vanishingIdeal (n := n) (strictAlong R L) ∧
      (geoTransformAlong (geometricTemplate L F) R).E = retainedRowBoundary N old born i R := by
  intro J L F Y R hR
  obtain ⟨hL,hOwn,hJ⟩ := actual_retained_selected_support_whole hn hN hE hTr hdense hOrd i
  let M := geometricTemplate (univ : Set X) (old ++ born)
  have hM : M.IsWellFormed :=
    ⟨isClosedSubmanifold_univ,isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hParent : (geometricTemplate N born).IsWellFormed := ⟨hN,isCoherent_unitIdeal,hBorn,hTr⟩
  have hZ : (geometricTemplate L []).IsWellFormed :=
    ⟨hL,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hL⟩
  have hFsub : F.Sublist M.E := (List.eraseIdx_sublist old i.val).append (List.Sublist.refl born)
  have hMissing : ∀ H ∈ M.E,H ∉ F → L ⊆ H := by
    intro H hH hNot
    rcases List.mem_append.mp hH with hOld | hBorn
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hOld
      have hji : j.val = i.val := by
        by_contra hne
        exact hNot (List.mem_append_left born
          (List.mem_eraseIdx_iff_getElem.mpr ⟨j.val,j.isLt,hne,hj⟩))
      rw [show j = i from Fin.ext hji] at hj
      exact hj ▸ hOwn
    · exact False.elim (hNot (List.mem_append_right _ hBorn))
  have hCentres : CentresIn L R :=
    centresIn_of_isGeoTestTower_withN (geometricTemplate (univ : Set X) F) L R hR
  have hSmall := (actual_zero_mark_test_of_lower_test ({ M with E := F } : MarkedIdeal n X)
    (isWellFormed_withE hM hFsub) rfl (subset_univ L) (List.Sublist.refl F) R hR).1
  have hFull : IsGeoTestTower M R :=
    (isGeoTestTower_withE_iff_of_centresIn M hM (fun _ hH => hFsub.subset hH) hMissing R hCentres).1.mp hSmall
  have hTest : IsGeoTestTower (geometricTemplate N born) R :=
    (actual_zero_mark_test_of_lower_test (geometricTemplate N born) hParent rfl
      inter_subset_left (List.sublist_append_right _ _) R hR).1
  have hLTest : IsGeoTestTower (geometricTemplate L []) R :=
    (actual_zero_mark_test_of_lower_test (geometricTemplate L []) hZ rfl
      Subset.rfl (List.nil_sublist _) R hR).1
  obtain ⟨_hN',hL',hSub,hNC,hIC⟩ :=
    actual_recorded_smooth_subcarrier_dictionary hn hN hL inter_subset_left R hLTest
  have hBase := actual_recorded_smooth_subcarrier_dictionary hn hN hL inter_subset_left
    (.refl : BlowupTower X X) trivial
  have hEq : (retainedResidualMarked N old born i).ideal = (originalRelativeMemberMarked N L).ideal :=
    hJ.trans hBase.2.2.2.2.symm
  obtain ⟨hAN,hAI⟩ := chronological_carrier_ideal_congr
    (M := retainedResidualMarked N old born i) (M' := originalRelativeMemberMarked N L) rfl hEq R
  have hWhole := hAI.trans hIC
  have hSupp : retainedRowSupport N old born i R = strictAlong R L := by
    unfold retainedRowSupport
    rw [hAN.trans hNC,hWhole,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hL'.1]
    exact inter_eq_right.mpr hSub
  have hBoundary : (geoTransformAlong (geometricTemplate L F) R).E =
      retainedRowBoundary N old born i R := by
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := geometricTemplate L F) (𝔫 := geometricTemplate (univ : Set X) F) rfl R]
    change (geoTransformAlong (geometricTemplate (univ : Set X) (old.eraseIdx i.val ++ born)) R).E =
      (old.map (strictAlong R)).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate N born) R).E
    rw [retained_born_full_boundary_ordered_dictionary N (old.eraseIdx i.val) born R,
      List.eraseIdx_map]
  exact ⟨hTest,hFull,hL',hSupp,hWhole,hBoundary⟩


set_option maxHeartbeats 780000 in
/-- The selected true lower sharp centres are sharp for the full upper
boundary, and the selected chronological residual row stays of order at
most one throughout the same actual tower. -/
theorem actual_retained_selected_lower_sharp_and_order (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (hOrd : ∀ x ∈ N,∀ j,ordinaryTraceOrder N (oldResidualPart N old born j) x ≤ 1)
    (i : Fin old.length) :
    let J := oldResidualPart N old born i
    let L := N ∩ J.zeroLocus
    let F := remainingBoundary old born i
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y), IsGeoTestTower (geometricTemplate L F) R →
      CurrentSharpCentres L F R →
      CurrentSharpCentres N (old ++ born) R ∧
      let A := chronologicalMarked (retainedResidualMarked N old born i) R
      ∀ y ∈ A.N,ordinaryTraceOrder A.N A.ideal y ≤ 1 := by
  intro J L F Y R
  let M := retainedResidualMarked N old born i
  obtain ⟨hSeed,hNZ,hPr⟩ := retainedResidualMarked_geometry hn hN hE hTr hdense i
  induction R with
  | refl =>
    intro _ _
    exact ⟨trivial,fun y hy => hOrd y hy i⟩
  | @step U V Q C π hπ ih =>
    intro hQ hSharp
    obtain ⟨hSharpQ,hBoundQ⟩ := ih hQ.1 hSharp.1
    obtain ⟨hPar,hFull,hL,hSupport,_hIdeal,hBoundary⟩ :=
      actual_retained_selected_lower_boundary_history hn hN hE hTr hdense hOrd i Q hQ.1
    let A := chronologicalMarked M Q
    let B := geoTransformAlong (geometricTemplate N born) Q
    let O := old.map (strictAlong Q)
    let j : Fin O.length := Fin.cast (List.length_map _).symm i
    have hRecord := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense Q hPar hFull
    have hSeedNow := retained_seed_eq_chronological_current hn hN hE hTr hdense Q hPar hFull i
    have hSuppNow : strictAlong Q L = B.N ∩ (oldResidualPart B.N O B.E j).zeroLocus := by
      rw [←hSupport]
      unfold retainedRowSupport
      rw [←hSeedNow]
      rfl
    have hBoundNow : (geoTransformAlong (geometricTemplate (univ : Set X) F) Q).E =
        remainingBoundary O B.E j := by
      rw [←MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
        (𝔪 := geometricTemplate L F) (𝔫 := geometricTemplate (univ : Set X) F) rfl Q]
      exact hBoundary
    have hFullNow := retained_born_full_boundary_ordered_dictionary N old born Q
    have hNNow : B.N = strictAlong Q N := N_geoTransformAlong _ Q
    have hSharpNext : C ⊆ originalSharpBadLocus (n := n) (strictAlong Q N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) Q).E := by
      intro x hx
      have hLow := hSharp.2 hx
      rw [hSuppNow,hBoundNow] at hLow
      have hUp := originalSharpBadLocus_residual_subset hn hRecord.1 hRecord.2.1
        hRecord.2.2.1 hRecord.2.2.2.1 j hLow
      rwa [←hFullNow,hNNow] at hUp
    refine ⟨⟨hSharpQ,hSharpNext⟩,?_⟩
    obtain ⟨hAG,hANZ,hAPr⟩ :=
      chronologicalMarked_actual_geometry hn M hSeed rfl hNZ hPr Q hPar
    have hCS : C ⊆ retainedRowSupport N old born i Q := by
      intro x hx
      rw [hSupport]
      have hLowerN : (geoTransformAlong (geometricTemplate L F) Q).N = strictAlong Q L :=
        N_geoTransformAlong _ Q
      exact hLowerN ▸ hQ.2.subset_N hx
    have hCN : C ⊆ A.N := fun x hx => (hCS hx).1
    have hOne : ∀ x ∈ C,ordinaryTraceOrder A.N A.ideal x = 1 := by
      intro x hx
      refine (hBoundQ x (hCN hx)).antisymm ?_
      have hCos : x ∈ cosupport n A.N A.ideal 1 := by
        rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hAG.isCoherent hg)]
        exact hCS hx
      exact (ordinaryTraceOrder_cosupport_iff hAG.isClosedSubmanifold_N hAG.isCoherent
        hANZ (hCN hx) 1).mp hCos
    have hConstant : ∀ x ∈ C,∀ᶠ x' in 𝓝 x,x' ∈ C →
        ordinaryTraceOrder A.N A.ideal x' = ordinaryTraceOrder A.N A.ideal x :=
      fun x hx => Eventually.of_forall fun x' hx' => (hOne x' hx').trans (hOne x hx).symm
    change ∀ z ∈ (nextTotalMarked A.N A.ideal C π).N,
      ordinaryTraceOrder (nextTotalMarked A.N A.ideal C π).N
        (nextRelativeStrict A.N A.ideal C π) z ≤ 1
    intro z hz
    have hle := nextRelativeStrict_order_le_of_locally_constant_on_centre hn
      hAG.isClosedSubmanifold_N hAG.isCoherent hANZ hAPr hπ hCN hConstant hz
    have hzN : π z ∈ A.N :=
      geoStrictTransform_subset_preimage (C := C) hπ.contMDiff.continuous hAG.isClosedSubmanifold_N.1 hz
    exact hle.trans (hBoundQ (π z) hzN)

set_option maxHeartbeats 720000 in
/-- Any full lower sharp cleanup of the selected native support prepares
its actual upper row. All original ordered labels remain and prepared
rows disjoint from the lower footprint retain their same pullback support. -/
theorem actual_retained_prepared_row_of_lower_sharp_cleanup (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (hOrd : ∀ x ∈ N,∀ j,ordinaryTraceOrder N (oldResidualPart N old born j) x ≤ 1)
    (i : Fin old.length) (P : Finset (Fin old.length)) :
    let L := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := remainingBoundary old born i
    let D := originalSharpBadLocus (n := n) L F
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y), IsGeoTestTower (geometricTemplate L F) R →
      CurrentSharpCentres L F R → CentresOver D R →
      HasNormalCrossings n (geoTransformAlong (geometricTemplate L F) R).N
        (geoTransformAlong (geometricTemplate L F) R).E →
      (geoTransformAlong (geometricTemplate L F) R).N ⊆
        closure ((geoTransformAlong (geometricTemplate L F) R).N \
          ⋃ G ∈ (geoTransformAlong (geometricTemplate L F) R).E,G) →
      (∀ j ∈ P,RetainedRowPrepared N old born j (.refl : BlowupTower X X) ∧
        Disjoint D (retainedRowSupport N old born j (.refl : BlowupTower X X))) →
      IsGeoTestTower (geometricTemplate N born) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R ∧
      CurrentSharpCentres N (old ++ born) R ∧
      RetainedRowPrepared N old born i R ∧ retainedRowSupport N old born i R = strictAlong R L ∧
      (∀ j ∈ P,RetainedRowPrepared N old born j R ∧
        retainedRowSupport N old born j R =
          R.proj ⁻¹' retainedRowSupport N old born j (.refl : BlowupTower X X)) := by
  intro L F D Y R hLow hSharp hOver hNC hDenseLow hOld
  obtain ⟨hPar,hFull,_hL,hSupport,_hIdeal,hBoundary⟩ :=
    actual_retained_selected_lower_boundary_history hn hN hE hTr hdense hOrd i R hLow
  obtain ⟨hSharpUpper,hOrder⟩ :=
    actual_retained_selected_lower_sharp_and_order hn hN hE hTr hdense hOrd i R hLow hSharp
  have hNLow : (geoTransformAlong (geometricTemplate L F) R).N = strictAlong R L :=
    N_geoTransformAlong _ R
  rw [hNLow, hBoundary, ←hSupport] at hNC hDenseLow
  refine ⟨hPar,hFull,hSharpUpper,⟨hOrder,hNC,hDenseLow⟩,hSupport,?_⟩
  intro j hj
  exact retained_prepared_row_of_disjoint_footprint hn hN hE hTr hdense j
    (hOld j hj).1 (hOld j hj).2 R hPar hOver

end
end Hironaka.HironakaG4RetainedSelectedLowerLift
