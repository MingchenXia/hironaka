import Hironaka.Resolution.HironakaG4OriginalSelectedLowerBoundaryHistory
import Hironaka.Resolution.HironakaG4EquimultipleRelativeOrder
import Hironaka.Resolution.HironakaG4OrderOneTransverseCoordinates
import Hironaka.Resolution.HironakaSharpActualCurveGlobalBoundaryCoordinates

/-! Genuine initial canonical D_h units on the ENTIRE selected support
protect one OTHER original row along the SAME actual lower test history.
Source-first complete proof: hironaka-g4-selected-support-unit-row-order.tex.
No future order/unit/comparison packet or arbitrary all-row persistence. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SelectedSupportUnitRowOrder

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MemberInterTowerAlong
  MemberInterLocusAlong BlowupStrictSubmanifold BlowupRestrictOpen NormalCrossings
  NormalCrossingsInvariance NormalCrossingsComparison HironakaNormalCrossingsTransversality
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4RecordedTowerResidualCompatibility
  HironakaG4EquimultipleRelativeOrder HironakaG4OrderOneTransverseCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpActualCurveGlobalBoundaryCoordinates GermIdealOrder
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NonmonomialTransformAlong MarkedIdealOperationsAlong MarkedIdealRestrictOpen
  MarkedIdealOpenBiholomorphism MarkedIdealBiholomorphism IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem normalCrossingsAt_singleton_of_unit_part (hn : 0 < n)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (B : List (Set X))
    (hcJ : (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).IsCoherent)
    (hnzJ : ∀ x ∈ N,IsNonzeroAlongAt N
      (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B) x)
    {x : X} (hx : x ∈ N)
    (hOrd : ordinaryTraceOrder N
      (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B) x ≤ 1)
    (hunit : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1) :
    normalCrossingsAt (n := n) N [H] x := by
  by_contra hNC
  have hraw : x ∈ cosupport n N (vanishingIdeal (n := n) H) 2 := by
    rw [←originalSharpBadLocus_singleton_eq_cosupport hn hN hH hdense]
    exact ⟨hx,hNC⟩
  let I := restrictOn n N (vanishingIdeal (n := n) H)
  have hnorm : x ∈ cosupport n N I 2 :=
    cosupport_subset_of_restrictLe restrictLe_restrictOn 2 hraw
  have hdouble : x ∈ cosupport n N (restrictOn n N I) 2 :=
    cosupport_subset_of_restrictLe restrictLe_restrictOn 2 hnorm
  have hcosJ : x ∈ cosupport n N (nonmonomialPartAlong n N I B) 2 := by
    refine ⟨hx,fun g hg => ?_⟩
    apply hdouble.2 g
    simpa only [Pi.one_apply,one_mul] using hg.2 1 hunit
  have hpos := (ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx 2).mp hcosJ
  omega

private theorem normalCrossingsAt_strict_singleton_over_support
    {N S H : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hS : IsClosedSubmanifold n S) (hSN : S ⊆ N)
    (hH : IsSNCDivisor n [H]) (hdense : N ⊆ closure (N \ H)) (hHF : H ∈ F)
    (hNC : ∀ x ∈ S,normalCrossingsAt (n := n) N [H] x)
    (R : BlowupTower X Y) (hR : IsGeoTestTower (geometricTemplate S F) R)
    {y : Y} (hy : y ∈ strictAlong R N) (hyS : R.proj y ∈ S) :
    normalCrossingsAt (n := n) (strictAlong R N) [strictAlong R H] y := by
  have hNear := eventually_normalCrossingsAt hN.1 hH.1 (hNC _ hyS)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hNear
  let U : Opens X := ⟨V,hVo⟩
  let NU : Set U := (Subtype.val : U → X) ⁻¹' N
  let SU : Set U := (Subtype.val : U → X) ⁻¹' S
  let HU : Set U := (Subtype.val : U → X) ⁻¹' H
  let FU : List (Set U) := F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hNU : IsClosedSubmanifold n NU := isClosedSubmanifold_preimage_val hN U
  have hHU : IsSNCDivisor n [HU] := by
    simpa only [List.map_singleton] using
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hH
  have hDenseU : NU ⊆ closure (NU \ HU) := by
    intro z hz
    have hc : z ∈ (Subtype.val : U → X) ⁻¹' closure (N \ H) := hdense hz
    have he : (Subtype.val : U → X) ⁻¹' closure (N \ H)=
        closure ((Subtype.val : U → X) ⁻¹' (N \ H)) :=
      U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val (N \ H)
    have hc' := (Set.ext_iff.mp he z).mp hc
    rw [preimage_sdiff] at hc'
    exact hc'
  have hNCU : HasNormalCrossings n NU [HU] := by
    intro z _hz
    exact normalCrossingsAt_singleton_preimage_val_iff.mpr (hV z.property)
  have hTransU : IsTransverse n NU [HU] :=
    isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNCU (by simpa using hDenseU)
  let M := geometricTemplate (X := CMfd.of (n := n) U) NU [HU]
  have hwM : M.IsWellFormed := ⟨hNU,isCoherent_unitIdeal,hHU,hTransU⟩
  have hRU : IsGeoTestTower (geometricTemplate (X := CMfd.of (n := n) U) SU FU)
      (restrict U R) := by
    simpa [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal,
      SU,FU] using isGeoTestTower_restrict U hS isCoherent_unitIdeal R hR
  have hHsub : [HU].Sublist FU :=
    List.singleton_sublist.mpr (List.mem_map.mpr ⟨H,hHF,rfl⟩)
  have hTest : IsGeoTestTower M (restrict U R) :=
    (actual_zero_mark_test_of_lower_test M hwM rfl
      (fun _ hz => hSN hz) hHsub (restrict U R) hRU).1
  have hwEnd := isWellFormed_geoTransformAlong hwM (restrict U R) hTest
  let K := geometricTemplate (X := CMfd.of (n := n) U) (univ : Set U) []
  have hMem : strictAlong (restrict U R) HU ∈ (geoTransformAlong M (restrict U R)).E := by
    rw [boundary_geoTransformAlong_decomposition M K rfl (restrict U R)]
    exact List.mem_append_left _ (List.mem_map_of_mem (by change HU ∈ [HU]; simp))
  have hOne : IsTransverse n (geoTransformAlong M (restrict U R)).N
      [strictAlong (restrict U R) HU] :=
    isTransverse_of_forall_mem hwEnd.isTransverse (fun D hD => by
      rw [List.mem_singleton] at hD
      subst D
      exact hMem)
  let yU : openPreimage R U := ⟨y,hxV⟩
  have hyU : yU ∈ (geoTransformAlong M (restrict U R)).N := by
    rw [N_geoTransformAlong]
    change yU ∈ strictAlong (restrict U R) ((Subtype.val : U → X) ⁻¹' N)
    rw [strictAlong_restrict U R N]
    exact hy
  have hPoint := hOne.hasNormalCrossings yU hyU
  have hEndN : (geoTransformAlong M (restrict U R)).N=
      strictAlong (restrict U R) NU := N_geoTransformAlong _ _
  rw [hEndN] at hPoint
  change normalCrossingsAt (n := n) (strictAlong (restrict U R) NU)
    [strictAlong (restrict U R) HU] yU at hPoint
  dsimp only [NU,HU] at hPoint
  rw [strictAlong_restrict U R N,strictAlong_restrict U R H] at hPoint
  exact normalCrossingsAt_singleton_preimage_val_iff.mp hPoint

private theorem original_other_row_order_off_selected_support
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i h : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrdi : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hOrdh : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ B.E
    let S := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),IsGeoTestTower (geometricTemplate S F) R →
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        R.proj y ∉ S →
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) (T.append R)).ideal y ≤ 1 := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ B.E
  let S := A.N ∩ A.ideal.zeroLocus
  obtain ⟨hS,_hWhole,hTails⟩ := actual_original_selected_lower_boundary_history
    hn hW hE hdense i T hT hFull hOrdi
  dsimp only
  intro Q R
  induction R with
  | refl =>
    intro _hR y hy _hOff
    rw [BlowupTower.append_refl] at hy ⊢
    have hNh : (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).N=
        (geoTransformAlong (geometricTemplate W []) T).N :=
      (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get h)) T).1
    rw [←hNh] at hy ⊢
    exact hOrdh y hy
  | step R C π hπ ih =>
    intro hR y hy hOff
    let M := chronologicalMarked (originalRelativeMemberMarked W (E.get h)) (T.append R)
    obtain ⟨hUpper,_hAmbient,_hRest⟩ := hTails R hR.1
    obtain ⟨hMN,_hME,_hMark,hwM,hnzM,hprM⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense h (T.append R) hUpper
    have hUpperStep := (hTails (.step R C π hπ) hR).1
    have hCN : C ⊆ M.N := by
      rw [hMN]
      exact hUpperStep.2.subset_N
    have hLowerN : (geoTransformAlong (geometricTemplate S F) R).N=strictAlong R S :=
      N_geoTransformAlong _ _
    have hCS : C ⊆ strictAlong R S := by
      rw [←hLowerN]
      exact hR.2.subset_N
    have hCOver : C ⊆ R.proj ⁻¹' S := hCS.trans (strictAlong_subset_preimage R hS.1)
    have hyC : π y ∉ C := fun hc => hOff (hCOver hc)
    have hNewN : (geoTransformAlong (geometricTemplate W [])
        (T.append (.step R C π hπ))).N=geoStrictTransform π C M.N := by
      change geoStrictTransform π C (geoTransformAlong (geometricTemplate W []) (T.append R)).N=
        geoStrictTransform π C M.N
      rw [hMN]
    have hyM : y ∈ geoStrictTransform π C M.N := by
      rw [←hNewN]
      exact hy
    have hyOldM : π y ∈ M.N :=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwM.isClosedSubmanifold_N.1 hyM
    have hyOld : π y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N :=
      hMN ▸ hyOldM
    have hBefore : ordinaryTraceOrder M.N M.ideal (π y) ≤ 1 := by
      rw [hMN]
      exact ih hR.1 (π y) hyOld hOff
    have hEq := nextRelativeStrict_order_eq_off_centre hn hwM.isClosedSubmanifold_N
      hwM.isCoherent hnzM hprM hπ hCN hyM hyC
    rw [hNewN]
    change ordinaryTraceOrder (geoStrictTransform π C M.N)
      (nextRelativeStrict M.N M.ideal C π) y ≤ 1
    exact hEq.trans_le hBefore

/-- A true CURRENT canonical other-row unit factor on the ENTIRE selected
support preserves that SAME ORIGINAL row's global order<=1 on any real lower test. -/
theorem actual_original_other_row_order_le_one_of_unit_on_selected
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i h : Fin E.length) (hne : h ≠ i)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrdi : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hOrdh : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal y ≤ 1)
    (hUnit : let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
      let B := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N ∩ A.ideal.zeroLocus,
        (monomialPartAlong n B.N
          (restrictOn n B.N (vanishingIdeal (n := n) (strictAlong T (E.get h)))) B.E).mem x 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ B.E
    let S := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),IsGeoTestTower (geometricTemplate S F) R →
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) (T.append R)).ideal y ≤ 1 := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ B.E
  let S := A.N ∩ A.ideal.zeroLocus
  let H := strictAlong T (E.get h)
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n B.N := hRecorded.1
  have hFullE := hRecorded.2.1
  have hDenseFull := hRecorded.2.2.2.1
  obtain ⟨_hcI,_hnzI,hNm,_hFactor⟩ := hRecorded.2.2.2.2 h
  have hHmem : H ∈ E.map (strictAlong T) ++ B.E :=
    List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E h))
  have hH : IsSNCDivisor n [H] :=
    isSNCDivisor_of_sublist hFullE (List.singleton_sublist.mpr hHmem)
  have hDenseH : B.N ⊆ closure (B.N \ H) := by
    apply hDenseFull.trans (closure_mono ?_)
    intro x hx
    exact ⟨hx.1,fun hxH => hx.2 (mem_iUnion₂.mpr ⟨H,hHmem,hxH⟩)⟩
  have hAN : A.N=B.N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  obtain ⟨hS,_hSelectedWhole,hTails⟩ := actual_original_selected_lower_boundary_history
    hn hW hE hdense i T hT hFull hOrdi
  have hSN : S ⊆ B.N := fun _ hx => hAN ▸ hx.1
  obtain ⟨hNh,_hEh,_hDh,hwJh,hnzJh,_hprJh⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense h T hT
  have hcNm : (nonmonomialPartAlong n B.N
      (restrictOn n B.N (vanishingIdeal (n := n) H)) B.E).IsCoherent := by
    rw [hNm]
    exact hwJh.isCoherent
  have hnzNm : ∀ x ∈ B.N,IsNonzeroAlongAt B.N
      (nonmonomialPartAlong n B.N (restrictOn n B.N (vanishingIdeal (n := n) H)) B.E) x := by
    rw [hNm,←hNh]
    exact hnzJh
  have hOrderNm : ∀ x ∈ B.N,ordinaryTraceOrder B.N
      (nonmonomialPartAlong n B.N (restrictOn n B.N (vanishingIdeal (n := n) H)) B.E) x ≤ 1 := by
    rw [hNm,←hNh]
    exact hOrdh
  have hNC : ∀ x ∈ S,normalCrossingsAt (n := n) B.N [H] x := by
    intro x hx
    exact normalCrossingsAt_singleton_of_unit_part hn hN hH hDenseH B.E hcNm hnzNm
      (hSN hx) (hOrderNm x (hSN hx)) (hUnit x hx)
  let j : Fin (E.map (strictAlong T)).length := ⟨h.val,by simp⟩
  have hGet : (E.map (strictAlong T)).get j=H := by simp [j,H]
  have hHF : H ∈ F :=
    List.mem_append_left _ (List.mem_eraseIdx_iff_getElem.mpr
      ⟨h.val,j.isLt,(fun heq => hne (Fin.ext heq)),by
        simpa only [List.get_eq_getElem] using hGet⟩)
  dsimp only
  intro Q R hR y hy
  by_cases hProj : R.proj y ∈ S
  · have hNAppend : (geoTransformAlong (geometricTemplate W []) (T.append R)).N=
        strictAlong R B.N := by
      calc
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N
            = strictAlong (T.append R) W := N_geoTransformAlong _ _
        _ = strictAlong R (strictAlong T W) := strictAlong_append T W R
        _ = strictAlong R B.N := congrArg (strictAlong R)
          (N_geoTransformAlong (geometricTemplate W []) T).symm
    have hHAppend : strictAlong R H=strictAlong (T.append R) (E.get h) :=
      (strictAlong_append T (E.get h) R).symm
    have hPoint := normalCrossingsAt_strict_singleton_over_support
      hN hS hSN hH hDenseH hHF hNC R hR (hNAppend ▸ hy) hProj
    rw [←hNAppend,hHAppend] at hPoint
    obtain ⟨hUpper,hAmbient,_hRest⟩ := hTails R hR
    have hNow := actual_recorded_tower_residual_dictionary hn hW hE hdense
      (T.append R) hUpper hAmbient
    have hNNow := hNow.1
    have hHmemNow : strictAlong (T.append R) (E.get h) ∈
        E.map (strictAlong (T.append R)) ++
          (geoTransformAlong (geometricTemplate W []) (T.append R)).E :=
      List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E h))
    have hHNow : IsSNCDivisor n [strictAlong (T.append R) (E.get h)] :=
      isSNCDivisor_of_sublist hNow.2.1 (List.singleton_sublist.mpr hHmemNow)
    have hDenseHNow : (geoTransformAlong (geometricTemplate W []) (T.append R)).N ⊆
        closure ((geoTransformAlong (geometricTemplate W []) (T.append R)).N \
          strictAlong (T.append R) (E.get h)) := by
      apply hNow.2.2.2.1.trans (closure_mono ?_)
      intro z hz
      exact ⟨hz.1,fun hzH => hz.2 (mem_iUnion₂.mpr ⟨_,hHmemNow,hzH⟩)⟩
    obtain ⟨hcINow,_hnzINow,hNmNow,_hFactorNow⟩ := hNow.2.2.2.2 h
    obtain ⟨hNhNow,_hEhNow,_hDhNow,hwJhNow,hnzJhNow,_hprJhNow⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense h
        (T.append R) hUpper
    have hJnZNow : ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) (T.append R)).ideal z := by
      rw [←hNhNow]
      exact hnzJhNow
    by_contra hNot
    have hGe : 2 ≤ ordinaryTraceOrder
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) (T.append R)).ideal y := by omega
    have hCosJ := (ordinaryTraceOrder_cosupport_iff hNNow hwJhNow.isCoherent hJnZNow hy 2).mpr hGe
    have hcHNow := VanishingIdealCoherent.isCoherent_vanishingIdeal
      (HironakaSharpSingleBoundaryTraceCentre.originalBoundary_isClosedSubmanifold hn hHNow)
    have hCosH : y ∈ cosupport n
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N
        (vanishingIdeal (n := n) (strictAlong (T.append R) (E.get h))) 2 := by
      refine ⟨hy,fun g hg => ?_⟩
      apply hCosJ.2 g
      rw [←hNmNow]
      exact le_nonmonomialPartAlong_self hcINow y g (le_restrictOn hcHNow y g hg)
    rw [←originalSharpBadLocus_singleton_eq_cosupport hn hNNow hHNow hDenseHNow] at hCosH
    exact hCosH.2 hPoint
  · exact original_other_row_order_off_selected_support hn hW hE hdense i h
      T hT hFull hOrdi hOrdh R hR y hy hProj

end
end Hironaka.HironakaG4SelectedSupportUnitRowOrder
