import Hironaka.Resolution.HironakaG4RetainedDefectCompactRank
import Hironaka.Resolution.HironakaG4OrderedDefectStamp
import Hironaka.Resolution.HironakaG4LocalJointProfileMask
import Hironaka.Resolution.HironakaG4JointProfileSupport
import Hironaka.Resolution.HironakaG4SharpClosedCrestPatch
import Hironaka.Resolution.HironakaG4RetainedRankTowerIso

/-! A first actual sharp history for a maximal retained defect crest over a
compact enclosure. Both canonical local generation and whole patched tests
are recorded on their literal physical domains. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedDefectFirstCrest
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail HomogenizedGlueingTower
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  RestrictEmptyTower MaxLocusLocal RelativePrincipalizationSpan
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBoundaryMaskBlock
  HironakaActualFiniteMarkedSumHistories HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4PreparedCentreCoordinates HironakaG34JointMaskEquivariance
  HironakaG4RetainedDefectCompactRank HironakaG4OrderedDefectStamp HironakaG4LocalJointProfileMask
  HironakaG4JointProfileSupport HironakaG4SharpClosedCrestPatch
  HironakaG4RetainedFactorOpenComparison HironakaG4RetainedRankOpenComparison HironakaG4RetainedRankTowerIso
open ResolutionInvariantSpec (IsCanonical IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n}

set_option maxHeartbeats 1000000 in
/-- Construct the actual first closed-crest history at a specified defect
point. The output enclosure lies inside the supplied rank-bound open. -/
theorem exists_retained_defect_first_closed_crest_of_rank_bound_with_domain (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    {x : X} (hx : x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born))
    (U : Opens X) (hKU : K ⊆ U)
    (hMax : ∀ y ∈ U, y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
      retainedDefectRank N old born y ≤ retainedDefectRank N old born x) :
    let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
    let q := ∑ i,r i
    let P := inactiveCanonicalRows N old born r x
    let C := retainedDefectCrest N old born r P
    let M := jointProfileMarked N old born q P
    ∃ (O V : Opens X), K ⊆ O ∧ O ≤ U ∧ C ∩ (O : Set X) ⊆ V ∧
      (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
        retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧ ∃ (hVO : V ≤ O)
      (A Y Z : CMfd.{u} n) (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
      (T : BlowupTower A Z) (Q : BlowupTower (CMfd.of (n := n) O) Y),
      let L := MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M
      IsInvDomain (n+1) L ∧
      (∀ y ∈ O,y ∈ C ↔ y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
        retainedDefectOrderedRank N old born y = retainedDefectOrderedRank N old born x) ∧
      (∀ y ∈ V,y ∈ M.cosupp ↔ y ∈ C) ∧
      IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) T ∧
      IsGeoResolution L T ∧
      IsGeoTestTower (geometricTemplate (univ : Set O)
        ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
      CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
        ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
      CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
      (let no := (Subtype.val : O → X)
       let NO := no ⁻¹' N
       let OO := old.map (no ⁻¹' ·)
       let BO := born.map (no ⁻¹' ·)
       ∀ z ∈ strictAlong Q NO, no (Q.proj z) ∈ C →
         retainedDefectRankAlong NO OO BO Q z < toLex (q,P.card)) ∧
      ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  classical
  obtain ⟨V,hVU,hq,hC,_hxC,hCover,_,hCtrl,hExact⟩ :=
    exists_retained_defect_crest_of_rank_bound hn hN hE hTr hdense hClosed U hx.2 hMax
  let J := oldResidualPart N old born
  let r := fun i => ordinaryTraceOrder N (J i) x
  let q := ∑ i,r i
  let P := inactiveCanonicalRows N old born r x
  let C := retainedDefectCrest N old born r P
  let M := jointProfileMarked N old born q P
  have hP : ∀ i ∈ P,r i = 0 := fun _ hi => (Finset.mem_filter.mp hi).2.1
  have hMI : M.ideal.IsCoherent := isCoherent_jointProfileMarked hn hN hE hTr hdense q P
  have hMFields : M.N = N ∧ M.E = born := by
    change (finiteSum (canonicalProductMarked N old born q)
      (P.toList.map (canonicalFactorMarked N old born))).N = N ∧
      (finiteSum (canonicalProductMarked N old born q)
      (P.toList.map (canonicalFactorMarked N old born))).E = born
    cases (P.toList.map (canonicalFactorMarked N old born)) <;> exact ⟨rfl,rfl⟩
  have hMN : IsClosedSubmanifold n M.N := hMFields.1.symm ▸ hN
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
    (.refl : BlowupTower X X) trivial).2.2.2
  have hCos {y : X} (hy : y ∈ V) : y ∈ M.cosupp ↔ y ∈ C := by
    have hMark := jointProfileMarked_cosupp_iff_actual_profile_mask_at hn hN hE hTr hdense r q
      hq rfl P hP y (fun _ => (hCtrl y hy).1)
      (fun _ _ => Finset.card_le_card (hCtrl y hy).2.2)
    rw [hMark, hExact y (hVU hy)]
    constructor
    · rintro ⟨hyN,hRows,hMask⟩
      refine ⟨⟨hyN,?_⟩,hRows,hMask⟩
      have hOrd : ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal y=q := by
        have hY := hOrder y hyN
        change ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal y =
          ∑ i,ordinaryTraceOrder N (J i) y at hY
        exact hY.trans (Finset.sum_congr rfl (fun i _ => hRows i))
      rw [←hMeaning,hOrd]
      exact (hCtrl y hy).2.1
    · exact fun h => ⟨h.1.1,h.2.1,h.2.2⟩
  let nv := (Subtype.val : V → X)
  let XV := CMfd.of (n := n) V
  let NV := nv ⁻¹' N
  let OV := old.map (nv ⁻¹' ·)
  let BV := born.map (nv ⁻¹' ·)
  let e : Fin old.length ≃ Fin OV.length := finCongr (List.length_map _).symm
  let rV := fun j => r (e.symm j)
  let PV := P.map e.toEmbedding
  obtain ⟨hNV,hEV,hTV,hDenseV,hJoint,hSumV,hPV,hOrdV,hCountV,hBoundV⟩ :=
    retained_joint_profile_open_data hn hN hE hTr hdense V r q rfl
      (fun y hy _ => (hCtrl y hy).1)
      (fun y hy _ _ => (hCtrl y hy).2.1) P hP
      (fun y hy _ _ => Finset.card_le_card (hCtrl y hy).2.2)
  have hKV : K ∩ C ⊆ V := fun y hy => hCover ⟨hy.2,hKU hy.1⟩
  have hCompactV : IsCompact (nv ⁻¹' (K ∩ C)) := by
    apply Subtype.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset (show K ∩ C ⊆ Set.range nv from
      fun y hy => ⟨⟨y,hKV hy⟩,rfl⟩)]
    exact hK.inter_right hC
  obtain ⟨W,hKW,Z,T,hCan,hRes,hRead,_hProdOver,hOver⟩ :=
    exists_actual_retained_joint_mask_locally_on_compact (X := XV) hn hNV hEV hTV hDenseV
      rV q hq hSumV hOrdV hCountV PV hPV hBoundV hCompactV
  let A := CMfd.of (n := n) W
  let f := nv ∘ (Subtype.val : W → V)
  let V' : Opens X := ⟨nv '' (W : Set V), V.isOpen.isOpenMap_subtype_val _ W.isOpen⟩
  have hVW (y : V) : y ∈ W ↔ y.val ∈ V' := by
    exact ⟨fun h => ⟨y,h,rfl⟩,fun ⟨z,hz,hzy⟩ => (Subtype.ext hzy : z=y) ▸ hz⟩
  have hV'V : V' ≤ V := by
    intro y hy
    obtain ⟨z,_hz,hzy⟩ := hy
    exact hzy ▸ z.property
  have hKV' : K ∩ C ⊆ V' := fun y hy => (hVW ⟨y,hKV hy⟩).mp (hKW hy)
  let ψ := MaxLocusLocal.nestedDiffeo (n := n) V W V' hVW hV'V
  have hMarker : MarkedIdeal.pullback (Subtype.val : W → V)
      (jointProfileMarked (X := XV) NV OV BV q PV) = MarkedIdeal.pullback f M := by
    rw [← show MarkedIdeal.pullback nv M = jointProfileMarked (X := XV) NV OV BV q PV from hJoint]
    exact StepOneTangentChange.pullback_pullback_of_comp hMI
      contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
  have hDomV := (actual_retained_boundary_joint_step (X := XV) (Y := XV)
    hn hNV hEV hTV hDenseV rV q hq hSumV hOrdV PV hPV hBoundV).1
  have hDomW := InvDomainTowerAlong.isInvDomain_pullback_val W hDomV
  rw [hMarker] at hCan hRes hDomW
  have hCosV : (jointProfileMarked (X := XV) NV OV BV q PV).cosupp = nv ⁻¹' C := by
    rw [← show MarkedIdeal.pullback nv M = jointProfileMarked (X := XV) NV OV BV q PV from hJoint]
    rw [cosupp_pullback_val M (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hMI h) V]
    exact Set.ext (fun y => hCos y.property)
  have hOverT : CentresOver (f ⁻¹' C) T := by
    rw [hCosV] at hOver
    exact hOver
  have hGeom :
      IsGeoTestTower (geometricTemplate (X := A) (univ : Set A) ((old ++ born).map (f ⁻¹' ·))) T ∧
        CurrentSharpCentres (f ⁻¹' N) ((old ++ born).map (f ⁻¹' ·)) T := by
    have hF := (hRead.2.2.1 0).2.1
    have hS := (hRead.2.2.1 0).2.2.1
    have hMap (L : List (Set X)) :
        (L.map (nv ⁻¹' ·)).map ((Subtype.val : W → V) ⁻¹' ·) = L.map (f ⁻¹' ·) := by
      rw [List.map_map]
      rfl
    have hEMap : OV.map ((Subtype.val : W → V) ⁻¹' ·) ++
        BV.map ((Subtype.val : W → V) ⁻¹' ·) = (old ++ born).map (f ⁻¹' ·) := by
      rw [List.map_append,←hMap old,←hMap born]
    rw [hEMap] at hF hS
    cases T <;> exact ⟨hF,hS⟩
  obtain ⟨O,hKO,hOU,hCOV',hV'O,Y,Q,hFull,hQMark,hSharp,hOverQ,χ,hχ⟩ :=
    exists_current_sharp_closed_crest_patch_over_open_equiv N (old ++ born) M hMN hMI
      U V' (hV'V.trans hVU) hC hKU hKV' ψ T hOverT hGeom.1 hRes.1 hGeom.2

  let vw := (Subtype.val : W → V)
  let NW := vw ⁻¹' NV
  let OW := OV.map (vw ⁻¹' ·)
  let BW := BV.map (vw ⁻¹' ·)
  let eW : Fin OV.length ≃ Fin OW.length := finCongr (List.length_map _).symm
  let rW := fun j => rV (eW.symm j)
  let PW := PV.map eW.toEmbedding
  obtain ⟨hNW,hEW,hTW,hDenseW,hMarkW,hSumW,hPW,hOrdW,_hCountW,hBoundW⟩ :=
    retained_joint_profile_open_data (X := XV) hn hNV hEV hTV hDenseV W rV q hSumV
      (fun x _ => hOrdV x) (fun x _ => hCountV x) PV hPV (fun x _ => hBoundV x)
  have hMarkWC : (jointProfileMarked (X := A) NW OW BW q PW).cosupp = f ⁻¹' C := by
    have hc := isCoherent_jointProfileMarked (X := XV) hn hNV hEV hTV hDenseV q PV
    rw [←hMarkW, cosupp_pullback_val _ (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hc h) W]
    rw [hCosV]
    rfl
  have hSmallRank (t : Z) (ht : t ∈ strictAlong T (f ⁻¹' N)) (htC : f (T.proj t) ∈ C) :
      retainedDefectRankAlong NW OW BW T t < toLex (q,P.card) := by
    have htN : t ∈ (geoTransformAlong (geometricTemplate NW BW) T).N :=
      (N_geoTransformAlong _ T).symm ▸ ht
    have htF : T.proj t ∈ (jointProfileMarked (X := A) NW OW BW q PW).cosupp := hMarkWC.symm ▸ htC
    have hDrop := retained_defect_rank_decrease_of_native_joint_mask
      hn hNW hEW hTW hDenseW rW q hq hSumW hOrdW PW hPW hBoundW T hRead t htN htF
    simpa only [PW,PV,Finset.card_map] using hDrop
  let XO := CMfd.of (n := n) O
  let no := (Subtype.val : O → X)
  let NO := no ⁻¹' N
  let OO := old.map (no ⁻¹' ·)
  let BO := born.map (no ⁻¹' ·)
  have hQGeo := isGeoTestTower_geometricTemplate_of_actual_test
    (MarkedIdeal.pullback no M) Q hQMark
  have hMQN : (MarkedIdeal.pullback no M).N = NO := by
    change no ⁻¹' M.N = no ⁻¹' N
    rw [hMFields.1]
  have hMQE : (MarkedIdeal.pullback no M).E = BO := by
    change M.E.map (no ⁻¹' ·) = born.map (no ⁻¹' ·)
    rw [hMFields.2]
  rw [hMQN,hMQE] at hQGeo
  have hNO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN O
  have hEO : IsSNCDivisor n (OO ++ BO) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hTO : IsTransverse n NO BO := isTransverse_preimage (pullsBackCoordinates_val O) hTr
  have hDenseO : NO ⊆ closure (NO \ ⋃ H ∈ OO ++ BO,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense O
  have hQFull : IsGeoTestTower (geometricTemplate (X := XO) (univ : Set O) (OO ++ BO)) Q := by
    simpa only [List.map_append] using hFull
  let B := nestedOpens O V'
  let β := (nestedOpensDiffeo (n := n) hV'O).trans ψ.symm
  have hStrict (z : Y) (hz : z ∈ strictAlong Q NO) (hzC : no (Q.proj z) ∈ C) :
      retainedDefectRankAlong NO OO BO Q z < toLex (q,P.card) := by
    have hzB : Q.proj z ∈ B := hCOV' ⟨hzC,(Q.proj z).property⟩
    let p : openPreimage Q B := ⟨z,hzB⟩
    let t := χ p
    have htProj : f (T.proj t) = no (Q.proj z) := by
      change f (T.proj (χ p)) = no (Q.proj p.val)
      rw [←hχ.proj_comm p]
      change no (((restrict B Q).proj p).val) = no (Q.proj p.val)
      exact congrArg no (proj_restrict B Q p)
    have hCarrier := hχ.symm.strictAlong_eq ((Subtype.val : B → O) ⁻¹' NO)
    rw [strictAlong_restrict] at hCarrier
    have ht : t ∈ strictAlong T (f ⁻¹' N) := by
      change t ∈ strictAlong T (β.symm ⁻¹' ((Subtype.val : B → O) ⁻¹' NO))
      rw [hCarrier]
      change (χ.symm (χ p)).val ∈ strictAlong Q NO
      rw [χ.symm_apply_apply]
      exact hz
    have hRank := actual_retained_rank_open_tower_iso_over_equiv (X := XO)
      hn hNO hEO hTO hDenseO B Q hQGeo hQFull β.symm T χ.symm hχ.symm t
    let a := (Subtype.val : B → O) ∘ β.symm
    have hMap (L : List (Set X)) :
        (L.map (no ⁻¹' ·)).map (a ⁻¹' ·) = (L.map (nv ⁻¹' ·)).map (vw ⁻¹' ·) := by
      rw [List.map_map,List.map_map]
      rfl
    change retainedDefectRankAlong NW (OO.map (a ⁻¹' ·)) (BO.map (a ⁻¹' ·)) T t =
      retainedDefectRankAlong NO OO BO Q (χ.symm (χ p)).val at hRank
    rw [show OO.map (a ⁻¹' ·) = OW from hMap old,
      show BO.map (a ⁻¹' ·) = BW from hMap born,χ.symm_apply_apply] at hRank
    exact hRank ▸ hSmallRank t ht (htProj.symm ▸ hzC)
  have hStamp (y : X) (hy : y ∈ O) :
      y ∈ C ↔ y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
        retainedDefectOrderedRank N old born y = retainedDefectOrderedRank N old born x := by
    rw [hExact y (hOU hy)]
    constructor
    · rintro ⟨hyD,hRows,hMask⟩
      refine ⟨hyD,?_⟩
      change orderedDefectStampRank (fun i => ordinaryTraceOrder N (J i) y)
        (inactiveCanonicalRows N old born (fun i => ordinaryTraceOrder N (J i) y) y) =
          orderedDefectStampRank r P
      rw [funext hRows,hMask]
    · rintro ⟨hyD,hRank⟩
      have h := retainedDefectStamp_eq_of_orderedRank_eq N old born hRank
      have hRows := congrArg Prod.fst h
      have hMask := congrArg Prod.snd h
      change (fun i => ordinaryTraceOrder N (J i) y) = r at hRows
      change inactiveCanonicalRows N old born (fun i => ordinaryTraceOrder N (J i) y) y = P at hMask
      rw [hRows] at hMask
      exact ⟨hyD,congrFun hRows,hMask⟩
  exact ⟨O,V',hKO,hOU,hCOV',fun y hy => hMax y (hOU hy),hV'O,A,Y,Z,ψ,T,Q,hDomW,
    hStamp,fun y hy => hCos (hV'V hy),hCan,hRes,hFull,hQMark,hSharp,hOverQ,hStrict,χ,hχ⟩

set_option maxHeartbeats 1000000 in
/-- Construct the actual first closed-crest history at a specified defect
point. The output enclosure lies inside the supplied rank-bound open. -/
theorem exists_retained_defect_first_closed_crest_of_rank_bound (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    {x : X} (hx : x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born))
    (U : Opens X) (hKU : K ⊆ U)
    (hMax : ∀ y ∈ U, y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
      retainedDefectRank N old born y ≤ retainedDefectRank N old born x) :
    let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
    let q := ∑ i,r i
    let P := inactiveCanonicalRows N old born r x
    let C := retainedDefectCrest N old born r P
    let M := jointProfileMarked N old born q P
    ∃ (O V : Opens X), K ⊆ O ∧ O ≤ U ∧ C ∩ (O : Set X) ⊆ V ∧
      (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
        retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧ ∃ (hVO : V ≤ O)
      (A Y Z : CMfd.{u} n) (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
      (T : BlowupTower A Z) (Q : BlowupTower (CMfd.of (n := n) O) Y),
      let L := MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M
      IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) T ∧
      IsGeoResolution L T ∧
      IsGeoTestTower (geometricTemplate (univ : Set O)
        ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
      CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
        ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
      CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
      (let no := (Subtype.val : O → X)
       let NO := no ⁻¹' N
       let OO := old.map (no ⁻¹' ·)
       let BO := born.map (no ⁻¹' ·)
       ∀ z ∈ strictAlong Q NO, no (Q.proj z) ∈ C →
         retainedDefectRankAlong NO OO BO Q z < toLex (q,P.card)) ∧
      ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  obtain ⟨O,V,hKO,hOU,hCV,hBound,hVO,A,Y,Z,ψ,T,Q,_hDom,_hStamp,_hCos,hCan,hRes,hFull,
    hMark,hSharp,hOver,hDrop,χ,hχ⟩ :=
    exists_retained_defect_first_closed_crest_of_rank_bound_with_domain hn hN hE hTr hdense
      hK hClosed hx U hKU hMax
  exact ⟨O,V,hKO,hOU,hCV,hBound,hVO,A,Y,Z,ψ,T,Q,hCan,hRes,hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩

/-- Select a pair-rank maximum and build its first closed-crest history. -/
theorem exists_retained_defect_first_closed_crest_with_rank_decrease (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
      let q := ∑ i,r i
      let P := inactiveCanonicalRows N old born r x
      let C := retainedDefectCrest N old born r P
      let M := jointProfileMarked N old born q P
      ∃ (O V : Opens X), K ⊆ O ∧ C ∩ (O : Set X) ⊆ V ∧
        (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧ ∃ (hVO : V ≤ O)
        (A Y Z : CMfd.{u} n) (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
        (T : BlowupTower A Z) (Q : BlowupTower (CMfd.of (n := n) O) Y),
        let L := MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M
        IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) T ∧
        IsGeoResolution L T ∧
        IsGeoTestTower (geometricTemplate (univ : Set O)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
        IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
        CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
        (let no := (Subtype.val : O → X)
         let NO := no ⁻¹' N
         let OO := old.map (no ⁻¹' ·)
         let BO := born.map (no ⁻¹' ·)
         ∀ z ∈ strictAlong Q NO, no (Q.proj z) ∈ C →
           retainedDefectRankAlong NO OO BO Q z < toLex (q,P.card)) ∧
        ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
          IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  obtain ⟨x,hx,U,hKU,hMax⟩ :=
    exists_retained_defect_rank_max_near_compact hn hN hE hTr hdense hK hClosed hNonempty
  obtain ⟨O,V,hKO,_hOU,hCV,hBound,hVO,A,Y,Z,ψ,T,Q,hCan,hRes,hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩ :=
    exists_retained_defect_first_closed_crest_of_rank_bound hn hN hE hTr hdense hK hClosed hx U hKU hMax
  exact ⟨x,hx,O,V,hKO,hCV,hBound,hVO,A,Y,Z,ψ,T,Q,hCan,hRes,hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩

/-- Select the refined numerical stamp, then use the same actual
closed-crest construction at that point. The refined rank is bounded
on the entire final enclosure. -/
theorem exists_ordered_retained_defect_first_closed_crest_with_domain (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
      let q := ∑ i,r i
      let P := inactiveCanonicalRows N old born r x
      let C := retainedDefectCrest N old born r P
      let M := jointProfileMarked N old born q P
      ∃ (O V : Opens X), K ⊆ O ∧ C ∩ (O : Set X) ⊆ V ∧
        (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧
        (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x) ∧ ∃ (hVO : V ≤ O)
        (A Y Z : CMfd.{u} n) (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
        (T : BlowupTower A Z) (Q : BlowupTower (CMfd.of (n := n) O) Y),
        let L := MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M
        IsInvDomain (n+1) L ∧
        (∀ y ∈ O,y ∈ C ↔ y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
          retainedDefectOrderedRank N old born y = retainedDefectOrderedRank N old born x) ∧
        (∀ y ∈ V,y ∈ M.cosupp ↔ y ∈ C) ∧
        IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) T ∧
        IsGeoResolution L T ∧
        IsGeoTestTower (geometricTemplate (univ : Set O)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
        IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
        CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
        (let no := (Subtype.val : O → X)
         let NO := no ⁻¹' N
         let OO := old.map (no ⁻¹' ·)
         let BO := born.map (no ⁻¹' ·)
         ∀ z ∈ strictAlong Q NO, no (Q.proj z) ∈ C →
           retainedDefectRankAlong NO OO BO Q z < toLex (q,P.card)) ∧
        ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
          IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  obtain ⟨x,hx,U,hKU,hMax⟩ :=
    exists_ordered_retained_defect_rank_max_near_compact hn hN hE hTr hdense hK hClosed hNonempty
  have hPair (y : X) (hy : y ∈ U) (hyD : y ∈ actualFamilyDistinctDefect N
      (oldResidualPart N old born)) :
      retainedDefectRank N old born y ≤ retainedDefectRank N old born x :=
    retainedDefectRank_le_of_orderedRank_le N old born (hMax y hy hyD)
  obtain ⟨O,V,hKO,hOU,hCV,hBound,hVO,A,Y,Z,ψ,T,Q,hDom,hStamp,hCos,hCan,hRes,hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩ :=
    exists_retained_defect_first_closed_crest_of_rank_bound_with_domain hn hN hE hTr hdense hK hClosed hx U hKU hPair
  exact ⟨x,hx,O,V,hKO,hCV,hBound,fun y hy => hMax y (hOU hy),hVO,A,Y,Z,ψ,T,Q,hDom,hStamp,hCos,hCan,hRes,
    hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩

/-- Select the refined numerical stamp, then use the same actual
closed-crest construction at that point. The refined rank is bounded
on the entire final enclosure. -/
theorem exists_ordered_retained_defect_first_closed_crest (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
      let q := ∑ i,r i
      let P := inactiveCanonicalRows N old born r x
      let C := retainedDefectCrest N old born r P
      let M := jointProfileMarked N old born q P
      ∃ (O V : Opens X), K ⊆ O ∧ C ∩ (O : Set X) ⊆ V ∧
        (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧
        (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x) ∧ ∃ (hVO : V ≤ O)
        (A Y Z : CMfd.{u} n) (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
        (T : BlowupTower A Z) (Q : BlowupTower (CMfd.of (n := n) O) Y),
        let L := MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M
        IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) T ∧
        IsGeoResolution L T ∧
        IsGeoTestTower (geometricTemplate (univ : Set O)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
        IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
        CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
        (let no := (Subtype.val : O → X)
         let NO := no ⁻¹' N
         let OO := old.map (no ⁻¹' ·)
         let BO := born.map (no ⁻¹' ·)
         ∀ z ∈ strictAlong Q NO, no (Q.proj z) ∈ C →
           retainedDefectRankAlong NO OO BO Q z < toLex (q,P.card)) ∧
        ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
          IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  obtain ⟨x,hx,O,V,hKO,hCV,hBound,hMax,hVO,A,Y,Z,ψ,T,Q,_hDom,_hStamp,_hCos,hCan,hRes,
    hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩ :=
    exists_ordered_retained_defect_first_closed_crest_with_domain hn hN hE hTr hdense hK hClosed hNonempty
  exact ⟨x,hx,O,V,hKO,hCV,hBound,hMax,hVO,A,Y,Z,ψ,T,Q,hCan,hRes,hFull,hMark,hSharp,hOver,hDrop,χ,hχ⟩

/-- The original first-crest interface follows from the actual strict
rank-decrease construction. -/
theorem exists_retained_defect_first_closed_crest (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
      let q := ∑ i,r i
      let P := inactiveCanonicalRows N old born r x
      let C := retainedDefectCrest N old born r P
      let M := jointProfileMarked N old born q P
      ∃ (O V : Opens X), K ⊆ O ∧ C ∩ (O : Set X) ⊆ V ∧
        (∀ y ∈ O,y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectRank N old born y ≤ retainedDefectRank N old born x) ∧ ∃ (hVO : V ≤ O)
        (A Y Z : CMfd.{u} n) (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
        (T : BlowupTower A Z) (Q : BlowupTower (CMfd.of (n := n) O) Y),
        let L := MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M
        IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) T ∧
        IsGeoResolution L T ∧
        IsGeoTestTower (geometricTemplate (univ : Set O)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
        IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
        CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
          ((old ++ born).map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
        ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
          IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  obtain ⟨x,hx,O,V,hKO,hCV,hMax,hVO,A,Y,Z,ψ,T,Q,hCan,hRes,hFull,hMark,hSharp,hOver,_hDrop,χ,hχ⟩ :=
    exists_retained_defect_first_closed_crest_with_rank_decrease hn hN hE hTr hdense hK hClosed hNonempty
  exact ⟨x,hx,O,V,hKO,hCV,hMax,hVO,A,Y,Z,ψ,T,Q,hCan,hRes,hFull,hMark,hSharp,hOver,χ,hχ⟩

end
end Hironaka.HironakaG4RetainedDefectFirstCrest
