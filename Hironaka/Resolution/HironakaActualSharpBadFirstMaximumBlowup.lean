import Hironaka.Resolution.HironakaActualSharpBadMaximumProcessedSlice
import Hironaka.Resolution.HironakaG4OriginalSelectedLowerBadHistory
import Hironaka.Resolution.HironakaG4SharpBadFootprint
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCompactDriver
import Hironaka.Resolution.HironakaG4MixedOldResidualStep
import Hironaka.Resolution.HironakaG4SmoothSubcarrierResidualStep
import Hironaka.Resolution.HironakaSharpActualRelativeSaturationOpenNaturality
import Hironaka.Resolution.HironakaSharpActualMixedCurveContactEvolution

/-! ONE actual whole sharp-bad maximum blowup on the SAME original prefix.
Blueprint and independent full route peer precede implementation. No future
history/protection packet, unprocessed-order re-entry or termination claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSharpBadFirstMaximumBlowup
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism RestrictedIdealExtension
  RelativePrincipalizationSpan GermIdealOrder HironakaG4PreparedCentreCoordinates
  MonomialPartAlong DivisorExponentAlong HironakaSharpOriginalProductTraceOrder
  HironakaG4RecordedTowerResidualCompatibility HironakaG4ResidualInductionInputs
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4GeneralSharpBadLocus
  HironakaNormalCrossingsBoundaryTransform HironakaSharpActualCurveWholeBoundaryTransversality
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumNativeFields
  HironakaOriginalNCMarkedStratumCanonicalHistory HironakaOriginalNCMarkedStratumAdmissibleLevels
  HironakaOriginalNCMarkedStratumStepDrop HironakaOriginalOldBranchOpenHistory
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4OriginalSelectedLowerBadHistory
  HironakaG4SharpBadFootprint HironakaActualSharpBadMaximumProcessedSlice
  HironakaActualProtectedOtherRowLocalStep HironakaG4SmoothSubcarrierResidualStep
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstBlowupOpenComparison
  HironakaSharpActualRelativeSaturationOpenNaturality
open HironakaG4OriginalSelectedResidualTail HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpActualTraceIncidence HironakaSharpActualChronologicalResidualDictionary
  HironakaActualCleanupDensityCompactness BlowupFlatCoordinates RegularPatchPushforward
  BlowupRestrictOpen HironakaSharpNormalCrossingsOpenLocus
open InvertibleIdealQuotient IdealWeightPowers BlowupSNCTransform
open HomogenizedGlueingTower HironakaNormalCrossingsSNCBlockCarrier
  HironakaG4CompactWholeMonomialMaskPhase HironakaSharpActualMixedCentreWholeStrictTraceGeometry
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open NonmonomialTransformAlong RestrictEmptyTower
open ResolutionDriver
open ResolutionInvariantOrder ResolutionInvariantDriver ResolutionInvariantSeq
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The true selected sharp bad locus is compact through the SAME original
sharp footprint; inherited born components remain external. -/
theorem actual_compact_sharp_bad_source
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃D∈E,D))
    (hK : IsCompact (originalSharpBadLocus (n:=n) W E))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀a : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x≤1)
    (d : ℕ) (hReg : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n:=n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T=∅) (j : Fin E.length) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    let L:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Fj:=(E.map (strictAlong T)).eraseIdx j.val++A.E
    let Bj:=originalSharpBadLocus (n:=n) L Fj
    let M : MarkedIdeal n Y:=⟨L,[],vanishingIdeal (n:=n) Bj,1⟩
    IsClosedSubmanifold n L ∧ IsSNCDivisor n Fj ∧ IsCompact Bj ∧
      IsInvDomain n M ∧ IsBoundaryAdaptedCarrier (n:=n) (⋃D∈Fj,D) [] := by
  dsimp only
  let A:=geoTransformAlong (geometricTemplate W []) T
  let old:=E.map (strictAlong T)
  let L:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
  let Fj:=old.eraseIdx j.val++A.E
  let Bj:=originalSharpBadLocus (n:=n) L Fj
  obtain ⟨hL,_hLreg,_hDense,hM,hH⟩:=sharp_bad_native_domain
    hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hRec:=actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n Fj:=isSNCDivisor_of_sublist hRec.2.1
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl A.E))
  let jo : Fin old.length:=⟨j.val,by simp only [old,List.length_map];exact j.isLt⟩
  have hGet : old.get jo=strictAlong T (E.get j) := by simp [old,jo,List.get_eq_getElem]
  have hJ : oldResidualPart A.N old A.E jo=
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal := by
    change nonmonomialPartAlong n A.N (restrictOn n A.N (vanishingIdeal (n:=n) (old.get jo))) A.E=_
    rw [hGet]
    exact (hRec.2.2.2.2 j).2.2.1
  have hStatic:=originalSharpBadLocus_residual_subset hn hRec.1 hRec.2.1
    hRec.2.2.1 hRec.2.2.2.1 jo
  rw [hJ] at hStatic
  have hSub : Bj⊆originalSharpBadLocus (n:=n) A.N (old++A.E):=hStatic
  have hFoot:=(currentSharpCentres_original_footprint hW.1 hE.1 T hSharp).1
  have hCurrent : originalSharpBadLocus (n:=n) A.N (old++A.E)⊆
      T.proj ⁻¹' originalSharpBadLocus (n:=n) W E := by
    have hN : A.N=strictAlong T W:=N_geoTransformAlong _ _
    have hBoundary:=actual_whole_ambient_boundary_ordered_dictionary W E T
    rw [hN,←hBoundary]
    exact hFoot
  have hCompact : IsCompact Bj:=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
      (isClosed_originalSharpBadLocus hL.1 hFj.1) (hSub.trans hCurrent)
  exact ⟨hL,hFj,hCompact,hM,hH⟩


/-- The actual WHOLE computed maximum, all original branch tests, and the
omitted containing old member, for ONE internally constructed native blowup. -/
theorem exists_native_first_maximum_blowup
    (M : MarkedIdeal n Y) (hM : IsInvDomain n M) (hEmpty : M.E=[])
    (hK : IsCompact M.cosupp) (hNe : M.cosupp.Nonempty)
    (old born : List (Set Y)) (hFull : IsSNCDivisor n (old++born))
    (j : Fin old.length) (hOwn : M.N⊆old.get j) :
    let F:=old.eraseIdx j.val++born
    let H:=⋃D∈F,D
    let C:=maxLocus (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∃(Z : CMfd.{u} n)(pi : Z→Y)(hpi : IsBlowupAlong n C pi),
      let R : BlowupTower Y Z:=.step .refl C pi hpi
      C.Nonempty ∧ IsCompact C ∧ M.IsAdmissibleCentre C ∧
      HasNormalCrossings n C (old++born) ∧
      IsCanonical M (markedStratumHistoryValue M H) R ∧
      IsGeoTestTower M R ∧ IsOriginalBranchTestTower M H R ∧
      IsGeoTestTower (geometricTemplate M.N F) R := by
  dsimp only
  let F:=old.eraseIdx j.val++born
  let H:=⋃D∈F,D
  let C:=maxLocus (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
  have hF : IsSNCDivisor n F:=isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  have hH : IsBoundaryAdaptedCarrier (n:=n) H M.E := by
    rw [hEmpty]
    exact boundaryAdapted_union_of_snc_append F [] (by simpa only [List.append_nil] using hF)
  obtain ⟨x,hx,hMax⟩:=(markedStratum_history_value_isInvUSCOn M hM hH
    (BlowupTower.refl : BlowupTower Y Y) trivial).exists_isMaxOn hK hNe
  have hxC : x∈C:=⟨hx,hMax⟩
  have hAdm : M.IsAdmissibleCentre C := by
    have hLevel:=markedStratum_history_value_levels_admissible M hM hH
      (BlowupTower.refl : BlowupTower Y Y) trivial ⊤
      (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) x)
      (fun y hy _=>hxC.2 y hy)
    change (MarkedIdeal.pullback (Subtype.val : (⊤ : Opens Y)→Y) M).IsAdmissibleCentre
      ((Subtype.val : (⊤ : Opens Y)→Y) ⁻¹' {y | y∈M.cosupp ∧
        markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) y=
          markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) x}) at hLevel
    rw [←maxLocus_eq_level hxC] at hLevel
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) hLevel
  have hInterior:=interior_maxLocus_eq_empty hM (BlowupTower.refl : BlowupTower Y Y)
    trivial (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y))
  obtain ⟨Z,pi,hpi⟩:=exists_blowup C hAdm.1 hInterior
  let R : BlowupTower Y Z:=.step .refl C pi hpi
  have hCan : IsCanonical M (markedStratumHistoryValue M H) R:=⟨trivial,Or.inr rfl⟩
  obtain ⟨hTest,hHistory,_hBirth,_hFrame⟩:=markedStratum_canonical_history_joint_interpretation M hM hH R hCan
  let U : Opens Y:=⊤
  let B:=F.map ((Subtype.val : U→Y) ⁻¹' ·)
  have hEU : (MarkedIdeal.pullback (Subtype.val : U→Y) M).E=[] := by
    change M.E.map _=[]
    rw [hEmpty]
    rfl
  have hBU : IsSNCDivisor n (B++(MarkedIdeal.pullback (Subtype.val : U→Y) M).E) := by
    rw [hEU,List.append_nil]
    exact isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hF
  have hUnion : (Subtype.val : U→Y) ⁻¹' H=⋃D∈B,D := by
    ext y
    simp [H,B]
  have hTop:=hHistory U B hBU hUnion
  have hTop' : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U→Y)
      ({M with E:=F} : MarkedIdeal n Y)) (restrict U R) := by
    convert hTop using 1
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪:=MarkedIdeal.pullback (Subtype.val : U→Y) ({M with E:=F} : MarkedIdeal n Y))
      (𝔫:=({MarkedIdeal.pullback (Subtype.val : U→Y) M with
        E:=B++(MarkedIdeal.pullback (Subtype.val : U→Y) M).E} : MarkedIdeal n U)) rfl ?_ rfl rfl
    change B=B++(MarkedIdeal.pullback (Subtype.val : U→Y) M).E
    rw [hEU,List.append_nil]
  have hAug:=isGeoTestTower_of_restrict_cosupport_cover M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent F U
    (fun _ _=>mem_univ _) R hTest hTop'
  have hCNC : HasNormalCrossings n C F:=hAug.2.2.2
  have hAll : HasNormalCrossings n C (old++born) := by
    apply hasNormalCrossings_of_forall_notMem hFull hCNC
    intro D hD hNot
    rcases List.mem_append.mp hD with hOld|hBorn
    · obtain ⟨a,ha⟩:=List.mem_iff_get.mp hOld
      have haj : a.val=j.val := by
        by_contra hne
        exact hNot (List.mem_append_left born
          (List.mem_eraseIdx_iff_getElem.mpr ⟨a.val,a.isLt,hne,ha⟩))
      have he : a=j:=Fin.ext haj
      rw [he] at ha
      rw [←ha]
      exact (fun y hy=>hOwn ((hAdm.2.1 hy).1))
    · exact False.elim (hNot (List.mem_append_right _ hBorn))
  have hLow : IsGeoTestTower (geometricTemplate M.N F) R := by
    refine ⟨trivial,hAdm.1,?_,hCNC⟩
    change C⊆cosupport n M.N (IdealWeightPowers.unitIdeal n Y) 0
    rw [cosupport_zero (fun _ _ hg=>hg)]
    exact fun y hy=>(hAdm.2.1 hy).1
  exact ⟨Z,pi,hpi,⟨x,hxC⟩,hK.of_isClosed_subset hAdm.1.1 (fun _ hy=>hy.1),
    hAdm,hAll,hCan,hTest,hHistory,hLow⟩

private theorem normalized_vanishingIdeal_of_subset {R L : Set X} (hRL : R ⊆ L) :
    restrictOn n L (vanishingIdeal (n := n) R)=vanishingIdeal (n := n) R := by
  ext x g
  exact ⟨fun hg => MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt hRL hg.1 hg.2,
    fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩

private theorem transverse_trace_reduced (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hTr : IsTransverse n N [H]) :
    IsClosedSubmanifold n (N ∩ H) ∧
      restrictOn n N (vanishingIdeal (n := n) H)=vanishingIdeal (n := n) (N ∩ H) := by
  obtain ⟨hc,hnz,_hpr,hOne⟩ := actual_normalized_transverse_member_geometry hn hN hH hTr
  have hd : N ⊆ closure (N \ H) := actual_density_of_nonzero_normalized_vanishing hnz
  have hOrd : ∀ x ∈ N,ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) H)) x ≤ 1 := by
    intro x hxN
    by_cases hxH : x ∈ H
    · exact (hOne x ⟨hxN,hxH⟩).le
    · have hunit : (restrictOn n N (vanishingIdeal (n := n) H)).mem x 1 := by
        apply le_restrictOn (W := N) (VanishingIdealCoherent.isCoherent_vanishingIdeal
          (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)))
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [(hH.1 H (by simp)).isOpen_compl.mem_nhds hxH] with y hy hyH
        exact (hy hyH).elim
      by_contra hgt
      have hcos := (ordinaryTraceOrder_cosupport_iff hN hc hnz hxN 1).mpr (by omega)
      exact one_ne_zero ((vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp (hcos.2 1 hunit))
  have hd' : N ⊆ closure (N \ ⋃ K ∈ [H],K) := by simpa using hd
  obtain ⟨hS,hWhole,_hTail⟩ := actual_original_selected_residual_tail hn hN hH hd'
    (0 : Fin [H].length) (BlowupTower.refl (X := X)) trivial hOrd
  have hHsmooth := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsmooth
  have hSet : N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus=N ∩ H := by
    ext x
    constructor
    · rintro ⟨hxN,hxJ⟩
      refine ⟨hxN,?_⟩
      have hxH := (zeroLocus_restrictOn_iff hcH hxN).mp hxJ
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1] at hxH
    · rintro ⟨hxN,hxH⟩
      refine ⟨hxN,(zeroLocus_restrictOn_iff hcH hxN).mpr ?_⟩
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1]
  change IsClosedSubmanifold n (N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus) at hS
  change restrictOn n N (vanishingIdeal (n := n) H)=
    vanishingIdeal (n := n) (N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus) at hWhole
  rw [hSet] at hS hWhole
  exact ⟨hS,hWhole⟩

private theorem transverse_slice_remaining (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) : IsTransverse n (N ∩ H) F := by
  intro x hx
  obtain ⟨_kC,kN,Φ,s,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hE hTr hTr.hasNormalCrossings hx.1
  let z : Fin (H :: F).length := ⟨0,by simp⟩
  let c : Fin F.length → Fin (H :: F).length := fun a =>
    ⟨a.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using a.isLt⟩
  have hz : (H :: F).get z=H := rfl
  have hc (a : Fin F.length) : (H :: F).get (c a)=F.get a := by
    simp [c,List.get_eq_getElem]
  have hxH : x ∈ (H :: F).get z := by rw [hz];exact hx.2
  let Q : Finset (Fin n) := Finset.univ.filter fun t => kN ≤ t.val
  refine ⟨Q ∪ {s z},fun a => {s (c a)},?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) hxa y hy hyΦ
    · change y ∈ N ∩ H ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace (Q ∪ {s z})
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ y ∈ H) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s z})
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      rw [show coordSubspace Q=complexCoordinatePlane n kN by
        simp only [Q,coordSubspace_eq_complexCoordinatePlane]]
      exact and_congr (by simpa only [complexChartAt] using (hflat hy hyΦ).2.1)
        (by simpa only [hz,complexChartAt] using (hflat hy hyΦ).2.2 z hxH)
    · change y ∈ F.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace {s (c a)}
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have ha : x ∈ (H :: F).get (c a) := by rw [hc];exact hxa
      simpa only [hc,complexChartAt] using (hflat hy hyΦ).2.2 (c a) ha
  · intro a hxa
    have ha : x ∈ (H :: F).get (c a) := by rw [hc];exact hxa
    refine ⟨by simp,Finset.disjoint_singleton_left.mpr ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hQ | heq
    · have hge := (Finset.mem_filter.mp hQ).2
      exact Nat.not_lt_of_ge hge (hs (c a) ha)
    · have he : c a=z := hinj ha hxH (Finset.mem_singleton.mp heq)
      have hv := congrArg Fin.val he
      dsimp [c,z] at hv
      omega

private theorem transverse_slice_no_born_factor (hn : 0<n) {L H : Set X}
    {born : List (Set X)} (hL : IsClosedSubmanifold n L)
    (hE : IsSNCDivisor n (H :: born)) (hTr : IsTransverse n L (H :: born)) :
    IsClosedSubmanifold n (L ∩ H) ∧
      restrictOn n L (vanishingIdeal (n := n) H)=vanishingIdeal (n := n) (L ∩ H) ∧
      (∀ x ∈ L,IsNonzeroAlongAt L (vanishingIdeal (n := n) (L ∩ H)) x) ∧
      ∀ x ∈ L,∀ b : Fin born.length,x ∈ born.get b →
        ∃ f,(vanishingIdeal (n := n) (L ∩ H)).mem x f ∧
          ¬IsInSpanOnAt (n := n) L ((vanishingIdeal (n := n) (born.get b)).mem x) x f := by
  have hSingle : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hE (by simp)
  have hTrSingle : IsTransverse n L [H] := isTransverse_of_forall_mem hTr
    (fun K hK => by rw [List.mem_singleton.mp hK];simp)
  obtain ⟨hR,hTrace⟩ := transverse_trace_reduced hn hL hSingle hTrSingle
  have hNZ := (actual_normalized_transverse_member_geometry hn hL hSingle hTrSingle).2.1
  rw [hTrace] at hNZ
  refine ⟨hR,hTrace,hNZ,?_⟩
  intro x hx b hxb
  let v : Fin (H :: born).length := ⟨0,by simp⟩
  let w : Fin (H :: born).length := ⟨1+b.val,by simp only [List.length_cons];omega⟩
  have hv : (H :: born).get v=H := rfl
  have hw : (H :: born).get w=born.get b := by simp [w,List.get_eq_getElem,Nat.add_comm]
  by_cases hxH : x ∈ H
  · have hvw : v ≠ w := by intro he;have hh:=congrArg Fin.val he;dsimp [v,w] at hh;omega
    obtain ⟨f,hf,hH,hNot⟩ := exists_traceSpan_separator hn hE hTr hx v w
      (by rw [hv];exact hxH) (by rw [hw];exact hxb) hvw
    rw [hv] at hH
    rw [hw] at hNot
    refine ⟨f,?_,hNot⟩
    rw [←hTrace]
    exact ⟨hf,hH⟩
  · have hOne : (restrictOn n L (vanishingIdeal (n := n) H)).mem x (1 : X → ℂ) :=
      ⟨holomorphicAt_const 1,(traceSpan_unit_iff_notMem (hE.1 H (by simp)) hx).mpr hxH⟩
    rw [hTrace] at hOne
    refine ⟨1,hOne,fun h => ?_⟩
    exact ((traceSpan_unit_iff_notMem (hE.1 _ (List.mem_cons_of_mem H (List.get_mem born b))) hx).mp h) hxb

private theorem transverse_raw_canonical_parts (hn : 0<n) {N K : Set X}
    {born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hSNC : IsSNCDivisor n (K :: born)) (hTr : IsTransverse n N (K :: born)) :
    IsClosedSubmanifold n (N ∩ K) ∧
      monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) K)) born=unitIdeal n X ∧
      nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) K)) born=
        vanishingIdeal (n := n) (N ∩ K) := by
  obtain ⟨hZ,hTrace,_hnz,hNo⟩ := transverse_slice_no_born_factor hn hN hSNC hTr
  have hcZ := VanishingIdealCoherent.isCoherent_vanishingIdeal hZ
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hSNC (by simp)
  have hTBorn : IsTransverse n N born := isTransverse_of_forall_mem hTr
    (fun A hA => List.mem_cons_of_mem K hA)
  have hD := monomialPartAlong_eq_unit_of_no_member_factor hBorn hTBorn hcZ hNo
  have hJ := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hN hBorn hTBorn hcZ hNo
  rw [normalized_vanishingIdeal_of_subset (inter_subset_left : N ∩ K ⊆ N)] at hJ
  rw [hTrace]
  exact ⟨hZ,hD,hJ⟩

private theorem normalized_transverse_trace_order_le_one (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hTr : IsTransverse n N [H]) :
    ∀ x ∈ N,ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) H)) x ≤ 1 := by
  obtain ⟨hcA,hnzA,_hprA,hordA⟩ :=
    HironakaSharpActualFirstAmbientStrictExponent.actual_normalized_transverse_member_geometry
      hn hN hH hTr
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  intro x hxN
  by_cases hxH : x ∈ H
  · exact (hordA x ⟨hxN,hxH⟩).le
  · have hUnitH : (vanishingIdeal (n := n) H).mem x (1 : X → ℂ) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hHsm.1.isOpen_compl.mem_nhds hxH] with y hy hyH
      exact (hy hyH).elim
    have hUnit := le_restrictOn (W := N) hcH x (1 : X → ℂ) hUnitH
    by_contra hgt
    have hCos := (ordinaryTraceOrder_cosupport_iff hN hcA hnzA hxN 1).mpr (by omega)
    have hOne := (vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp (hCos.2 1 hUnit)
    exact one_ne_zero hOne


/-- A full NC centre preserves the reduced transverse slice. The genuine
mixed-old engine handles BOTH contained and transverse branches per stalk;
all source/future canonical parts are derived from actual full charts. -/
theorem nc_slice_same_centre_relative_strict
    (hn : 0<n) {N H C : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (H::F))
    (hTr : IsTransverse n N (H::F))
    (hCN : C⊆N) (hCNC : HasNormalCrossings n C (H::F))
    {pi : Y→X} (hpi : IsBlowupAlong n C pi) :
    let S:=N∩H
    let Nnext:=geoStrictTransform pi C N
    let Snext:=geoStrictTransform pi C S
    let Fnext:=F.map (geoStrictTransform pi C)++[pi ⁻¹' C]
    IsClosedSubmanifold n Snext ∧
      nextRelativeStrict N (vanishingIdeal (n:=n) S) C pi=vanishingIdeal (n:=n) Snext ∧
      HasNormalCrossings n Snext Fnext ∧
      Snext⊆closure (Snext \ ⋃D∈Fnext,D) ∧
      ∀z∈Nnext,ordinaryTraceOrder Nnext (vanishingIdeal (n:=n) Snext) z≤1 := by
  dsimp only
  let Nnext:=geoStrictTransform pi C N
  let Hnext:=geoStrictTransform pi C H
  let Snext:=geoStrictTransform pi C (N∩H)
  let Fnext:=F.map (geoStrictTransform pi C)++[pi ⁻¹' C]
  have hNnext : IsClosedSubmanifold n Nnext:=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hpi hN hCN
  have hEnext : IsSNCDivisor n (Hnext::Fnext) := by
    simpa only [List.map_cons,List.cons_append] using
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hpi hE hCNC
  have hTnext : IsTransverse n Nnext (Hnext::Fnext) := by
    simpa only [List.map_cons,List.cons_append] using
      isTransverse_geoTransformE_of_hasNormalCrossings hpi hN.1 hCN hE hTr hCNC
  have hSnext : Snext=Nnext∩Hnext := by
    change geoStrictTransform pi C (N∩H)=_
    calc
      _=geoStrictTransform pi C (H∩N):=congrArg _ (inter_comm N H)
      _=Hnext∩Nnext:=ExceptionalPushforwardAlong.geoStrictTransform_inter_eq
        hpi hN.1 hCN hE hTr hCNC (0 : Fin (H::F).length)
      _=Nnext∩Hnext:=inter_comm _ _
  have hParts:=transverse_raw_canonical_parts hn hN hE hTr
  have hPartsNext:=transverse_raw_canonical_parts hn hNnext hEnext hTnext
  have hDenseN : N⊆closure (N \ ⋃D∈H::F,D) := by
    simpa only [List.nil_append] using actual_cleanup_source_full_density
      (O:=[]) (B:=H::F) hn hN (by simpa using hE) hTr
      (by simpa using (subset_closure : N⊆closure N))
  have hMixed:=HironakaG4MixedOldResidualStep.actual_mixed_old_residual_step
    (old:=[H]) (born:=F) hn hN hE
    (isTransverse_of_forall_mem hTr (fun D hD=>List.mem_cons_of_mem H hD))
    hDenseN (0 : Fin [H].length) hpi hCN hCNC
  have hWhole : nextRelativeStrict N (vanishingIdeal (n:=n) (N∩H)) C pi=
      vanishingIdeal (n:=n) Snext := by
    have hh:=hMixed.2.2
    change nonmonomialPartAlong n Nnext
      (restrictOn n Nnext (vanishingIdeal (n:=n) Hnext)) Fnext=
        nextRelativeStrict N
          (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n:=n) H)) F) C pi at hh
    rw [hParts.2.2,hPartsNext.2.2,←hSnext] at hh
    exact hh.symm
  have hSmooth : IsClosedSubmanifold n Snext := by
    rw [hSnext]
    exact hPartsNext.1
  have hSliceT:=transverse_slice_remaining hn hEnext hTnext
  rw [←hSnext] at hSliceT
  have hFnext : IsSNCDivisor n Fnext:=isSNCDivisor_of_sublist hEnext (by simp)
  have hDense : Snext⊆closure (Snext \ ⋃D∈Fnext,D) := by
    simpa only [List.nil_append] using actual_cleanup_source_full_density
      (O:=[]) (B:=Fnext) hn hSmooth (by simpa using hFnext) hSliceT
      (by simpa using (subset_closure : Snext⊆closure Snext))
  have hOne:=normalized_transverse_trace_order_le_one hn hNnext
    (isSNCDivisor_of_sublist hEnext (by simp) : IsSNCDivisor n [Hnext])
    (isTransverse_of_forall_mem hTnext (by simp) : IsTransverse n Nnext [Hnext])
  have hTrace:=(transverse_trace_reduced hn hNnext
    (isSNCDivisor_of_sublist hEnext (by simp) : IsSNCDivisor n [Hnext])
    (isTransverse_of_forall_mem hTnext (by simp) : IsTransverse n Nnext [Hnext])).2
  rw [hTrace,←hSnext] at hOne
  exact ⟨hSmooth,hWhole,hSliceT.hasNormalCrossings,hDense,hOne⟩

private theorem pullback_comp_val_mem_iff (U : Opens X) {I : GermIdeal n X}
    (hI : I.IsCoherent) (x : U) (g : X→ℂ) :
    (GermIdeal.pullback (m:=n) (Subtype.val : U→X) I).mem x (g ∘ Subtype.val) ↔ I.mem x.val g := by
  rw [MarkedIdealRestrictOpen.mem_pullback_val_iff U hI]
  have he : extendOpens U (g ∘ (Subtype.val : U→X)) =ᶠ[𝓝 x.val] g := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact extendOpens_val U (g ∘ (Subtype.val : U→X)) ⟨y,hy⟩
  exact ⟨fun h=>HomogenizedIdeal.mem_congr hI h he,
    fun h=>HomogenizedIdeal.mem_congr hI h he.symm⟩

private theorem mem_iff_holomorphic_of_one {I : GermIdeal n X} (hI : I.IsCoherent)
    {x : X} (hOne : I.mem x 1) (g : X→ℂ) : I.mem x g ↔ HolomorphicAt n g x := by
  refine ⟨fun h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h,fun hg=>?_⟩
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  exact isInSpanAt_of_eq_mul hOne hg hg (Eventually.of_forall fun y=>by simp)

-- PRIVATE composition of already constructed actual local outputs. Its caller
-- derives every local field from source NC windows and the SAME actual pi.
private theorem global_from_actual_local
    (hn : 0<n) {S : Set X} {pi : Y→X} {Nnext Snext : Set Y}
    (hSnext : IsClosed Snext) (hProj : Snext⊆pi ⁻¹' S)
    (hNnext : IsClosedSubmanifold n Nnext) (I : GermIdeal n Y)
    (hI : I.IsCoherent) (hnzI : ∀y∈Nnext,IsNonzeroAlongAt Nnext I y)
    (F : List (Set Y))
    (hUnitOff : ∀y : Y,pi y∉S → I.mem y 1)
    (hLocal : ∀y : Y,pi y∈S → ∃V : Opens Y,y∈V ∧
      IsClosedSubmanifold n ((Subtype.val : V→Y) ⁻¹' Snext) ∧
      GermIdeal.pullback (m:=n) (Subtype.val : V→Y) I=
        vanishingIdeal (n:=n) ((Subtype.val : V→Y) ⁻¹' Snext) ∧
      HasNormalCrossings n ((Subtype.val : V→Y) ⁻¹' Snext)
        (F.map ((Subtype.val : V→Y) ⁻¹' ·)) ∧
      ((Subtype.val : V→Y) ⁻¹' Snext)⊆closure
        (((Subtype.val : V→Y) ⁻¹' Snext) \ ⋃D∈F.map ((Subtype.val : V→Y) ⁻¹' ·),D) ∧
      ∀z∈(Subtype.val : V→Y) ⁻¹' Nnext,
        ordinaryTraceOrder (X:=CMfd.of (n:=n) V) ((Subtype.val : V→Y) ⁻¹' Nnext)
          (GermIdeal.pullback (m:=n) (Subtype.val : V→Y) I) z≤1) :
    IsClosedSubmanifold n Snext ∧ I=vanishingIdeal (n:=n) Snext ∧
      HasNormalCrossings n Snext F ∧ Snext⊆closure (Snext \ ⋃D∈F,D) ∧
      ∀y∈Nnext,ordinaryTraceOrder Nnext I y≤1 := by
  have hSmooth : IsClosedSubmanifold n Snext := by
    refine ⟨hSnext,?_⟩
    intro y hy
    obtain ⟨V,hyV,hSm,_hIdeal,_hNC,_hDense,_hOrd⟩:=hLocal y (hProj hy)
    obtain ⟨k,hk⟩:=hSm.2 (⟨y,hyV⟩ : V) hy
    exact ⟨k,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk⟩
  have hcS:=(VanishingIdealCoherent.isCoherent_vanishingIdeal hSmooth)
  have hWhole : I=vanishingIdeal (n:=n) Snext := by
    ext y g
    by_cases hyS : pi y∈S
    · obtain ⟨V,hyV,_hSm,hIdeal,_hNC,_hDense,_hOrd⟩:=hLocal y hyS
      rw [←SmoothCentreHomogeneity.pullback_val_vanishingIdeal V Snext] at hIdeal
      have hh:=congrArg (fun K : GermIdeal n V=>K.mem ⟨y,hyV⟩ (g ∘ (Subtype.val : V→Y))) hIdeal
      rw [pullback_comp_val_mem_iff V hI,pullback_comp_val_mem_iff V hcS] at hh
      exact Iff.of_eq hh
    · have hyOff : y∉Snext:=fun h=>hyS (hProj h)
      have hOne : (vanishingIdeal (n:=n) Snext).mem y 1 := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [hSnext.isOpen_compl.mem_nhds hyOff] with z hz hzS
        exact (hz hzS).elim
      exact (mem_iff_holomorphic_of_one hI (hUnitOff y hyS) g).trans
        (mem_iff_holomorphic_of_one hcS hOne g).symm
  have hNC : HasNormalCrossings n Snext F := by
    intro y hy
    obtain ⟨V,hyV,_hSm,_hIdeal,hNC,_hDense,_hOrd⟩:=hLocal y (hProj hy)
    exact HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp
      (hNC (⟨y,hyV⟩ : V) hy)
  have hDense : Snext⊆closure (Snext \ ⋃D∈F,D) := by
    intro y hy
    obtain ⟨V,hyV,_hSm,_hIdeal,_hNC,hDense,_hOrd⟩:=hLocal y (hProj hy)
    have hUnion : (Subtype.val : V→Y) ⁻¹' (⋃D∈F,D)=
        ⋃D∈F.map ((Subtype.val : V→Y) ⁻¹' ·),D := by ext z;simp
    have hSet : ((Subtype.val : V→Y) ⁻¹' Snext) \ (⋃D∈F.map ((Subtype.val : V→Y) ⁻¹' ·),D)=
        (Subtype.val : V→Y) ⁻¹' (Snext \ ⋃D∈F,D) := by rw [←hUnion];rfl
    have hCl:=hDense (show (⟨y,hyV⟩ : V)∈(Subtype.val : V→Y) ⁻¹' Snext from hy)
    rw [hSet] at hCl
    exact closure_mono (image_preimage_subset (Subtype.val : V→Y) _)
      (image_closure_subset_closure_image continuous_subtype_val ⟨⟨y,hyV⟩,hCl,rfl⟩)
  have hOrd : ∀y∈Nnext,ordinaryTraceOrder Nnext I y≤1 := by
    intro y hyN
    by_cases hyS : pi y∈S
    · obtain ⟨V,hyV,_hSm,_hIdeal,_hNC,_hDense,hOne⟩:=hLocal y hyS
      have hOp:=HironakaSharpActualMixedCurveContactEvolution.actual_ordinary_trace_order_pullback_open
        hn hNnext hI hnzI V (⟨y,hyV⟩ : V)
      rw [←hOp]
      exact hOne _ hyN
    · by_contra hgt
      have hCos:=(ordinaryTraceOrder_cosupport_iff hNnext hI hnzI hyN 1).mpr (by omega)
      exact one_ne_zero ((vanishesToOrderOn_one_iff hyN (holomorphicAt_const 1)).mp
        (hCos.2 1 (hUnitOff y hyS)))
  exact ⟨hSmooth,hWhole,hNC,hDense,hOrd⟩

private theorem next_relative_one {N C : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {pi : Y→X} (hpi : IsBlowupAlong n C pi)
    (y : Y) (hOne : I.mem (pi y) 1) : (nextRelativeStrict N I C pi).mem y 1 := by
  have hcP:=GermIdealPullbackCalculus.isCoherent_pullback hpi.contMDiff hI
  have hP : (GermIdeal.pullback (m:=n) pi I).mem y 1 :=
    GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨(1 : X→ℂ),hOne,rfl⟩ (holomorphicAt_const 1))
  refine ⟨0,holomorphicAt_const 1,?_⟩
  intro a ha
  change HolomorphicAt n a y at ha
  have hProd : (GermIdeal.pullback (m:=n) pi I).mem y (a*1) :=
    (mem_iff_holomorphic_of_one hcP hP (a*1)).mpr (ha.mul (holomorphicAt_const 1))
  exact ⟨hProd.1,IsInSpanAt.restrict (isInSpanAt_self hProd hProd.1)⟩

-- Source windows only. Every future local field is constructed for the SAME
-- actual pi, using genuine restriction and the public NC-slice connector.
theorem same_step_of_source_windows
    (hn : 0<n) {N S C : Set X} (I : GermIdeal n X)
    (hN : IsClosedSubmanifold n N) (hS : IsClosedSubmanifold n S)
    (hI : I.IsCoherent) (hIS : I=vanishingIdeal (n:=n) S)
    (hnz : ∀x∈N,IsNonzeroAlongAt N I x)
    (hpr : ∀x∈N,∃ f : X→ℂ,HolomorphicAt n f x ∧
      ∀g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n:=n) N (·=f) x g)
    (F : List (Set X)) {pi : Y→X} (hpi : IsBlowupAlong n C pi) (hCN : C⊆N)
    (hWindows : ∀x∈S,∃(U : Opens X),x∈U ∧ ∃Haux : Set U,
      (Subtype.val : U→X) ⁻¹' S=(Subtype.val : U→X) ⁻¹' N∩Haux ∧
      IsSNCDivisor n (Haux::F.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U→X) ⁻¹' N) (Haux::F.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
      HasNormalCrossings n ((Subtype.val : U→X) ⁻¹' C) (Haux::F.map ((Subtype.val : U→X) ⁻¹' ·))) :
    let Nnext:=geoStrictTransform pi C N
    let Snext:=geoStrictTransform pi C S
    let Inext:=nextRelativeStrict N I C pi
    let Fnext:=F.map (geoStrictTransform pi C)++[pi ⁻¹' C]
    IsClosedSubmanifold n Snext ∧ Inext=vanishingIdeal (n:=n) Snext ∧
      HasNormalCrossings n Snext Fnext ∧ Snext⊆closure (Snext \ ⋃D∈Fnext,D) ∧
      ∀y∈Nnext,ordinaryTraceOrder Nnext Inext y≤1 := by
  dsimp only
  let Nnext:=geoStrictTransform pi C N
  let Snext:=geoStrictTransform pi C S
  let Inext:=nextRelativeStrict N I C pi
  let Fnext:=F.map (geoStrictTransform pi C)++[pi ⁻¹' C]
  have hNnext : IsClosedSubmanifold n Nnext:=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hpi hN hCN
  have hGeo:=nextRelativeStrict_actual_geometry hn hN hI hnz hpr hpi hCN
  have hcNext : Inext.IsCoherent:=hGeo.2.1
  have hnzNext : ∀y∈Nnext,IsNonzeroAlongAt Nnext Inext y:=hGeo.2.2.1
  apply global_from_actual_local hn (pi:=pi) (S:=S) (Nnext:=Nnext) (Snext:=Snext)
    isClosed_closure (geoStrictTransform_subset_preimage hpi.contMDiff.continuous hS.1)
    hNnext Inext hcNext hnzNext Fnext
  · intro y hy
    apply next_relative_one hI hpi y
    rw [hIS]
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [hS.1.isOpen_compl.mem_nhds hy] with z hz hzS
    exact (hz hzS).elim
  · intro y hy
    obtain ⟨U,hyU,Haux,hSlice,hEU,hTU,hCU⟩:=hWindows (pi y) hy
    let V:=firstBlowupSourceOpen hpi U
    let rho:=firstBlowupOpenProjection hpi U
    let NU:=(Subtype.val : U→X) ⁻¹' N
    let CU:=(Subtype.val : U→X) ⁻¹' C
    let FU:=F.map ((Subtype.val : U→X) ⁻¹' ·)
    have hrho : IsBlowupAlong n CU rho:=BlowupRestrictOpen.isBlowupAlong_restrict hpi U V.isOpen
    have hNU : IsClosedSubmanifold n NU:=BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
    have hCNU : CU⊆NU:=fun _ hx=>hCN hx
    obtain ⟨hSm,hWh,hNC,hDen,hOne⟩:=nc_slice_same_centre_relative_strict (X:=CMfd.of (n:=n) U)
      (Y:=CMfd.of (n:=n) V) (N:=NU) (H:=Haux) (C:=CU) (F:=FU)
      (pi:=rho) hn hNU hEU hTU hCNU hCU hrho
    have hEqN : geoStrictTransform rho CU NU=(Subtype.val : V→Y) ⁻¹' Nnext:=
      MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen N
    have hEqS : geoStrictTransform rho CU (NU∩Haux)=(Subtype.val : V→Y) ⁻¹' Snext := by
      rw [←hSlice]
      exact MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen S
    have hFmap : FU.map (geoStrictTransform rho CU)++[rho ⁻¹' CU]=
        Fnext.map ((Subtype.val : V→Y) ⁻¹' ·) := by
      simp only [FU,Fnext,List.map_append,List.map_singleton,List.map_map]
      congr 1
      · apply List.map_congr_left
        intro D _hD
        exact MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen D
    have hPullI : GermIdeal.pullback (m:=n) (Subtype.val : U→X) I=
        vanishingIdeal (n:=n) (NU∩Haux) := by
      rw [hIS,SmoothCentreHomogeneity.pullback_val_vanishingIdeal U S,hSlice]
    have hPullNext : GermIdeal.pullback (m:=n) (Subtype.val : V→Y) Inext=
        vanishingIdeal (n:=n) ((Subtype.val : V→Y) ⁻¹' Snext) := by
      change GermIdeal.pullback (m:=n) (Subtype.val : V→Y) (nextRelativeStrict N I C pi)=_
      rw [nextRelativeStrict_open hn hN hI hnz hpr hpi hCN U,hPullI,hWh,hEqS]
    rw [hEqS] at hSm
    rw [hEqS,hFmap] at hNC hDen
    refine ⟨V,hyU,hSm,hPullNext,hNC,hDen,?_⟩
    rw [hEqN,hEqS] at hOne
    rw [hPullNext]
    exact hOne


theorem actual_first_maximum_original_history
(hn : 0 < n) {W : Set X} {E : List (Set X)}
(hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
(hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
(hK : IsCompact (originalSharpBadLocus (n:=n) W E))
(T : BlowupTower X Y)
(hT : IsGeoTestTower (geometricTemplate W []) T)
(hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
(hSharp : CurrentSharpCentres W E T)
(hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
  ∀ a : Fin E.length,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
(d : Nat)
(hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
  RegularAtDim (n:=n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
(hDistinct : chronologicalDistinctDefect W E T = ∅)
(j : Fin E.length)
  : let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let L := A.N ∩ (J j).zeroLocus
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n:=n) L Fj
    let Mbad : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n:=n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y)) Mbad.cosupp
    Bj.Nonempty →
    ∃ (Z : CMfd.{u} n) (pi : Z → Y) (hpi : IsBlowupAlong n C pi),
      let R : BlowupTower Y Z := .step .refl C pi hpi
      let Tnext : BlowupTower X Z := .step T C pi hpi
      let Anext := geoTransformAlong (geometricTemplate W []) Tnext
      let oldnext := E.map (strictAlong Tnext)
      let Jnext := fun a : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) Tnext).ideal
      C.Nonempty ∧ IsCompact C ∧ IsClosedSubmanifold n C ∧
      C ⊆ Bj ∧ C ⊆ L ∧ C ⊆ A.N ∧
      HasNormalCrossings n C (old ++ A.E) ∧
      IsCanonical Mbad (markedStratumHistoryValue Mbad H) R ∧
      IsGeoTestTower Mbad R ∧ IsOriginalBranchTestTower Mbad H R ∧
      IsGeoTestTower (geometricTemplate L Fj) R ∧
      IsGeoTestTower (geometricTemplate W []) Tnext ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Tnext ∧
      CurrentSharpCentres W E Tnext ∧
      CentresOver (originalSharpBadLocus (n:=n) W E) Tnext ∧
      R.length = 1 ∧ Tnext.length = T.length+1 ∧
      Tnext.proj = T.proj ∘ pi ∧
      oldnext = old.map (geoStrictTransform pi C) ∧
      Anext.E = A.E.map (geoStrictTransform pi C) ++ [pi ⁻¹' C] ∧
      IsClosedSubmanifold n (strictAlong R L) ∧
      strictAlong R L ⊆ Anext.N ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) Tnext).N = Anext.N ∧
      Jnext j = vanishingIdeal (n:=n) (strictAlong R L) ∧
      (∀ a : Fin E.length,
        let I := restrictOn n Anext.N (vanishingIdeal (n:=n) (oldnext.get
          ⟨a.val, by simpa only [oldnext, List.length_map] using a.isLt⟩))
        nonmonomialPartAlong n Anext.N I Anext.E = Jnext a ∧
        I = restrictOn n Anext.N ((monomialPartAlong n Anext.N I Anext.E).mul (Jnext a))) ∧
      (∀ z ∈ (geoTransformAlong Mbad R).cosupp,
        (pi z ∈ C → markedStratumHistoryValue Mbad H R z <
          markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y) (pi z)) ∧
        (pi z ∉ C → markedStratumHistoryValue Mbad H R z =
          markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y) (pi z)))
 := by
  dsimp only
  let A:=geoTransformAlong (geometricTemplate W []) T
  let old:=E.map (strictAlong T)
  let J:=fun a : Fin E.length=>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let L:=A.N∩(J j).zeroLocus
  let Fj:=old.eraseIdx j.val++A.E
  let Bj:=originalSharpBadLocus (n:=n) L Fj
  let Mbad : MarkedIdeal n Y:=⟨L,[],vanishingIdeal (n:=n) Bj,1⟩
  let H:=⋃D∈Fj,D
  let C:=maxLocus (markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y)) Mbad.cosupp
  intro hNe
  obtain ⟨hL,hFj,hKB,hM,hAdapt⟩:=actual_compact_sharp_bad_source
    hn hW hE hdense hK T hT hFull hSharp hOrd d hReg hDistinct j
  have hRec:=actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hCos : Mbad.cosupp=Bj:=SmoothCentreLocus.cosupp_vanishingIdeal
    (isClosed_originalSharpBadLocus hL.1 hFj.1) (fun _ hx=>hx.1)
  have hNi : (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N:=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  have hOrdj : ∀y∈(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (J j) y≤1 := by
    simpa only [hNi] using (fun y hy=>hOrd y hy j)
  obtain ⟨_hLj,_hWholej,hTail⟩:=actual_original_selected_lower_boundary_history
    hn hW hE hdense j T hT hFull hOrdj
  let jo : Fin old.length:=⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩
  have hGet : old.get jo=strictAlong T (E.get j):=by simp [old,jo]
  have hOwn : Mbad.N⊆old.get jo := by
    rw [hGet]
    have hOldSm : IsClosedSubmanifold n (strictAlong T (E.get j)) := by
      have hMem : strictAlong T (E.get j)∈old++A.E:=
        List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E j))
      obtain ⟨a,ha⟩:=List.mem_iff_get.mp hMem
      exact ha ▸ MonomialPart.isClosedSubmanifold_get hn hRec.2.1 a
    have hcH:=VanishingIdealCoherent.isCoherent_vanishingIdeal hOldSm
    obtain ⟨hcI,_hnz,hNm,_hFact⟩:=hRec.2.2.2.2 j
    have hLe : (restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong T (E.get j)))).Le (J j) := by
      change (restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong T (E.get j)))).Le
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
      rw [←hNm]
      exact le_nonmonomialPartAlong_self hcI
    intro x hx
    have hZero := (zeroLocus_restrictOn_iff hcH hx.1).mp (fun g hg=>hx.2 g (hLe x g hg))
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hOldSm.1] at hZero
  have hKCos : IsCompact Mbad.cosupp:=hCos.symm ▸ hKB
  have hNeCos : Mbad.cosupp.Nonempty:=hCos.symm ▸ hNe
  obtain ⟨Q,pi,hpi,hCNe,hKC,hAdm,hCNC,hCan,hTest,hHistory,hLow⟩:=
    exists_native_first_maximum_blowup Mbad hM rfl hKCos hNeCos old A.E hRec.2.1 jo hOwn
  let R : BlowupTower Y Q:=.step .refl C pi hpi
  let Tnext : BlowupTower X Q:=.step T C pi hpi
  have hLow' : IsGeoTestTower (geometricTemplate
      ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N∩(J j).zeroLocus) Fj) R := by
    simpa only [hNi] using hLow
  obtain ⟨hTnext,hFullnext,_hNStrict,hLStrict,hLSub,hChronN,hJStrict⟩:=hTail R hLow'
  have hTN : T.append R=Tnext:=rfl
  rw [hTN] at hTnext hFullnext hChronN hJStrict
  rw [hNi] at hLStrict hLSub hJStrict
  have hNextN : (geoTransformAlong (geometricTemplate W []) Tnext).N=strictAlong R A.N:=by
    change (geoTransformAlong (geometricTemplate W []) (T.append R)).N=_
    rw [geoTransformAlong_append]
    exact N_geoTransformAlong _ _
  have hLStrict' : IsClosedSubmanifold n (strictAlong R L):=hLStrict
  have hLSub' : strictAlong R L⊆(geoTransformAlong (geometricTemplate W []) Tnext).N:=by
    rw [hNextN]
    exact hLSub
  have hChronN' : (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) Tnext).N=
      (geoTransformAlong (geometricTemplate W []) Tnext).N:=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) Tnext).1
  have hCB : C⊆Bj:=fun _ hx=>hCos ▸ hx.1
  have hCL : C⊆L:=fun _ hx=>(hAdm.2.1 hx).1
  have hCN : C⊆A.N:=hCL.trans inter_subset_left
  have hBad : Bj⊆originalSharpBadLocus (n:=n) A.N (old++A.E) := by
    have hh:=actual_original_selected_lower_current_bad_subset hn hW hE hdense j T hT hFull
      hOrdj (BlowupTower.refl : BlowupTower Y Y) trivial
    simp only [hNi,geoTransformAlong_refl,BlowupTower.append_refl] at hh
    rw [actual_whole_ambient_boundary_ordered_dictionary W E T] at hh
    exact hh
  have hSharpnext : CurrentSharpCentres W E Tnext := by
    refine ⟨hSharp,?_⟩
    have hBnd:=actual_whole_ambient_boundary_ordered_dictionary W E T
    rw [hBnd]
    change C⊆originalSharpBadLocus (n:=n) (strictAlong T (geometricTemplate W []).N) (old++A.E)
    rw [←N_geoTransformAlong]
    exact hCB.trans hBad
  have hOver : CentresOver (originalSharpBadLocus (n:=n) W E) Tnext:=
    (currentSharpCentres_original_footprint hW.1 hE.1 Tnext hSharpnext).2
  have hNewRec:=actual_recorded_tower_residual_dictionary hn hW hE hdense Tnext hTnext hFullnext
  refine ⟨Q,pi,hpi,hCNe,hKC,hAdm.1,hCB,hCL,hCN,hCNC,hCan,hTest,hHistory,
    hLow,hTnext,hFullnext,hSharpnext,hOver,rfl,rfl,rfl,?_,rfl,
    hLStrict',hLSub',hChronN',hJStrict,?_,?_⟩
  · simp only [List.map_map]
    rfl
  · intro a
    have hGetNext : (E.map (strictAlong Tnext)).get
        ⟨a.val,by simpa only [List.length_map] using a.isLt⟩=strictAlong Tnext (E.get a) := by simp
    rw [hGetNext]
    exact (hNewRec.2.2.2.2 a).2.2
  · intro z hz
    exact markedStratum_history_value_decrease Mbad hM hAdapt
      (BlowupTower.refl : BlowupTower Y Y) C pi hpi trivial hCNe rfl z hz


theorem processed_original_row_same_maximum_step
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (i j : Fin E.length) (hne : j ≠ i)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    let L := A.N ∩ (J j).zeroLocus
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H
        (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∀ {Q : CMfd.{u} n} (pi : Q→Y) (hpi : IsBlowupAlong n C pi),
      let Tnext : BlowupTower X Q:=.step T C pi hpi
      let Anext:=geoTransformAlong (geometricTemplate W []) Tnext
      let JiNext:=(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) Tnext).ideal
      let SiNext:=geoStrictTransform pi C Si
      let FiNext:=(E.map (strictAlong Tnext)).eraseIdx i.val++Anext.E
      IsClosedSubmanifold n SiNext ∧ JiNext=vanishingIdeal (n:=n) SiNext ∧
        Anext.N∩JiNext.zeroLocus=SiNext ∧ HasNormalCrossings n SiNext FiNext ∧
        SiNext⊆closure (SiNext \ ⋃D∈FiNext,D) ∧
        ∀z∈Anext.N,ordinaryTraceOrder Anext.N JiNext z≤1 := by
  dsimp only
  let A:=geoTransformAlong (geometricTemplate W []) T
  let old:=E.map (strictAlong T)
  let J:=fun a : Fin E.length=>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let Si:=A.N∩(J i).zeroLocus
  let L:=A.N∩(J j).zeroLocus
  let Fi:=old.eraseIdx i.val++A.E
  let Fj:=old.eraseIdx j.val++A.E
  let Bj:=originalSharpBadLocus (n:=n) L Fj
  let M : MarkedIdeal n Y:=⟨L,[],vanishingIdeal (n:=n) Bj,1⟩
  let H:=⋃D∈Fj,D
  let C:=maxLocus (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
  intro Q pi hpi
  let Tnext : BlowupTower X Q:=.step T C pi hpi
  let Anext:=geoTransformAlong (geometricTemplate W []) Tnext
  have hRec:=actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hProtect:=HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection
    hn hW hE hdense i T hT hFull (fun y hy=>hOrd y hy i) hNCi hDensei
  have hSi : IsClosedSubmanifold n Si:=hProtect.1
  have hIS : J i=vanishingIdeal (n:=n) Si:=hProtect.2.1
  have hGi:=original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  have hNi : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N:=hGi.1
  have hcI : (J i).IsCoherent:=hGi.2.2.2.1.isCoherent
  have hnz : ∀x∈A.N,IsNonzeroAlongAt A.N (J i) x:=by
    simpa only [hNi] using hGi.2.2.2.2.1
  have hpr : ∀x∈A.N,∃f : Y→ℂ,HolomorphicAt n f x ∧
      ∀g,(J i).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n:=n) A.N (·=f) x g:=by
    simpa only [hNi] using hGi.2.2.2.2.2
  obtain ⟨hL,_hRegL,_hDenseL,_hM,_hAdapt⟩:=sharp_bad_native_domain
    hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hFj : IsSNCDivisor n Fj:=isSNCDivisor_of_sublist hRec.2.1
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl A.E))
  have hCos : M.cosupp=Bj:=SmoothCentreLocus.cosupp_vanishingIdeal
    (isClosed_originalSharpBadLocus hL.1 hFj.1) (fun _ hx=>hx.1)
  have hCN : C⊆A.N:=fun x hx=>(show x∈Bj from hCos ▸ hx.1).1.1
  have hWindows : ∀x∈Si,∃(U : Opens Y),x∈U ∧ ∃Haux : Set U,
      (Subtype.val : U→Y) ⁻¹' Si=(Subtype.val : U→Y) ⁻¹' A.N∩Haux ∧
      IsSNCDivisor n (Haux::Fi.map ((Subtype.val : U→Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U→Y) ⁻¹' A.N) (Haux::Fi.map ((Subtype.val : U→Y) ⁻¹' ·)) ∧
      HasNormalCrossings n ((Subtype.val : U→Y) ⁻¹' C) (Haux::Fi.map ((Subtype.val : U→Y) ⁻¹' ·)) := by
    intro x hx
    by_cases hxC : x∈C
    · exact actual_sharp_bad_maximum_processed_slice_locality hn hW hE hdense T hT hFull
        hOrd d hReg hDistinct i j hne hNCi hDensei x ⟨hxC,hx⟩
    · have hOrdI : ∀y∈(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
          ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N (J i) y≤1 := by
        simpa only [hNi] using (fun y hy=>hOrd y hy i)
      have hx' : x∈(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N∩(J i).zeroLocus:=by
        simpa only [hNi] using hx
      obtain ⟨U,hxU,hU,Haux,hEU,hTU,hSlice,_hI,_hOther⟩:=protected_slice_window
        hn hW hE hdense i T hT hFull hOrdI hNCi hDensei hx'
        ⟨Cᶜ,hpi.1.1.isOpen_compl⟩ hxC
      refine ⟨U,hxU,Haux,hSlice,hEU,hTU,?_⟩
      have hEmpty : (Subtype.val : U→Y) ⁻¹' C=∅:=by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hU z.property hz
      rw [hEmpty]
      intro z hz
      exact hz.elim
  obtain ⟨hSm,hWhole,hNC,hDen,hOne⟩:=same_step_of_source_windows
    (X:=Y) (Y:=Q) hn (J i) hRec.1 hSi hcI hIS hnz hpr Fi hpi hCN hWindows
  have hIdealNext : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) Tnext).ideal=
      nextRelativeStrict A.N (J i) C pi := by
    change nextRelativeStrict (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
      (J i) C pi=_
    rw [hNi]
  have hNnext : Anext.N=geoStrictTransform pi C A.N:=rfl
  have hFnext : (E.map (strictAlong Tnext)).eraseIdx i.val++Anext.E=
      Fi.map (geoStrictTransform pi C)++[pi ⁻¹' C] := by
    simp only [Fi,old,List.map_append,List.eraseIdx_map,List.map_map,List.append_assoc]
    rfl
  have hSub : geoStrictTransform pi C Si⊆Anext.N := by
    rw [hNnext]
    exact geoStrictTransform_mono pi C (inter_subset_left : Si⊆A.N)
  refine ⟨hSm,hIdealNext.trans hWhole,?_,?_,?_,?_⟩
  · rw [hIdealNext,hWhole,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hSm.1]
    exact inter_eq_right.mpr hSub
  · rw [hFnext]
    exact hNC
  · rw [hFnext]
    exact hDen
  · rw [hNnext,hIdealNext]
    exact hOne


theorem exists_actual_first_sharp_bad_maximum_blowup
(hn : 0 < n) {W : Set X} {E : List (Set X)}
(hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
(hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
(hK : IsCompact (originalSharpBadLocus (n:=n) W E))
(T : BlowupTower X Y)
(hT : IsGeoTestTower (geometricTemplate W []) T)
(hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
(hSharp : CurrentSharpCentres W E T)
(hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
  ∀ a : Fin E.length,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
(d : Nat)
(hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
  RegularAtDim (n:=n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
(hDistinct : chronologicalDistinctDefect W E T = ∅)
(P : Finset (Fin E.length)) (j : Fin E.length) (hj : j ∉ P)
(hProcessedNC : ∀ i ∈ P,
  let A := geoTransformAlong (geometricTemplate W []) T
  let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
  HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
(hProcessedDense : ∀ i ∈ P,
  let A := geoTransformAlong (geometricTemplate W []) T
  let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
  Si ⊆ closure (Si \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H))
  : let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let L := A.N ∩ (J j).zeroLocus
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n:=n) L Fj
    let Mbad : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n:=n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y)) Mbad.cosupp
    Bj.Nonempty →
    ∃ (Z : CMfd.{u} n) (pi : Z → Y) (hpi : IsBlowupAlong n C pi),
      let R : BlowupTower Y Z := .step .refl C pi hpi
      let Tnext : BlowupTower X Z := .step T C pi hpi
      let Anext := geoTransformAlong (geometricTemplate W []) Tnext
      let oldnext := E.map (strictAlong Tnext)
      let Jnext := fun a : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) Tnext).ideal
      C.Nonempty ∧ IsCompact C ∧ IsClosedSubmanifold n C ∧
      C ⊆ Bj ∧ C ⊆ L ∧ C ⊆ A.N ∧
      HasNormalCrossings n C (old ++ A.E) ∧
      IsCanonical Mbad (markedStratumHistoryValue Mbad H) R ∧
      IsGeoTestTower Mbad R ∧ IsOriginalBranchTestTower Mbad H R ∧
      IsGeoTestTower (geometricTemplate L Fj) R ∧
      IsGeoTestTower (geometricTemplate W []) Tnext ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Tnext ∧
      CurrentSharpCentres W E Tnext ∧
      CentresOver (originalSharpBadLocus (n:=n) W E) Tnext ∧
      R.length = 1 ∧ Tnext.length = T.length+1 ∧
      Tnext.proj = T.proj ∘ pi ∧
      oldnext = old.map (geoStrictTransform pi C) ∧
      Anext.E = A.E.map (geoStrictTransform pi C) ++ [pi ⁻¹' C] ∧
      IsClosedSubmanifold n (strictAlong R L) ∧
      strictAlong R L ⊆ Anext.N ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) Tnext).N = Anext.N ∧
      Jnext j = vanishingIdeal (n:=n) (strictAlong R L) ∧
      (∀ i ∈ P,
        let Si := A.N ∩ (J i).zeroLocus
        let SiNext := geoStrictTransform pi C Si
        let FiNext := oldnext.eraseIdx i.val ++ Anext.E
        IsClosedSubmanifold n SiNext ∧
        Jnext i = vanishingIdeal (n:=n) SiNext ∧
        Anext.N ∩ (Jnext i).zeroLocus = SiNext ∧
        HasNormalCrossings n SiNext FiNext ∧
        SiNext ⊆ closure (SiNext \ ⋃ D ∈ FiNext, D) ∧
        ∀ z ∈ Anext.N, ordinaryTraceOrder Anext.N (Jnext i) z ≤ 1) ∧
      (∀ a : Fin E.length,
        let I := restrictOn n Anext.N (vanishingIdeal (n:=n) (oldnext.get
          ⟨a.val, by simpa only [oldnext, List.length_map] using a.isLt⟩))
        nonmonomialPartAlong n Anext.N I Anext.E = Jnext a ∧
        I = restrictOn n Anext.N ((monomialPartAlong n Anext.N I Anext.E).mul (Jnext a))) ∧
      (∀ z ∈ (geoTransformAlong Mbad R).cosupp,
        (pi z ∈ C → markedStratumHistoryValue Mbad H R z <
          markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y) (pi z)) ∧
        (pi z ∉ C → markedStratumHistoryValue Mbad H R z =
          markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y) (pi z)))
 := by
  dsimp only
  intro hNe
  obtain ⟨Q,pi,hpi,hCNe,hKC,hCSm,hCB,hCL,hCN,hCNC,hCan,hTest,hHistory,
    hLow,hTnext,hFullnext,hSharpnext,hOver,hRLength,hTLength,hProj,hOld,hBorn,
    hLStrict,hLSub,hChronN,hJStrict,hRows,hDrop⟩:=
    actual_first_maximum_original_history hn hW hE hdense hK T hT hFull hSharp
      hOrd d hReg hDistinct j hNe
  refine ⟨Q,pi,hpi,hCNe,hKC,hCSm,hCB,hCL,hCN,hCNC,hCan,hTest,hHistory,
    hLow,hTnext,hFullnext,hSharpnext,hOver,hRLength,hTLength,hProj,hOld,hBorn,
    hLStrict,hLSub,hChronN,hJStrict,?_,hRows,hDrop⟩
  intro i hi
  exact processed_original_row_same_maximum_step hn hW hE hdense T hT hFull
    hOrd d hReg hDistinct i j (fun he=>hj (he.symm ▸ hi))
    (hProcessedNC i hi) (hProcessedDense i hi) pi hpi

end
end Hironaka.HironakaActualSharpBadFirstMaximumBlowup
