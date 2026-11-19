import Hironaka.Resolution.HironakaG1PositiveNormalAlignedTail
import Hironaka.Resolution.HironakaG1PositiveNormalSharedTail

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalOwnTailTest
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism BlowupTowerIsomorphism ResolutionInvariantSpec StepOneValue
  StepOneValueMasked StepOneRegime CanonicalCentres NormalCrossings BoundaryCount
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionPositiveLowerRecords
  HironakaActualNativeSectionOriginalCuts HironakaActualNativeInvariantDomain
  HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative HironakaG1PositiveNormalPhase
  HironakaG1PositiveNormalAlignedTail HironakaG1PositiveNormalSharedTail
  HironakaG1RecursiveMemberValueTransport HironakaActualOpenZeroSectionDifferentials
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaG8HomStable HironakaG8LocalHistory InvDomainMemberRestriction
  InvDomainTowerAlong RelativePrincipalizationSpan StepOneLowerDomain InvDomainRebase MarkedIdealRestrictOpen
  NormalCrossingsComparison NormalCrossingsInvariance
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem own_window_test {n q : ℕ} {X Y : CMfd.{0} (n + 1)}
    {A : Set X} {hAc : IsClosed A} {hA : ∀ x ∈ A, RegularAtDim (n := n + 1) A x n}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀ x ∈ V, RegularAtDim (n := n + 1) V x n}
    {E : List (Set X)} {S : BlowupTower X Y}
    {N : BlowupTower (nativeManifold (Nat.le_succ n) A hA)
      (nativeManifold (Nat.le_succ n) V hV)}
    (hTail : Lift (Nat.le_succ n) A hAc hA E S V hVc hV N)
    (O : Opens X) (ON : Opens (nativeManifold (Nat.le_succ n) A hA))
    (hON : nativeWindow (Nat.le_succ n) A hA O = ON)
    (M : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) O))
    (L : MarkedIdeal n (CMfd.of (n := n) ON))
    (hM : M.ideal.IsCoherent) (f : ON → O) (hf : ∀ x, (f x).val = x.val.val)
    (hRec : markedPullback (m := n) f M = L)
    {hZ : ∀ x ∈ openSection V (openPreimage S O),
      RegularAtDim (n := n + 1) (openSection V (openPreimage S O)) x n}
    (K : BlowupTower (nativeManifold (Nat.le_succ n) (openSection A O) (openSection_regular hA O))
      (nativeManifold (Nat.le_succ n) (openSection V (openPreimage S O)) hZ))
    (hIso : IsTowerIso (windowEquiv (Nat.le_succ n) A hA hAc O) K
      (restrict (nativeWindow (Nat.le_succ n) A hA O) N) (endpointEquiv hTail O))
    (hDomain : IsInvDomain q
      (nativePullback (Nat.le_succ n) (openSection A O) (openSection_regular hA O) M))
    (hTest : IsGeoTestTower
      (nativePullback (Nat.le_succ n) (openSection A O) (openSection_regular hA O) M) K)
    (b : nativeManifold (Nat.le_succ n) (openSection V (openPreimage S O)) hZ)
    (hb : b ∈ (geoTransformAlong
      (nativePullback (Nat.le_succ n) (openSection A O) (openSection_regular hA O) M) K).cosupp) :
    IsInvDomain q L ∧ IsGeoTestTower L (restrict ON N) ∧
      ∃ w : openPreimage N ON, w.val.val = b.val.val ∧
        w ∈ (geoTransformAlong L (restrict ON N)).cosupp := by
  subst ON
  let hk := Nat.le_succ n
  let W := openSection A O
  let hW := openSection_regular hA O
  let ψ := windowEquiv hk A hA hAc O
  let χ := endpointEquiv hTail O
  let J := nativePullback hk W hW M
  have hf' : f = sourceInclusion hk A hA O := by
    funext x
    exact Subtype.ext (hf x)
  have hfh := (source_geometry hk A hA hAc O).1
  rw [← hf'] at hfh
  have hLc : L.ideal.IsCoherent := by
    rw [← hRec]
    exact GermIdealPullbackCalculus.isCoherent_pullback hfh hM
  have hMap : f ∘ ψ = (Subtype.val : nativeManifold hk W hW → O) := by
    funext x
    apply Subtype.ext
    exact hf (ψ x)
  have hBack : MarkedIdeal.pullback ψ L = J := by
    rw [← hRec]
    change markedPullback (m := n) ψ (markedPullback (m := n) f M) =
      J
    rw [← whole_markedPullback_comp hfh ψ.contMDiff M hM, hMap]
    rfl
  have hForth : MarkedIdeal.pullback ψ.symm J = L := by
    rw [← hBack]
    change markedPullback (m := n) ψ.symm (markedPullback (m := n) ψ L) = L
    rw [← whole_markedPullback_comp ψ.contMDiff ψ.symm.contMDiff L hLc]
    have hid : (⇑ψ : _ → _) ∘ ⇑ψ.symm = id := funext ψ.apply_symm_apply
    rw [hid]
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · simp [markedPullback]
    · exact BlowupControlledTransform.pullback_id hLc
    · rfl
  have hLD := hForth ▸ isInvDomain_pullback ψ.symm hDomain
  have hi := IsTowerIso.isGeoTestTower_iff ψ hLD.isWellFormed.isClosedSubmanifold_N hLc hIso
  rw [hBack] at hi
  have hLT := hi.mp hTest
  have hc := IsTowerIso.cosupp_geoTransformAlong ψ hLD.isWellFormed.isClosedSubmanifold_N hLc hIso hLT
  rw [hBack] at hc
  refine ⟨hLD, hLT, χ b, endpointEquiv_val_native hTail O b, ?_⟩
  change b ∈ (⇑χ) ⁻¹' (geoTransformAlong L (restrict (nativeWindow hk A hA O) N)).cosupp
  rw [← hc]
  exact hb

private theorem zeroPlane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual lifted upper history, the literal native positive lower
record has its tight domain, and its own restricted tail is a test ending
in the lower cosupport over the original endpoint. -/
theorem positive_normal_own_native_tail_test {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) Sec
    let r := regimeRun (stepRegime P (s + 1)) T y
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV))
      (z : nativeManifold (Nat.le_succ n) V hV),
      Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U) Sec.E T V hVc hV N ∧
      z.val = y ∧ regimeRun (stepRegime B (s + 1)) N z = r ∧ ¬ IsSpecial B N z ∧
      ∃ (A : Set (split T r).1) (hA : ∀ x ∈ A, RegularAtDim (n := n + 1) A x n)
        (e : (split N r).1 = nativeManifold (Nat.le_succ n) A hA),
        let NH := recastTarget e (head N r)
        let NS := recastSource e (tail N r)
        let a := NS.proj z
        let O := maskA B NH a
        let L := lowerMarkedM B (s + 1) NH a
        IsInvDomain (k - 1) L ∧ IsGeoTestTower L (restrict O NS) ∧
        ∃ w : openPreimage NS O, w.val = z ∧ w ∈ (geoTransformAlong L (restrict O NS)).cosupp := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let R := invFamily (Nat.succ_pos n) k
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA Sec H p
  let M := positiveMemberOn Sec H p O
  let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) Sec
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R
    (Nat.succ_pos n)).isGeoTestTower_of_isCanonical hP hMax T hCan
  have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  have hNS : ¬ IsSpecial P T y := fun h =>
    hSecNS (positive_normal_special_of_padded Q hQ T hTest y (hLevel ▸ Nat.succ_pos s) h)
  have hShared := positive_normal_section_head_nonspecial_of_endpoint Q hQ T hTest y hy hLevel hSecNS
  have hSharedData := original_normal_positive_shared_tail Q hQ T hCan y hy hLevel hNS hShared
  obtain ⟨hD, hCanL, hClass, W, hWc, hW, Z, hZc, hZ, K', hW_eq, hNativeD, hSmall, _, hRec,
    b', hb'y, hb'⟩ := hSharedData
  have hMTest : IsGeoTestTower M (restrict O S) :=
    (hClass.wEquiv.2 _).1.mp (R.isInvValue.isGeoTestTower_of_isCanonical hD _ hCanL)
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSecBar := (properNormalMarked_locWPEquiv_section Q hQ).trans (bar_local_any_boundary (X := X) Sec hSec)
  let MT := geoTransformAlong (barMarked Sec) H
  have hMT : MT.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked Sec hSec.isWellFormed) H ((hSecBar.wEquiv.2 H).1.mp hHeadTest)
  have hWF : M.IsWellFormed :=
    IsWellFormed.pullback_val (isWellFormed_memberRestrict (Nat.succ_pos n) hMT _) O
  have hHol : ∀ x f, M.ideal.mem x f → HolomorphicAt (n + 1) f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hWF.isCoherent hf
  have hSupport : M.N ⊆ openSection (strictAlong H (zeroPlane U)) O := by
    intro x hx
    have hx' : (x : (split T r).1) ∈ (geoTransformAlong (barMarked Sec) H).N := hx.1
    rw [N_geoTransformAlong] at hx'
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hx'
  have hY : ∃ b : openPreimage S O, b.val = y ∧ b ∈ (geoTransformAlong M (restrict O S)).cosupp := by
    refine ⟨b'.val, hb'y, ?_⟩
    rw [hRec, cosupp_nativePullback (Nat.le_succ n) Z hZ _
      (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hSmall M (hW_eq.symm ▸ hSupport))
      (HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong M hHol (restrict O S))] at hb'
    exact hb'
  obtain ⟨V, hVc, hV, N, z, hLift, hz, hClock, hNativeNS, A, hAc, hA, e, hHead, hTail,
    ha, hWindow, ⟨hZc', hZ', K, hGeo, hIso⟩, f, _, _, _, _, hf, _, hInit, _⟩ :=
    positive_normal_native_tail_records_of_nonspecial Q hQ T hTest y hy hLevel hSecNS
  refine ⟨V, hVc, hV, N, z, hLift, hz, hClock, hNativeNS, A, hA, e, ?_⟩
  let NH := recastTarget e (head N r)
  let NS := recastSource e (tail N r)
  let a := NS.proj z
  let Oa := maskA Sec H a.val
  let ON := maskA B NH a
  let LN := lowerMarkedM B (s + 1) NH a
  let L := lowerMarkedM Sec (s + 1) H a.val
  have hTransfer (x : (split T r).1) (hx : x = p) :
      let O' := maskA Sec H x
      let M' := positiveMemberOn Sec H x O'
      M'.IsWellFormed ∧ M'.N ⊆ openSection A O' ∧ IsGeoTestTower M' (restrict O' S) ∧
      IsInvDomain (k - 1) (nativePullback (Nat.le_succ n) (openSection A O') (openSection_regular hA O') M') ∧
      ∃ b : openPreimage S O', b.val = y ∧ b ∈ (geoTransformAlong M' (restrict O' S)).cosupp := by
    subst x
    have hAeq : openSection A O = W :=
      (congrArg (fun A => openSection A O) hHead.carrier).trans hW_eq.symm
    refine ⟨hWF, hAeq.symm ▸ (hW_eq.symm ▸ hSupport), hMTest, ?_, hY⟩
    exact (congrArg (fun (W' : Set (CMfd.of (n := n + 1) O)) =>
      ∀ h : (∀ w ∈ W', RegularAtDim (n := n + 1) W' w n),
        IsInvDomain (k - 1) (nativePullback (Nat.le_succ n) W' h M)) hAeq).mpr
      (fun _ => hNativeD) (openSection_regular hA O)
  obtain ⟨hL, hLN, hLT, hLD, b, hb, hbL⟩ := hTransfer a.val ha
  have hList : L.E.Sublist (MT.E.map ((Subtype.val : Oa → (split T r).1) ⁻¹' ·)) := by
    let E := membersThrough MT.E (origMembers Sec H) a.val
    have hs : (memberRestrict MT E).E.Sublist MT.E := by
      rw [memberRestrict_membersThrough_E]
      exact List.filter_sublist
    exact hs.map _
  have hBoundary : MT.E = boundary Sec.E H :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec)
      (𝔫 := (⟨univ, Sec.E, IdealWeightPowers.unitIdeal (n + 1) X, 1⟩ : MarkedIdeal (n + 1) X)) rfl H
  have hList' : L.E.Sublist ((boundary Sec.E H).map ((Subtype.val : Oa → (split T r).1) ⁻¹' ·)) := by
    rw [← hBoundary]
    exact hList
  have hTrans0 : IsTransverse (n + 1) (zeroPlane U) Sec.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hTransA : IsTransverse (n + 1) A MT.E :=
    hBoundary.symm ▸ (hHead.geometry (Nat.succ_pos n) hSec.isWellFormed.isSNCDivisor hTrans0).2
  have hTransW := isTransverse_of_forall_mem
    (isTransverse_preimage (pullsBackCoordinates_val Oa) hTransA) hList.subset
  have hSmall' := Lift.forget_boundary hGeo (E' := L.E) hList'
  have hLHol : ∀ x f, L.ideal.mem x f → HolomorphicAt (n + 1) f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hL.isCoherent hf
  have hK := HironakaActualNativeSectionNormalCrossings.Lift.native_test hSmall'
    (Nat.succ_pos n) hL.isSNCDivisor hTransW L rfl hLN hLHol hLT
  have hbV : b.val ∈ V := by rw [hb, ← hz]; exact z.property
  let bw : nativeManifold (Nat.le_succ n) (openSection V (openPreimage S Oa)) hZ' := ⟨b, hbV⟩
  have hbw : bw ∈ (geoTransformAlong
      (nativePullback (Nat.le_succ n) (openSection A Oa) (openSection_regular hA Oa) L) K).cosupp := by
    rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hSmall'
      (Nat.succ_pos n) hL.isSNCDivisor hTransW L rfl hLN hLHol]
    exact hbL
  obtain ⟨hOwnD, hOwnT, w, hw, hwL⟩ :=
    own_window_test hTail Oa ON hWindow L LN hL.isCoherent f hf hInit K hIso hLD hK bw hbw
  exact ⟨hOwnD, hOwnT, w, Subtype.ext (hw.trans (hb.trans hz.symm)), hwL⟩


end
end Hironaka.HironakaG1PositiveNormalOwnTailTest
