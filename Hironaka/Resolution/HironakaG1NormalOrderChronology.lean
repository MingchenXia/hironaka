import Hironaka.Resolution.HironakaG1NormalOrderCompanion
import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.Resolution.HironakaActualNativeCompanionHistories
import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Invariant.NonmonomialOrderTransport

/-! The original nonmonomial-order clock on an actual supported normal
history and its literal transported native history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NormalOrderChronology
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec InvDomainTowerAlong NonmonomialOrderLocal NonmonomialOrderTail
  NonmonomialOrderRegime NonmonomialOrderTransport StepOneRegime
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOriginalCuts
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionInitialBar
  HironakaActualNativeSectionNormalCrossings HironakaActualNativeCompanionHistories
  HironakaActualNativeInvariantDomain HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaActualOpenSectionRepresentative NormalCrossings
  HironakaG1NormalOrderCompanion HironakaG1ControlledCarrierRestriction
  HironakaG1ProperCarrierNormalContact SubmanifoldChartedSpace
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  CompanionRebase CoefficientIdealRestriction InvDomainCompanion InvDomainRebase

private theorem recast_split_iso {n : ℕ} {X' X Y' Y W' W V : CMfd.{0} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    {P' : BlowupTower X' W'} {P : BlowupTower X W}
    {S' : BlowupTower W' Y'} {S : BlowupTower W Y}
    {ψ : W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ W}
    (hP : IsTowerIso Φ P' P ψ) (hS : IsTowerIso ψ S' S χ) (e : W = V) :
    ∃ η : W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V,
      IsTowerIso Φ P' (recastTarget e P) η ∧
        IsTowerIso η S' (recastSource e S) χ := by
  cases e
  exact ⟨ψ, hP, hS⟩

private theorem masked_companion_pullback_of_whole {n m k : ℕ}
    {X : CMfd.{0} n} {Y : CMfd.{0} m} (hn : 0 < n) (hm : 0 < m)
    {A : MarkedIdeal n X} {B : MarkedIdeal m Y}
    (hA : IsInvDomain k A) (hB : IsInvDomain k B) {o : ℕ} (ho : 0 < o)
    {f : Y → X} (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hWhole : markedPullback (m := m) f (companionOf n A o) = companionOf m B o)
    (hMask : ∀ p ∈ ordMask B o, f p ∈ ordMask A o) :
    let V := ordMask B o
    let W := ordMask A o
    let g : V → W := fun p => ⟨f p.val, hMask p.val p.property⟩
    markedPullback (m := m) g
        (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) A) o) =
      companionOf m (M := CMfd.of (n := m) V) (MarkedIdeal.pullback (Subtype.val : V → Y) B) o := by
  let V := ordMask B o
  let W := ordMask A o
  let g : V → W := fun p => ⟨f p.val, hMask p.val p.property⟩
  have hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff W g).mp (hf.comp contMDiff_subtype_val)
  have hc := (isInvDomain_companionAlong hn hA ho).isWellFormed.isCoherent
  change markedPullback (m := m) g
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) A) o) =
    companionOf m (M := CMfd.of (n := m) V) (MarkedIdeal.pullback (Subtype.val : V → Y) B) o
  rw [← pullback_val_companionOf hn hA.isWellFormed hA.isNonzeroAlongAt W o,
    ← pullback_val_companionOf hm hB.isWellFormed hB.isNonzeroAlongAt V o, ← hWhole]
  exact (whole_markedPullback_comp contMDiff_subtype_val hg (companionOf n A o) hc).symm.trans
    (whole_markedPullback_comp hf contMDiff_subtype_val (companionOf n A o) hc)

set_option maxHeartbeats 800000 in
/-- The same supported normal test and literal original native test have
identical order-regime clocks. At every split, the actual head inclusion
commutes with the tail projections and identifies the head order flags and
order masks. The whole positive companion on a head's kept ambient carrier
pulls back on the actual head mask, preserving its mark and ordered boundary.
In particular this applies at the run head selected by either clock. -/
theorem exists_original_native_order_chronology {n k : ℕ}
    {U : Opens (ComplexModel n)} (hn : 0 < n)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    ∃ (C : Set Y) (hCc : IsClosed C) (hC : ∀ y ∈ C, RegularAtDim (n := n+1) C y n)
      (N : BlowupTower
        (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) C hC)),
      let H := transport (nativeZeroSectionEquiv U) N
      let M := supportedNormalMarked Q
      (∃ hWc : IsClosed (zeroPlane U),
        Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) M.E T C hCc hC N) ∧
      H.tower.length = T.length ∧ IsGeoTestTower Q H.tower ∧
      (∀ o (z : H.target),
        regimeRun (OrdRegime Q o) H.tower z =
          regimeRun (OrdRegime M o) T (H.back z).val) ∧
      ∀ j, ∃ (P : Set (split T j).1) (hP : ∀ y ∈ P, RegularAtDim (n := n+1) P y n)
        (η : (split H.tower j).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          nativeManifold (Nat.le_succ n) P hP),
        P = HomogenizedGlueingTower.strictAlong (head T j) (zeroPlane U) ∧
        (∀ z : H.target, (η ((tail H.tower j).proj z)).val =
          (tail T j).proj (H.back z).val) ∧
        (∀ o p,
          (OrdRegime Q o (head H.tower j) p ↔ OrdRegime M o (head T j) (η p).val) ∧
          regimeRun (OrdRegime Q o) (head H.tower j) p =
            regimeRun (OrdRegime M o) (head T j) (η p).val ∧
          (p ∈ ordMask (geoTransformAlong Q (head H.tower j)) o ↔
            (η p).val ∈ ordMask (geoTransformAlong M (head T j)) o)) ∧
        (∀ o (z : H.target),
          z ∈ openPreimage (tail H.tower j) (ordMask (geoTransformAlong Q (head H.tower j)) o) ↔
            (H.back z).val ∈ openPreimage (tail T j) (ordMask (geoTransformAlong M (head T j)) o)) ∧
        ∀ o, 0 < o →
          let A := withN (geoTransformAlong (properNormalMarked Q) (head T j))
            (geoTransformAlong M (head T j)).N
          let B := geoTransformAlong Q (head H.tower j)
          let W := ordMask A o
          let V := ordMask B o
          ∃ hMask : ∀ p ∈ V, (η p).val ∈ W,
            let g : V → W := fun p => ⟨(η p.val).val, hMask p.val p.property⟩
            let J := companionOf n (M := CMfd.of (n := n) V)
              (MarkedIdeal.pullback (Subtype.val : V → (split H.tower j).1) B) o
            let K := companionOf (n+1) (M := CMfd.of (n := n+1) W)
              (MarkedIdeal.pullback (Subtype.val : W → (split T j).1) A) o
            markedPullback (m := n) g K = J ∧ J.E = K.E.map (g ⁻¹' ·) ∧
              J.d = (if o < Q.d then o * (Q.d - o) else o) ∧ K.d = J.d := by
  let M := supportedNormalMarked Q
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hMT := (hPM.wEquiv.2 T).1.mp hT
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) M.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt (n+1) g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hM.isWellFormed.isCoherent hg
  obtain ⟨C, hCc, hC, N, hLift, hNativeTest, _, hLength, hBaseTest, _⟩ :=
    exists_literal_original_native_test_history Q hQ T hT
  let H := transport (nativeZeroSectionEquiv U) N
  let NB := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  have hNB : IsInvDomain k NB :=
    isInvDomain_nativePullback (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) NB = Q :=
    native_supported_input_record Q hQ
  have hIso := transport_isTowerIso (nativeZeroSectionEquiv U) N
  refine ⟨C, hCc, hC, N, ⟨_, hLift⟩, hLength, hBaseTest, ?_, ?_⟩
  · intro o z
    have hRun := regimeRun_ordRegime_isTowerIso hn (nativeZeroSectionEquiv U) hNB o hIso hNativeTest z
    rw [hInput] at hRun
    exact hRun.trans (Lift.original_order_regime_run hLift (Nat.succ_pos n)
      hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol o (H.back z)).symm
  · intro j
    obtain ⟨P, hPc, hP, e, hHead, hTail⟩ := Lift.original_head_tails hLift j
    obtain ⟨ψ, hIsoHead, hIsoTail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hIso j
    obtain ⟨η, hHeadIso, hTailIso⟩ := recast_split_iso hIsoHead hIsoTail e
    have hMHead := ((isGeoTestTower_iff_head_tail M T j).mp hMT).1
    have hNBHead := Lift.native_test hHead (Nat.succ_pos n)
      hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol hMHead
    have hSquare (z : H.target) : (η ((tail H.tower j).proj z)).val =
        (tail T j).proj (H.back z).val :=
      (congrArg Subtype.val (hTailIso.proj_comm z)).trans (hTail.square (H.back z)).symm
    obtain ⟨hNativeComp, hNativeMask, _⟩ :=
      Lift.original_current_companion_masks (X := CMfd.of (n := n+1) (productOpen U))
        (Y := (split T j).1) (T := head T j) (Q := recastTarget e (head N j))
        (Nat.succ_pos n) hn (supportedNormalMarked Q) hM hSupport hTrans hHead hMHead
    have hHeadMask (o : ℕ) (p : (split H.tower j).1) :
        p ∈ ordMask (geoTransformAlong Q (head H.tower j)) o ↔
          (η p).val ∈ ordMask (geoTransformAlong M (head T j)) o := by
      have hMask := mem_ordMask_isTowerIso_iff hn (nativeZeroSectionEquiv U) hNB
        hHeadIso hNBHead o p
      rw [hInput] at hMask
      exact hMask.trans (hNativeMask o (η p)).symm
    refine ⟨P, hP, η, hHead.carrier, hSquare, ?_, ?_, ?_⟩
    · intro o p
      have hReg := ordRegime_isTowerIso_iff hn (nativeZeroSectionEquiv U) hNB o hHeadIso hNBHead p
      rw [hInput] at hReg
      have hNativeReg := Lift.original_order_regime hHead (Nat.succ_pos n)
        hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol o (η p)
      have hRun := regimeRun_ordRegime_isTowerIso hn (nativeZeroSectionEquiv U) hNB o
        hHeadIso hNBHead p
      rw [hInput] at hRun
      have hNativeRun := Lift.original_order_regime_run hHead (Nat.succ_pos n)
        hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol o (η p)
      exact ⟨hReg.trans hNativeReg.symm, hRun.trans hNativeRun.symm, hHeadMask o p⟩
    · intro o z
      have hMask := hHeadMask o ((tail H.tower j).proj z)
      rw [hSquare z] at hMask
      exact hMask
    · intro o ho A B W V
      let Z := (split T j).1
      let := chartedSpace (Nat.le_succ n) hP
      have := isComplexManifold_chartedSpace (Nat.le_succ n) hP
      let L := nativeManifold (Nat.le_succ n) P hP
      let F := (split H.tower j).1
      let f : F → Z := fun p => (η p).val
      have hPHead := ((isGeoTestTower_iff_head_tail (properNormalMarked Q) T j).mp hT).1
      have hDomP := isInvDomain_geoTransformAlong (properNormalMarked_isInvDomain Q hQ)
        (head T j) hPHead
      have hDomM := isInvDomain_geoTransformAlong hM (head T j) hMHead
      have hRestriction := properNormal_supported_restrictEquiv Q hQ (head T j) hPHead
      have hA : IsInvDomain k A :=
        isInvDomain_of_restrictEquiv hDomM
          ⟨hRestriction.N_eq.symm, hRestriction.E_eq.symm, hRestriction.d_eq.symm,
            hRestriction.ge, hRestriction.le⟩ hDomP.isWellFormed.isCoherent
      have hBaseHead := ((isGeoTestTower_iff_head_tail Q H.tower j).mp hBaseTest).1
      have hB := isInvDomain_geoTransformAlong hQ (head H.tower j) hBaseHead
      have hMid := isInvDomain_geoTransformAlong hNB (recastTarget e (head N j)) hNBHead
      have hHeadWhole : B = MarkedIdeal.pullback η (geoTransformAlong NB (recastTarget e (head N j))) := by
        have h := IsTowerIso.geoTransformAlong_eq (nativeZeroSectionEquiv U)
          hNB.isWellFormed.isClosedSubmanifold_N hNB.isWellFormed.isCoherent hHeadIso hNBHead
        simpa only [hInput] using h
      have hVal : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n+1)) ∞
          (Subtype.val : L → Z) := contMDiff_val (Nat.le_succ n) hP
      have hWholeComp : markedPullback (m := n) f (companionOf (n+1) A o) = companionOf n B o := by
        have hc := (isInvDomain_companionAlong (Nat.succ_pos n) hA ho).isWellFormed.isCoherent
        change markedPullback (m := n) ((Subtype.val : L → Z) ∘ η) (companionOf (n+1) A o) = _
        rw [whole_markedPullback_comp hVal η.contMDiff _ hc]
        change MarkedIdeal.pullback η
          (nativePullback (Nat.le_succ n) P hP (companionOf (n+1) A o)) = _
        rw [show A = withN (geoTransformAlong (properNormalMarked Q) (head T j))
          (geoTransformAlong M (head T j)).N from rfl,
          current_companionOf_on_kept_carrier Q hQ (head T j) hPHead o, hNativeComp o, hHeadWhole]
        exact pullback_diffeo_companionOf hn η hMid.isWellFormed hMid.isNonzeroAlongAt o
      have hSameMask : W = ordMask (geoTransformAlong M (head T j)) o := by
        apply Opens.ext
        change (closure (ordGe A (o+1)))ᶜ = (closure (ordGe (geoTransformAlong M (head T j)) (o+1)))ᶜ
        rw [ordGe_congr hRestriction hA.isWellFormed.isClosedSubmanifold_N.1 (o+1)]
      have hMatch : ∀ p ∈ V, f p ∈ W := by
        intro p hp
        rw [hSameMask]
        exact (hHeadMask o p).mp hp
      have hRecord := masked_companion_pullback_of_whole (Nat.succ_pos n) hn hA hB ho
        (hVal.comp η.contMDiff) hWholeComp hMatch
      refine ⟨hMatch, hRecord, ?_, ?_, ?_⟩
      · exact (congrArg (fun J : MarkedIdeal n V => J.E) hRecord).symm
      · simp only [companionOf, companionAlong_d, MarkedIdeal.pullback, B, d_geoTransformAlong]
      · exact congrArg (fun J : MarkedIdeal n V => J.d) hRecord

end
end Hironaka.HironakaG1NormalOrderChronology
