import Hironaka.Resolution.HironakaG1ControlledCarrierRestriction
import Hironaka.Resolution.HironakaActualNativeCompanionHistories
import Hironaka.Invariant.NonmonomialOrderTransport

/-! The current order companion on the kept normal carrier and its literal
descent to the original input's native test history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NormalOrderCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec InvDomainTowerAlong CompanionRebase CoefficientIdealRestriction
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderTransport
  InvDomainCompanion InvDomainRebase CompanionReductionAlong HomogenizedIdealAlong
  HironakaActualNativeCompanionHistories
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionInitialBar
  HironakaActualNativeInvariantDomain HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaG1ControlledCarrierRestriction
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenSectionRepresentative NormalCrossings

/-- Recompute the whole current companion on the actual kept strict carrier.
The upper mark and all chronological boundary slots are inherited before
taking monomial factors or computing the companion. -/
theorem current_companionOf_on_kept_carrier {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (o : ℕ) :
    companionOf (n+1) (withN (geoTransformAlong (properNormalMarked Q) T)
      (geoTransformAlong (supportedNormalMarked Q) T).N) o =
        companionOf (n+1) (geoTransformAlong (supportedNormalMarked Q) T) o := by
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hMT := (hPM.wEquiv.2 T).1.mp hT
  have hCurrent := isInvDomain_geoTransformAlong hM T hMT
  exact companionOf_congr (properNormal_supported_restrictEquiv Q hQ T hT)
    hCurrent.isWellFormed.isClosedSubmanifold_N.1 o

private theorem mem_masked_companion_cosupp_of_order {n k : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) {B : MarkedIdeal n X} (hB : IsInvDomain k B)
    {z : X} (hz : z ∈ B.cosupp) {o : ℕ} (ho : 0 < o) (hOrder : nmOrd B z = o)
    (hzMask : z ∈ ordMask B o) :
    let V := ordMask B o
    let BV := MarkedIdeal.pullback (Subtype.val : V → X) B
    (⟨z, hzMask⟩ : V) ∈ (companionOf n (M := CMfd.of (n := n) V) BV o).cosupp := by
  let V := ordMask B o
  let BV := MarkedIdeal.pullback (Subtype.val : V → X) B
  have hBV := isInvDomain_pullback_val V hB
  have hBound : ∀ x ∈ BV.cosupp, x ∉ ordGe (M := CMfd.of (n := n) V) BV (o+1) :=
    CompanionOpen.bound_pullback_val hn hB.isWellFormed hB.isNonzeroAlongAt V
      (fun _ _ hx => notMem_ordGe_of_mem_ordMask hx)
  have hcos := cosupp_companionOf_geoTransformAlong (𝔫 := BV) hn hBV ho hBound
    (BlowupTower.refl : BlowupTower (CMfd.of (n := n) V) (CMfd.of (n := n) V)) trivial
  change (companionOf n (M := CMfd.of (n := n) V) BV o).cosupp =
    ordGe (M := CMfd.of (n := n) V) BV o ∩ BV.cosupp at hcos
  dsimp only
  rw [hcos]
  constructor
  · exact (mem_ordGe_pullback_val_iff hn hB.isWellFormed hB.isNonzeroAlongAt V o
      ⟨z, hzMask⟩).mpr ((mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hz.1 o).mpr hOrder.ge)
  · rw [MarkedIdealRestrictOpen.cosupp_pullback_val B
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hB.isWellFormed.isCoherent hg)]
    exact hz

/-- An ordinary upper test gives an actual native test of the original Q.
At its endpoint, recomputing the upper companion on the kept strict carrier
and pulling it back gives the whole original current companion. The same
identification reads the current order mask at every native point. At
positive-order cosupport points, both masked companions have maximal order,
agree on the true branch mark, and contain the corresponding anchor. -/
theorem exists_original_current_order_companion_history {n k : ℕ}
    {U : Opens (ComplexModel n)} (hn : 0<n)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    ∃ (C : Set Y) (hCc : IsClosed C) (hC : ∀y∈C, RegularAtDim (n := n+1) C y n)
      (N : BlowupTower
        (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) C hC)),
      (∃ hWc : IsClosed (zeroPlane U),
        Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
          (supportedNormalMarked Q).E T C hCc hC N) ∧
      let H := transport (nativeZeroSectionEquiv U) N
      let A := withN (geoTransformAlong (properNormalMarked Q) T)
        (geoTransformAlong (supportedNormalMarked Q) T).N
      H.tower.length = T.length ∧ IsGeoTestTower Q H.tower ∧
      (∀ o, MarkedIdeal.pullback H.back
        (nativePullback (Y := Y) (Nat.le_succ n) C hC (companionOf (n+1) A o)) =
          companionOf n (geoTransformAlong Q H.tower) o) ∧
      (∀ o (z : H.target), z ∈ ordMask (geoTransformAlong Q H.tower) o ↔
        (H.back z).val ∈ ordMask A o) ∧
      ∀ (z : H.target), z ∈ (geoTransformAlong Q H.tower).cosupp →
        let o := nmOrd (geoTransformAlong Q H.tower) z
        0 < o →
        nmOrd A (H.back z).val = o ∧
        ∃ (hz : z ∈ ordMask (geoTransformAlong Q H.tower) o)
          (ha : (H.back z).val ∈ ordMask A o),
          let V := ordMask (geoTransformAlong Q H.tower) o
          let W := ordMask A o
          let J := companionOf n (M := CMfd.of (n := n) V)
            (MarkedIdeal.pullback (Subtype.val : V → H.target) (geoTransformAlong Q H.tower)) o
          let K := companionOf (n+1) (M := CMfd.of (n := n+1) W)
            (MarkedIdeal.pullback (Subtype.val : W → Y) A) o
          IsInvDomain k J ∧ IsInvDomain k K ∧
            IsMaximalOrderAlong J.N J.ideal J.d ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧
            J.d = (if o < Q.d then o * (Q.d - o) else o) ∧ K.d = J.d ∧
            (⟨z, hz⟩ : V) ∈ J.cosupp ∧ (⟨(H.back z).val, ha⟩ : W) ∈ K.cosupp := by
  let M := supportedNormalMarked Q
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hMT := (hPM.wEquiv.2 T).1.mp hT
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) M.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  obtain ⟨C, hCc, hC, N, hLift, hNativeTest, _hNativeWhole, hLength, hBaseTest, _hSquare, _hBoundary, hBaseCos, _⟩ :=
    exists_literal_original_native_test_history Q hQ T hT
  let H := transport (nativeZeroSectionEquiv U) N
  let A := withN (geoTransformAlong (properNormalMarked Q) T) (geoTransformAlong M T).N
  let NB := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  have hNB : IsInvDomain k NB :=
    isInvDomain_nativePullback (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hCurrentNB := isInvDomain_geoTransformAlong hNB N hNativeTest
  have hIso := transport_isTowerIso (nativeZeroSectionEquiv U) N
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) NB = Q :=
    native_supported_input_record Q hQ
  have hWhole : geoTransformAlong Q H.tower = MarkedIdeal.pullback H.back (geoTransformAlong NB N) := by
    have h := IsTowerIso.geoTransformAlong_eq (nativeZeroSectionEquiv U)
      hNB.isWellFormed.isClosedSubmanifold_N hNB.isWellFormed.isCoherent hIso hNativeTest
    simpa only [hInput] using h
  obtain ⟨hCompanion, hMask, _⟩ :=
    Lift.original_current_companion_masks (X := CMfd.of (n := n+1) (productOpen U))
      (Y := Y) (T := T) (Q := N) (Nat.succ_pos n) hn (supportedNormalMarked Q)
      hM hSupport hTrans hLift hMT
  have hCurrentM := isInvDomain_geoTransformAlong hM T hMT
  have hRestriction := properNormal_supported_restrictEquiv Q hQ T hT
  have hMasks (o : ℕ) (z : H.target) :
      z ∈ ordMask (geoTransformAlong Q H.tower) o ↔ (H.back z).val ∈ ordMask A o := by
    have hTransport := mem_ordMask_isTowerIso_iff hn (nativeZeroSectionEquiv U) hNB
      hIso hNativeTest o z
    rw [hInput] at hTransport
    have hOrderGe := ordGe_congr hRestriction hCurrentM.isWellFormed.isClosedSubmanifold_N.1 (o+1)
    have hSameMask : ordMask A o = ordMask (geoTransformAlong M T) o := by
      apply Opens.ext
      change (closure (NonmonomialOrderLocal.ordGe A (o+1)))ᶜ =
        (closure (NonmonomialOrderLocal.ordGe (geoTransformAlong M T) (o+1)))ᶜ
      rw [hOrderGe]
    exact hTransport.trans ((hMask o (H.back z)).symm.trans (by rw [hSameMask]))
  refine ⟨C, hCc, hC, N, ⟨_, hLift⟩, hLength, hBaseTest, ?_, hMasks, ?_⟩
  · intro o
    rw [current_companionOf_on_kept_carrier Q hQ T hT o, hCompanion o, hWhole]
    exact pullback_diffeo_companionOf hn H.back hCurrentNB.isWellFormed hCurrentNB.isNonzeroAlongAt o
  · intro z hz o ho
    let B := geoTransformAlong Q H.tower
    have hB := isInvDomain_geoTransformAlong hQ H.tower hBaseTest
    have hP := isInvDomain_geoTransformAlong (properNormalMarked_isInvDomain Q hQ) T hT
    have hA : IsInvDomain k A :=
      isInvDomain_of_restrictEquiv hCurrentM
        ⟨hRestriction.N_eq.symm, hRestriction.E_eq.symm, hRestriction.d_eq.symm,
          hRestriction.ge, hRestriction.le⟩ hP.isWellFormed.isCoherent
    have hOrder : nmOrd A (H.back z).val = nmOrd B z := by
      unfold nmOrd
      congr 1
      ext q
      exact ((mem_ordMask_iff (Nat.succ_pos n) hA.isWellFormed hA.isNonzeroAlongAt q
          (H.back z).val).symm.trans ((hMasks q z).symm.trans
        (mem_ordMask_iff hn hB.isWellFormed hB.isNonzeroAlongAt q z)))
    have hzNot : z ∉ ordGe B (o+1) := by
      intro hx
      have h := (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hz.1 (o+1)).mp hx
      exact (Nat.not_succ_le_self o) h
    have hzMask := (mem_ordMask_iff hn hB.isWellFormed hB.isNonzeroAlongAt o z).mpr hzNot
    let V := ordMask B o
    let W := ordMask A o
    let BV := MarkedIdeal.pullback (Subtype.val : V → H.target) B
    let J := companionOf n (M := CMfd.of (n := n) V) BV o
    let K := companionOf (n+1) (M := CMfd.of (n := n+1) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y) A) o
    have haMask := (hMasks o z).mp hzMask
    have ha : (H.back z).val ∈ A.cosupp := by
      have hCos := (hPM.wEquiv.2 T).2 hT
      rw [hRestriction.cosupp_eq, ←hCos]
      rw [hBaseCos] at hz
      exact hz
    have hzJ := mem_masked_companion_cosupp_of_order hn hB hz ho rfl hzMask
    have haK := mem_masked_companion_cosupp_of_order (Nat.succ_pos n) hA ha ho hOrder haMask
    have hJd : J.d = (if o < Q.d then o * (Q.d - o) else o) := by
      simp only [J, companionOf, companionAlong_d, BV, MarkedIdeal.pullback, B, d_geoTransformAlong]
    have hKd : K.d = J.d := by
      rw [hJd]
      simp only [K, companionOf, companionAlong_d, MarkedIdeal.pullback, A, withN_d, d_geoTransformAlong]
      rfl
    refine ⟨hOrder, hzMask, haMask, ?_, ?_, ?_, ?_, hJd, hKd, hzJ, haK⟩
    · exact isInvDomain_companionAlong_pullback_val hn hB V ho
    · exact isInvDomain_companionAlong_pullback_val (Nat.succ_pos n) hA W ho
    · rw [show J.N = BV.N from companionAlong_N _ _ _ _ _ _]
      exact CompanionOpen.isMaximalOrderAlong_companionOf_pullback_val hn hB V
        (fun _ _ hx => notMem_ordGe_of_mem_ordMask hx)
    · rw [show K.N = (MarkedIdeal.pullback (Subtype.val : W → Y) A).N from
          companionAlong_N _ _ _ _ _ _]
      exact CompanionOpen.isMaximalOrderAlong_companionOf_pullback_val (Nat.succ_pos n) hA W
        (fun _ _ hx => notMem_ordGe_of_mem_ordMask hx)

end
end Hironaka.HironakaG1NormalOrderCompanion
