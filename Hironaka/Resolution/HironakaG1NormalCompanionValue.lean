import Hironaka.Resolution.HironakaG1NormalOrderCanTransport
import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaG3RWindowLowerData
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Resolution.HironakaG1NormalOrderTail
import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts
import Hironaka.Resolution.HironakaActualNativeCompanionHistories
import Hironaka.Resolution.HironakaDisjointRecursiveNativeHistory
import Hironaka.Invariant.CompanionTowerIso

/-! The actual supported companion tail inherits TEST from the literal
native original CAN along the same normal Lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NormalCompanionValue
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec InvDomainTowerAlong NonmonomialOrderCanonical NonmonomialOrderLocal
  NonmonomialOrderRegime NonmonomialOrderTail NonmonomialOrderTransport StepOneRegime CanonicalCentres
  GeneralValue GeneralCompare CompanionRebase CompanionReductionAlong CompanionTowerIso InvDomainCompanion
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOriginalCuts
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeCompanionHistories HironakaActualNativeInvariantDomain
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaActualOpenSectionRepresentative HironakaG1NormalOrderTail
  HironakaDisjointRecursiveNativeHistory HironakaDisjointNativeReferenceWindow
  StepOneTangentChange NormalCrossings NormalCrossingsInvariance HironakaDisjointNativeOpenLift
  HironakaG1SupportedStepOne HomogenizedIdealAlong MarkedIdealRestrictOpen
  HironakaG3RWindowLowerData GeneralCanonicalTail MaxOrderValue StepOneSeq
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalFamilyDepthStability HironakaActualSectionBoundaryDimension

private theorem recast_split_iso {n : ℕ} {X' X Y' Y W' W V : CMfd.{0} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    {P' : BlowupTower X' W'} {P : BlowupTower X W}
    {S' : BlowupTower W' Y'} {S : BlowupTower W Y}
    {ψ : W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ W}
    (hP : IsTowerIso Φ P' P ψ) (hS : IsTowerIso ψ S' S χ) (e : W = V) :
    ∃ η : W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V,
      IsTowerIso Φ P' (recastTarget e P) η ∧ IsTowerIso η S' (recastSource e S) χ := by
  cases e
  exact ⟨ψ, hP, hS⟩

/-- Values and cosupport along the geometric inclusion of literal masked
companion endpoints. -/
def StepOneCompanionReads {n q a : ℕ} (hn : 0 < n)
    {A B : CMfd.{0} n} {X Y : CMfd.{0} (n+1)}
    (J : MarkedIdeal n A) (K : MarkedIdeal (n+1) X)
    (S : BlowupTower A B) (T : BlowupTower X Y) (i : B → Y) : Prop :=
  ∀ p : B, p ∈ (geoTransformAlong J S).cosupp →
    i p ∈ (geoTransformAlong K T).cosupp ∧
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (a+q)) K T (i p) =
      stepDimensionMap (depthPadMap a q ∘ sameIndexMap 1 q)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) J S p)

set_option maxHeartbeats 1800000 in
/-- Literal original native CAN supplies canonical Step One on the same
actual supported companion tail, at arbitrary additional ambient depth. -/
theorem supported_step_one_companion_of_native_canonical {n q : ℕ}
    {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q+1) Q) (a : ℕ)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T)
    {C : Set Y} {hCc : IsClosed C} {hC : ∀ y ∈ C, RegularAtDim (n := n+1) C y n}
    {hWc : IsClosed (zeroPlane U)}
    (N : BlowupTower
      (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Y := Y) (Nat.le_succ n) C hC))
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (supportedNormalMarked Q).E T C hCc hC N)
    (hfCan : IsCanonical Q ((invFamily hn (q+1)).inv Q)
      (transport (nativeZeroSectionEquiv U) N).tower) :
    let H := transport (nativeZeroSectionEquiv U) N
    let M := supportedNormalMarked Q
    ∀ (z : H.target) (o : ℕ), z ∈ (geoTransformAlong Q H.tower).cosupp →
      nmOrd (geoTransformAlong Q H.tower) z = o → 0 < o →
      let r := regimeRun (OrdRegime Q o) H.tower z
      r = regimeRun (OrdRegime M o) T (H.back z).val ∧
      let W := ordMask (geoTransformAlong M (head T r)) o
      let K := compAt M o (head T r)
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (a+q)) K)
        (restrict W (tail T r)) ∧
      let V := ordMask (geoTransformAlong Q (head H.tower r)) o
      let J := compAt Q o (head H.tower r)
      ∃ i : openPreimage (tail H.tower r) V → openPreimage (tail T r) W,
        (∀ p, (i p).val = (H.back p.val).val) ∧
        StepOneCompanionReads (q := q) (a := a) hn
          (A := CMfd.of (n := n) V) (B := CMfd.of (n := n) (openPreimage (tail H.tower r) V))
          (X := CMfd.of (n := n+1) W) (Y := CMfd.of (n := n+1) (openPreimage (tail T r) W))
          J K (restrict V (tail H.tower r)) (restrict W (tail T r)) i := by
  let M := supportedNormalMarked Q
  let H := transport (nativeZeroSectionEquiv U) N
  let f : ∀ {X' : CMfd.{0} n}, MarkedIdeal n X' → ∀ {Y' : CMfd.{0} n},
      BlowupTower X' Y' → Y' → ℕ ×ₗ WithTop (ValTy q) :=
    fun {X'} J {Y'} S p => Seq.StepOneValueMasked.stepOneInvM
      (X := X') (invFamily hn q) J (Y := Y') S p
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (invFamily hn q) hn
  have hCan : IsCanonical Q (genInv f Q) H.tower := hfCan
  let g : ∀ {Z : CMfd.{0} (n+1)}, BlowupTower (CMfd.of (n := n+1) (productOpen U)) Z → Z → ℕ :=
    fun S p => nmOrd (geoTransformAlong M S) p
  have hg : OrdMonotone M g := fun _ _ _ _ _ _ h => h
  obtain ⟨hBaseTest, hNative⟩ :=
    original_native_order_companion_tail_of_canonical hn Q hQ T hT N hLift
      (genInv f Q) (ordMonotone_genInv (X := CMfd.of (n := n) U) f Q) hCan g hg
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hMT := (hPM.wEquiv.2 T).1.mp hT
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) M.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hHol : ∀ x a, M.ideal.mem x a → HolomorphicAt (n+1) a x :=
    fun _ _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hM.isWellFormed.isCoherent ha
  let NB := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  have hNB : IsInvDomain (q+1) NB :=
    isInvDomain_nativePullback (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) NB = Q :=
    native_supported_input_record Q hQ
  have hIso := transport_isTowerIso (nativeZeroSectionEquiv U) N
  intro H0 M0 z o hz hoz ho r
  obtain ⟨hRun, _, _, _⟩ := hNative z o hz hoz ho
  have hData := hasGenLowerData_of_isCanonical f hF hn hQ H.tower hBaseTest hCan z hz o hoz ho
  obtain ⟨_, hJDom, hJMax, hJCan, _⟩ := hData
  refine ⟨hRun, ?_⟩
  intro W0 K0
  obtain ⟨P, hPc, hP, e, hHead, hTail⟩ := Lift.original_head_tails hLift r
  obtain ⟨ψ, hIsoHead, hIsoTail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hIso r
  obtain ⟨η, hHeadIso, hTailIso⟩ := recast_split_iso hIsoHead hIsoTail e
  let A := geoTransformAlong M (head T r)
  let Nh := recastTarget e (head N r)
  let Nt := recastSource e (tail N r)
  let B := geoTransformAlong NB Nh
  let L := companionOf (n+1) A o
  let Bc := companionOf n B o
  let W := ordMask A o
  let V := ordMask (geoTransformAlong Q (head H.tower r)) o
  let F := nativeWindow (Nat.le_succ n) P hP W
  have hMHead := ((isGeoTestTower_iff_head_tail M T r).mp hMT).1
  have hA := isInvDomain_geoTransformAlong hM (head T r) hMHead
  have hNBHead := Lift.native_test hHead (Nat.succ_pos n)
    hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol hMHead
  have hB := isInvDomain_geoTransformAlong hNB Nh hNBHead
  have hBC := isInvDomain_companionAlong hn hB ho
  have hL := isInvDomain_companionAlong (Nat.succ_pos n) hA ho
  obtain ⟨hComp, hMask, _⟩ :=
    Lift.original_current_companion_masks (X := CMfd.of (n := n+1) (productOpen U))
      (Y := (split T r).1) (T := head T r) (Q := Nh)
      (Nat.succ_pos n) hn (supportedNormalMarked Q) hM hSupport hTrans hHead hMHead
  have hMatch (p : (split H.tower r).1) : p ∈ V ↔ η p ∈ F := by
    have h := mem_ordMask_isTowerIso_iff hn (nativeZeroSectionEquiv U) hNB
      hHeadIso hNBHead o p
    rw [hInput] at h
    exact h.trans (hMask o (η p)).symm
  let α := diffeoOpens η V F hMatch
  have hMaskIso := isTowerIso_restrictOpens hMatch hTailIso
    (isTowerIso_mem_openPreimage_iff hTailIso hMatch)
  have hRec := companionOf_isTowerIso (nativeZeroSectionEquiv U) hn hNB ho
    hHeadIso hNBHead V F α (fun _ => rfl)
  rw [hInput] at hRec
  let J := compAt Q o (head H.tower r)
  let K := compAt M o (head T r)
  let BF := MarkedIdeal.pullback (Subtype.val : F → _) Bc
  have hQHead := ((isGeoTestTower_iff_head_tail Q H.tower r).mp hBaseTest).1
  have hJRec : J = MarkedIdeal.pullback α BF :=
    (compAt_eq_pullback hn o (head H.tower r)
      (isInvDomain_geoTransformAlong hQ (head H.tower r) hQHead)).trans hRec
  change IsInvDomain (q+1) J at hJDom
  change IsMaximalOrderAlong J.N J.ideal J.d at hJMax
  change IsCanonical J (f J) (restrict V (tail H.tower r)) at hJCan
  have hBF := isInvDomain_pullback_val F hBC
  have hInvRec : MarkedIdeal.pullback α.symm J = BF := by
    rw [hJRec, pullback_symm_pullback_of_isCoherent α hBF.isWellFormed.isCoherent]
  have hBFCan : IsCanonical BF (f BF) (restrict F Nt) := by
    have h := hF.isCanonical_of_isTowerIso hJDom hJMax α.symm hMaskIso.symm hJCan
    rw [hInvRec] at h
    exact h
  have hNativeComp : nativePullback (Nat.le_succ n) P hP L = Bc := hComp o
  have hEN : A.E = boundary M.E (head T r) :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := M) (𝔫 := (⟨univ,M.E,IdealWeightPowers.unitIdeal (n+1) _,1⟩ : MarkedIdeal (n+1) _))
      rfl (head T r)
  obtain ⟨_, hTr⟩ := hHead.geometry (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans
  have hLE : L.E = boundary M.E (head T r) := (companionAlong_E _ _ _ _ _ _).trans hEN
  have hLN : L.N ⊆ P :=
    (companionAlong_N _ _ _ _ _ _).symm ▸ Lift.current_carrier_subset hHead M hSupport
  have hLK : K = MarkedIdeal.pullback (Subtype.val : W → _) L :=
    compAt_eq_pullback (Nat.succ_pos n) o (head T r) hA
  have hKDom := isInvDomain_compAt (Nat.succ_pos n) ho (head T r) hA
  have hKMax := isMaximalOrderAlong_compAt (Nat.succ_pos n) o (head T r) hA
  obtain ⟨hSc, hS, S, hOpen, hOpenIso⟩ := exists_open_lift hTail W
  have hKE : K.E = (boundary M.E (head T r)).map ((Subtype.val : W → _) ⁻¹' ·) := by
    rw [hLK]
    exact congrArg (fun E => E.map ((Subtype.val : W → _) ⁻¹' ·)) hLE
  have hKN : K.N ⊆ openSection P W := by
    rw [hLK]
    exact preimage_mono hLN
  have hKTrans : IsTransverse (n+1) (openSection P W) K.E := by
    rw [hKE]
    exact isTransverse_preimage (pullsBackCoordinates_val W) hTr
  let β := windowEquiv (Nat.le_succ n) P hP hPc W
  let KS := nativePullback (Nat.le_succ n) (openSection P W) (openSection_regular hP W) K
  have hKS : KS = MarkedIdeal.pullback β BF := by
    rw [show KS = nativePullback (Nat.le_succ n) (openSection P W) (openSection_regular hP W) K from rfl, hLK]
    have h := native_open_initial_record (Nat.le_succ n) P hPc hP W L hL.isWellFormed.isCoherent
    rw [hNativeComp] at h
    exact h
  have hBFMax : IsMaximalOrderAlong BF.N BF.ideal BF.d := by
    have h := (StepOneTowerIso.hypotheses_pullback α.symm J hJDom.isWellFormed
      hJDom.one_le_d hJMax hJDom.dimLE).2.2.1
    rw [hInvRec] at h
    exact h
  have hSCan : IsCanonical KS (f KS) S := by
    rw [hKS]
    exact hF.isCanonical_of_isTowerIso hBF hBFMax β hOpenIso hBFCan
  have hOpen' := hKE.symm ▸ hOpen
  have hCompare := Lift.original_step_one_with_depth (Nat.succ_pos n) hn a K hKDom
    hKN hKTrans hKMax hOpen'
  have hKCan := hCompare.1.mp hSCan
  refine ⟨hKCan, ?_⟩
  intro V0 J0
  let δ := diffeoOpens H.back (openPreimage (tail H.tower r) V) (openPreimage Nt F)
    (isTowerIso_mem_openPreimage_iff hTailIso hMatch)
  let γ := (endpointEquiv hTail W).trans δ.symm
  let γ₀ := β.trans α.symm
  have hγIso : IsTowerIso γ₀ S (restrict V (tail H.tower r)) γ :=
    hOpenIso.trans hMaskIso.symm
  have hKSRec : KS = MarkedIdeal.pullback γ₀ J := by
    rw [hKS, ← hInvRec]
    exact (HironakaSmoothSubmersionOrderedChoiceImageTrace.whole_markedPullback_comp
      α.symm.contMDiff β.contMDiff J hJDom.isWellFormed.isCoherent).symm
  let i : openPreimage (tail H.tower r) V → openPreimage (tail T r) W :=
    fun p => (γ.symm p).val
  refine ⟨i, ?_, ?_⟩
  · intro p
    have h := endpointEquiv_val_native hTail W (γ.symm p)
    change (endpointEquiv hTail W (γ.symm p)).val.val = (i p).val at h
    have hComp' : endpointEquiv hTail W (γ.symm p) = δ p := by
      have hγ := γ.apply_symm_apply p
      change δ.symm (endpointEquiv hTail W (γ.symm p)) = p at hγ
      exact δ.symm.injective (hγ.trans (δ.symm_apply_apply p).symm)
    rw [hComp'] at h
    exact h.symm
  · intro p hp
    let x := γ.symm p
    have hx : γ x = p := γ.apply_symm_apply p
    have hJTest := hF.isGeoTestTower_of_isCanonical hJDom hJMax _ hJCan
    have hNativeCos := IsTowerIso.cosupp_geoTransformAlong γ₀
      hJDom.isWellFormed.isClosedSubmanifold_N hJDom.isWellFormed.isCoherent hγIso hJTest
    rw [←hKSRec] at hNativeCos
    have hxCos : x ∈ (geoTransformAlong KS S).cosupp := by
      rw [hNativeCos]
      exact (show γ x ∈ (geoTransformAlong J (restrict V (tail H.tower r))).cosupp from
        hx.symm ▸ hp)
    have hKC := Lift.current_cosupport hOpen' (Nat.succ_pos n) hKDom.isWellFormed.isSNCDivisor
      hKTrans K rfl hKN (fun _ _ ht => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hKDom.isWellFormed.isCoherent ht)
    change (geoTransformAlong KS S).cosupp = Subtype.val ⁻¹' (geoTransformAlong K (restrict W (tail T r))).cosupp at hKC
    have hiCos : i p ∈ (geoTransformAlong K (restrict W (tail T r))).cosupp :=
      (Set.ext_iff.mp hKC x).mp hxCos
    have hpγ : γ x ∈ (geoTransformAlong J (restrict V (tail H.tower r))).cosupp := hx.symm ▸ hp
    have hV := hF.towerIso γ₀ J hJDom hJMax S (restrict V (tail H.tower r))
      γ hγIso hJCan x hpγ
    rw [← hKSRec, hx] at hV
    refine ⟨hiCos, ?_⟩
    have hAValue := hCompare.2 hKCan x hiCos
    have hDim : n+1-n = 1 := by omega
    rw [hDim] at hAValue
    exact hAValue.trans (congrArg (stepDimensionMap (depthPadMap a q ∘ sameIndexMap 1 q)) hV)

end
end Hironaka.HironakaG1NormalCompanionValue
