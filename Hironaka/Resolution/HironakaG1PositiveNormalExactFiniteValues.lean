import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaActualNativePositiveHistories
import Hironaka.Resolution.HironakaG1PositiveNormalAlignedTail

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1PositiveNormalExactFiniteValues
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres NormalCrossings HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionContactChoices
  HironakaActualNativePositiveHistories HironakaActualNativeRecursiveValues
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaG1SupportedStepOne
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperNormalPhaseNative HironakaG1PositiveNormalRestartCarrier
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaActualSectionBoundaryGeometry RelativePrincipalizationSpan HironakaG8LocalHistory

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Literal supported and native lower states and their finite Step One values. -/
abbrev PositiveFiniteValues
    {n k q s : ℕ} {X : CMfd.{0} n} {hk : k ≤ n}
    (hn : 0 < n) (hkpos : 0 < k)
    {W : Set X} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    (M : MarkedIdeal n X)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) {V : Set Y}
    {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
    (Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV))
    (z : nativeManifold hk V hV) : Prop :=
    let B := nativePullback hk W hW M
    let r := regimeRun (stepRegime M (s + 1)) T z.val
    let rB := regimeRun (stepRegime B (s + 1)) Q z
    let H := head T r
    let S := tail T r
    let HB := head Q rB
    let SB := tail Q rB
    let p := S.proj z.val
    let pB := SB.proj z
    let O := maskA M H p
    let OB := maskA B HB pB
    let L := lowerMarkedM M (s + 1) H p
    let LB := lowerMarkedM B (s + 1) HB pB
    rB = r ∧
    IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B) Q ∧
    ∃ (w : openPreimage S O) (wB : openPreimage SB OB),
      w.val = z.val ∧ wB.val = z ∧
      IsInvDomain q L ∧ IsInvDomain q LB ∧
      IsCanonical L ((invFamily hn q).inv L) (restrict O S) ∧
      IsCanonical LB ((invFamily hkpos q).inv LB) (restrict OB SB) ∧
      w ∈ (geoTransformAlong L (restrict O S)).cosupp ∧
      wB ∈ (geoTransformAlong LB (restrict OB SB)).cosupp ∧
      let v := (invFamily hn q).inv L (restrict O S) w
      let vB := (invFamily hkpos q).inv LB (restrict OB SB) wB
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M T z.val =
        toLex (s + 1, (v : WithTop (ValTy q))) ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B Q z =
        toLex (s + 1, (vB : WithTop (ValTy q))) ∧
      v = sameIndexMap (n - k) q vB

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
/-- A supported canonical Step One history yields both literal positive
lower canonical tails and the finite value on each tail. The map relates
the supported and native values at the same recursive bound. -/
theorem original_positive_lower_finite_values
    {n k q s : ℕ} {X : CMfd.{0} n} {hk : k ≤ n}
    (hn : 0 < n) (hkpos : 0 < k)
    {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hMax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M) T)
    (z : nativeManifold hk V hV)
    (hz : z.val ∈ (geoTransformAlong M T).cosupp)
    (hLevel : level M T z.val = s + 1)
    (hNS : ¬ IsSpecial M T z.val) :
    PositiveFiniteValues (q := q) (s := s) hn hkpos M T Q z := by
  let B := nativePullback hk W hW M
  let R := invFamily hn q
  let RB := invFamily hkpos q
  have hB : IsInvDomain (q + 1) B :=
    isInvDomain_nativePullback hn hk hW M hM hMN hTrans
  obtain ⟨_, _, hMaxB, _⟩ := native_source_geometry hk hW M hMN
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hMax
  obtain ⟨hBCan, hValues⟩ := HironakaG1SupportedStepOne.Lift.original_same_bound_step_one_values
    hn hkpos M hM hMN hTrans hMax h hCan
  have hChron := original_step_one_chronology M hM.isWellFormed hMN hTrans h hn
  have hClock := (hChron.2.2.2.2 (s + 1) z).symm
  have hLevelB : level B Q z = s + 1 := (hChron.2.2.1 z).1.symm.trans hLevel
  have hNSB : ¬ IsSpecial B Q z := fun h => hNS ((hChron.2.2.1 z).2.mpr h)
  obtain ⟨_, _, hCosM⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical R M hM hMax hn T hCan
  obtain ⟨_, _, hCosB⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical RB B hB hMaxB hkpos Q hBCan
  have hzB : z ∈ (geoTransformAlong B Q).cosupp := by
    rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor
      hTrans M rfl hMN (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)]
    exact hz
  have hData := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical (k := q + 1) M R
    hM.isWellFormed hM.one_le_d hn hMax hM.dimLE T
      ((Seq.StepOneBridge.isCanonical_iff R M hM hMax hn T).mp hCan)
      z.val (hCosM.symm ▸ hz) hNS
  have hDataB := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical (k := q + 1) B RB
    hB.isWellFormed hB.one_le_d hkpos hMaxB hB.dimLE Q
      ((Seq.StepOneBridge.isCanonical_iff RB B hB hMaxB hkpos Q).mp hBCan)
      z (hCosB.symm ▸ hzB) hNSB
  rw [hLevel] at hData
  rw [hLevelB] at hDataB
  obtain ⟨hp, hL, hLCan, hw⟩ := hData
  obtain ⟨hpB, hLB, hLBCan, hwB⟩ := hDataB
  refine ⟨hClock, hBCan, ⟨z.val, hp⟩, ⟨z, hpB⟩, rfl, rfl, hL, hLB, hLCan, hLBCan, hw, hwB, ?_⟩
  have hv := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R M (lowerMarkedM M) T hNS
  have hvB := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial RB B (lowerMarkedM B) Q hNSB
  rw [hLevel, Seq.StepOneValueMasked.lowerValueL_eq_of_mem R M (lowerMarkedM M) hp] at hv
  rw [hLevelB, Seq.StepOneValueMasked.lowerValueL_eq_of_mem RB B (lowerMarkedM B) hpB] at hvB
  refine ⟨hv, hvB, ?_⟩
  have hVal := hValues z hz
  change Seq.StepOneValueMasked.stepOneInvL R M (lowerMarkedM M) T z.val =
    stepDimensionMap (sameIndexMap (n - k) q)
      (Seq.StepOneValueMasked.stepOneInvL RB B (lowerMarkedM B) Q z) at hVal
  rw [hv, hvB] at hVal
  have hCoe := congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (ofLex v).2) hVal
  simp only [stepDimensionMap, ofLex_toLex, WithTop.map_coe, WithTop.coe_inj] at hCoe
  exact hCoe

private theorem zeroPlane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Canonicality for the section-supported original Step One history
gives the exact native finite branch on an actual lift. At a positive
section-nonspecial endpoint the padded and section run indices also agree. -/
theorem positive_normal_section_exact_finite_values {n q s : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q + 1) Q)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp)
    (hLevel : level (sectionMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let M := sectionMarked Q
    let P := properNormalMarked Q
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV))
      (z : nativeManifold (Nat.le_succ n) V hV),
      Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U) M.E T V hVc hV N ∧
      z.val = y ∧
      regimeRun (stepRegime M (s + 1)) T y = regimeRun (stepRegime P (s + 1)) T y ∧
      PositiveFiniteValues (q := q) (s := s) (Nat.succ_pos n) hn M T N z := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let M := sectionMarked Q
  let P := properNormalMarked Q
  have hM : IsInvDomain (q + 1) M := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hSupport : M.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) M.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hTestM := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) q) M hM hMax (Nat.succ_pos n) T hCan).2.1
  have hClass := properNormalMarked_locWPEquiv_section Q hQ
  have hTestP := (hClass.wEquiv.2 T).1.mpr hTestM
  have hyP : y ∈ (geoTransformAlong P T).cosupp := (hClass.wEquiv.2 T).2 hTestP ▸ hy
  have hLevelP := (HironakaG8MemberLoci.level_eq_of_E_eq (show P.E = M.E from rfl) T y).trans hLevel
  have hClock := positive_normal_section_run_eq_of_nonspecial Q hQ T hTestP y hyP hLevelP hNS
  obtain ⟨V, hVc, hV, N, hLift, _, _, _, _, _, _⟩ := exists_upper_native_test_history Q hQ T hTestP
  have hyV : y ∈ V := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift M hSupport
    ((geoTransformAlong M T).cosupp_subset_N hy)
  let z : nativeManifold (Nat.le_succ n) V hV := ⟨y, hyV⟩
  exact ⟨V, hVc, hV, N, z, hLift, rfl, hClock,
    original_positive_lower_finite_values (n := n + 1) (k := n) (q := q) (s := s) (X := X)
      (hk := Nat.le_succ n) (Nat.succ_pos n) hn (W := zeroPlane U) (hW := zeroPlane_regular U)
      M hM hSupport hTrans hMax (T := T) (V := V) (hV := hV) (Q := N) hLift hCan z hy hLevel hNS⟩

end
end Hironaka.HironakaG1PositiveNormalExactFiniteValues
