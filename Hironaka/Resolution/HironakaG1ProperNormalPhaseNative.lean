import Hironaka.Resolution.HironakaG1ProperNormalNativeHistory
import Hironaka.Resolution.HironakaG1ProperNormalZeroPhase

/-! Actual upper tests internally produce whole geometric native histories;
actual zero phases then produce native ORIGINAL canonical lower tails.
Blueprint FIRST: hironaka-g1-proper-normal-phase-native.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperNormalPhaseNative
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalLowerCanonical
  HironakaG1ProperNormalNativeHistory HironakaG1ProperNormalZeroPhase
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeHistoryExistence HironakaActualNativeInvariantDomain
  HironakaActualNativeSectionOrderHistory HironakaOriginalFamilyDepthStability
  HironakaDisjointNativeOpenLift HironakaActualRelativeNormalGeometry
  GermIdealPullbackCalculus HironakaG8HomStable HironakaG8CoefficientBoundaryLocal
  HironakaG8LocalHistory HironakaG11InvBMClass RelativePrincipalizationSpan
  NormalCrossings NormalCrossingsInvariance SubmanifoldChartedSpace StepOneValue
  StepOneValueMasked StepOneRegime ContactStageKept HomogenizedGlueingTower
  CoefficientIdealRestriction

private theorem plane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

/-- Ordinary upper TEST, without any lower/native CAN or supplied Lift,
constructs the SAME actual whole native geometric/test history. -/
theorem exists_upper_native_test_history {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    ∃(C : Set Y)(hCc : IsClosed C)(hC : ∀y∈C,RegularAtDim (n := n+1) C y n)
      (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) C hC)),
      Lift (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U)
        (sectionBarCoefficient Q).E T C hCc hC N ∧
      IsGeoTestTower (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionBarCoefficient Q)) N ∧
      N.length=T.length ∧ (∀z,T.proj z.val=(N.proj z).val) ∧
      IsTransverse (n+1) C (geoTransformAlong (sectionBarCoefficient Q) T).E ∧
      geoTransformAlong (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionBarCoefficient Q)) N=
        nativePullback (Y := Y) (Nat.le_succ n) C hC (geoTransformAlong (sectionBarCoefficient Q) T) ∧
      MarkedIdeal.pullback (nativeZeroSectionEquiv U)
        (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionBarCoefficient Q))=
        coeffMarkedAlong (barMarked (X := CMfd.of (n := n) U) Q) := by
  let S:=sectionMarked Q
  let V:=sectionBarCoefficient Q
  have hS : IsInvDomain k S:=section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hBS:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X := CMfd.of (n := n+1) (productOpen U)) S hS
  have hPV : LocWPEquiv (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) V :=
    (properNormalMarked_locWPEquiv_section Q hQ).trans
      ((bar_local_any_boundary (X := CMfd.of (n := n+1) (productOpen U)) S hS).trans
        (coefficient_local_any_boundary (X := CMfd.of (n := n+1) (productOpen U)) _ hBS))
  have hVT:= (hPV.wEquiv.2 T).1.mp hT
  have hV:= (kept_normal_lower_data Q hQ).2.1
  have hSupport : V.N⊆zeroPlane U:=fun _ hz=>⟨mem_univ _,hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) V.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  obtain ⟨C,hCc,hC,N,hLift,hNativeTest⟩:=exists_native_history_of_original_test
    (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U)
    V hV hSupport hTrans T hVT
  have hGeom:=hLift.geometry (Nat.succ_pos n) hV.isWellFormed.isSNCDivisor hTrans
  have hE : (geoTransformAlong V T).E=boundary V.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := V)
      (𝔫 := (⟨univ,V.E,IdealWeightPowers.unitIdeal (n+1) (productOpen U),1⟩ :
        MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)))) rfl T
  have hhol : ∀x f,V.ideal.mem x f → HolomorphicAt (n+1) f x:=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hV.isWellFormed.isCoherent hf
  exact ⟨C,hCc,hC,N,hLift,hNativeTest,hLift.length,hLift.square,hE ▸ hGeom.2,
    hLift.whole_records (Nat.succ_pos n) hV.isWellFormed.isSNCDivisor hTrans V rfl hSupport hhol,
    native_input_record Q hQ⟩

/-- The native support and genuine SAME-tail native CAN are INTERNALLY
constructed at the ACTUAL original zero-phase head, never supplied. -/
theorem exists_original_normal_phase_native_history {n k : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0<n) (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (properNormalMarked Q)) T)
    (y : Y) (hy : y∈(geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y=0) (hNS : ¬IsSpecial (properNormalMarked Q) T y) :
    let P:=properNormalMarked Q
    let r:=regimeRun (stepRegime P 0) T y
    let H:=head T r
    let S:=tail T r
    let p:=S.proj y
    let O:=maskB P H p
    let B:=contactMarkedKept P (relativeNormalCoordinate U) H O
    ∃(W : Set (CMfd.of (n := n+1) O))(hWc : IsClosed W)
      (hW : ∀x∈W,RegularAtDim (n := n+1) W x n),
      B.N⊆W ∧ IsTransverse (n+1) W B.E ∧
      ∃(C : Set (CMfd.of (n := n+1) (openPreimage S O)))(hCc : IsClosed C)
        (hC : ∀z∈C,RegularAtDim (n := n+1) C z n)
        (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n+1) O) (Nat.le_succ n) W hW)
          (nativeManifold (Y := CMfd.of (n := n+1) (openPreimage S O)) (Nat.le_succ n) C hC)),
        Lift (Nat.le_succ n) W hWc hW B.E (restrict O S) C hCc hC N ∧
        let NB:=nativePullback (Y := CMfd.of (n := n+1) O) (Nat.le_succ n) W hW B
        IsInvDomain k NB ∧ IsCanonical NB ((invFamily hn k).inv NB) N ∧ IsGeoTestTower NB N ∧
          N.length=(restrict O S).length ∧ (∀z,(restrict O S).proj z.val=(N.proj z).val) ∧
          geoTransformAlong NB N=nativePullback (Y := CMfd.of (n := n+1) (openPreimage S O))
            (Nat.le_succ n) C hC (geoTransformAlong B (restrict O S)) ∧
          (geoTransformAlong NB N).cosupp=(Subtype.val : C → openPreimage S O) ⁻¹'
            (geoTransformAlong B (restrict O S)).cosupp ∧
          (Subtype.val : C → openPreimage S O) '' (geoTransformAlong NB N).cosupp=
            (geoTransformAlong B (restrict O S)).cosupp ∧
          (∀z : nativeManifold (Y := CMfd.of (n := n+1) (openPreimage S O)) (Nat.le_succ n) C hC,
            z.val∈(geoTransformAlong B (restrict O S)).cosupp →
            (invFamily (Nat.succ_pos n) k).inv B (restrict O S) z.val=
              HironakaActualSectionBoundaryDimension.sameIndexMap 1 k ((invFamily hn k).inv NB N z)) := by
  let P:=properNormalMarked Q
  let r:=regimeRun (stepRegime P 0) T y
  let H:=head T r
  let S:=tail T r
  let p:=S.proj y
  let O:=maskB P H p
  let B:=contactMarkedKept P (relativeNormalCoordinate U) H O
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hMax:=properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest:=(StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1)
    (invFamily (Nat.succ_pos n) k) (Nat.succ_pos n)).isGeoTestTower_of_isCanonical hP hMax T hCan
  have hHeadTest:=((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨V,hVc,hV,NH,hHeadLift,_hNativeHeadTest,_hHeadLength,_hHeadSquare,hHeadTrans,_hHeadWhole,_hInput⟩:=
    exists_upper_native_test_history Q hQ H hHeadTest
  obtain ⟨_hp,_hOwn,hB,_hL,_hDim,_hI,_hE,_hd,_hExp,_hOwnCan,hCanB,_hEndpoint,_hValues⟩:=
    original_normal_zero_phase Q hQ T hCan y hy hLevel hNS
  let W : Set (CMfd.of (n := n+1) O):=openSection V O
  have hWc : IsClosed W:=hVc.preimage continuous_subtype_val
  have hW : ∀x∈W,RegularAtDim (n := n+1) W x n:=openSection_regular hV O
  have hInitialSupport : P.N∩{z | relativeNormalCoordinate U z=0}⊆zeroPlane U := by
    intro z hz
    refine ⟨mem_univ _,?_⟩
    ext i
    have hi : i=(0 : Fin 1):=Fin.eq_zero i
    subst i
    simpa [relativeNormalCoordinate,HironakaActualZeroCoordinateContactSeed.addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction,HironakaActualZeroCoordinateContactSeed.zeroFunction] using hz.2
  have hStrictSupport:=MemberInterTowerAlong.strictAlong_mono H hInitialSupport
  rw [←hHeadLift.carrier] at hStrictSupport
  have hBN : B.N⊆W:=fun _ hz=>hStrictSupport hz
  have hBarE : (geoTransformAlong (barMarked P) H).E=(geoTransformAlong (sectionBarCoefficient Q) H).E:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked (X := CMfd.of (n := n+1) (productOpen U)) P) (𝔫 := sectionBarCoefficient Q) rfl H
  have hTransB : IsTransverse (n+1) W B.E := by
    change IsTransverse (n+1) ((Subtype.val : O→(split T r).1) ⁻¹' V)
      ((geoTransformAlong (barMarked P) H).E.map ((Subtype.val : O→(split T r).1) ⁻¹' ·))
    rw [hBarE]
    exact isTransverse_preimage (pullsBackCoordinates_val O) hHeadTrans
  have hBTest:=(invFamily (Nat.succ_pos n) k).isInvValue.isGeoTestTower_of_isCanonical
    (X := CMfd.of (n := n+1) O) hB (restrict O S) hCanB
  obtain ⟨C,hCc,hC,N,hLift,hNativeTest⟩:=exists_native_history_of_original_test
    (X := CMfd.of (n := n+1) O) (Nat.succ_pos n) (Nat.le_succ n) W hWc hW B hB hBN hTransB
    (restrict O S) hBTest
  let NB:=nativePullback (Y := CMfd.of (n := n+1) O) (Nat.le_succ n) W hW B
  have hNB : IsInvDomain k NB:=isInvDomain_nativePullback (X := CMfd.of (n := n+1) O)
    (W := W) (Nat.succ_pos n) (Nat.le_succ n) hW B hB hBN hTransB
  have hNative:=HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (n := n+1) (k := n) (q := k) (X := CMfd.of (n := n+1) O)
    (hk := Nat.le_succ n) (W := W) (hWc := hWc) (hW := hW)
    (T := restrict O S) (V := C) (hVc := hCc) (hV := hC) (Q := N)
    (Nat.succ_pos n) hn B hB hBN hTransB hLift hCanB
  have hhol : ∀x f,B.ideal.mem x f→HolomorphicAt (n+1) f x:=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hf
  have hWhole:=hLift.whole_records (Nat.succ_pos n) hB.isWellFormed.isSNCDivisor hTransB B rfl hBN hhol
  have hCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift (Nat.succ_pos n)
    hB.isWellFormed.isSNCDivisor hTransB B rfl hBN hhol
  have hCurrentSupport : (geoTransformAlong B (restrict O S)).N⊆C :=
    HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset
      (X := CMfd.of (n := n+1) O) (Y := CMfd.of (n := n+1) (openPreimage S O))
      hLift B hBN
  have hImage : (Subtype.val : C → openPreimage S O) '' (geoTransformAlong NB N).cosupp=
      (geoTransformAlong B (restrict O S)).cosupp := by
    rw [hCos]
    apply Set.image_preimage_eq_iff.mpr
    intro z hz
    exact ⟨⟨z,hCurrentSupport hz.1⟩,rfl⟩
  refine ⟨W,hWc,hW,hBN,hTransB,C,hCc,hC,N,hLift,hNB,hNative.1,hNativeTest,hLift.length,
    hLift.square,hWhole,hCos,hImage,?_⟩
  intro z hz
  have hdim : (n+1)-n=1:=by omega
  simpa only [hdim] using hNative.2 z hz

end
end Hironaka.HironakaG1ProperNormalPhaseNative
