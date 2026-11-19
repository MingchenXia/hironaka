import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaG1RefreshedNativeZeroLift

/-! A native canonical lower tail at the literal section zero phase. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set TopologicalSpace

namespace Hironaka.HironakaG1NativeSectionEvaluator

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  NormalCrossings NormalCrossingsInvariance SubmanifoldChartedSpace MarkedIdealBiholomorphism
  HomogenizedGlueingTower HomogenizedIdealAlong CoefficientIdealRestriction MemberInterTowerAlong
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperNormalPhaseNative
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeHistoryExistence
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionOrderHistory
  HironakaDisjointNativeOpenLift HironakaActualSectionBoundaryDimension
  HironakaActualSectionBoundaryGeometry HironakaG1RefreshedNativeZeroLift
  HironakaG8MemberLoci InvDomainTowerAlong HironakaG1RecursiveMemberValueTransport

noncomputable section

private theorem zero_section_selected_geometry {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)}
    (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) :
    let Sec := sectionMarked Q
    let O := maskB Sec H p
    let A := CMfd.of (n := n+1) O
    let P := lowerMarkedM Sec 0 H p
    ∃ (W : Set A) (_hWc : IsClosed W) (_hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
      W = (Subtype.val : O → Y) ⁻¹' strictAlong H (zeroPlane U) ∧
      P.N ⊆ W ∧ IsTransverse (n+1) W P.E := by
  intro Sec O A P
  let X := CMfd.of (n := n+1) (productOpen U)
  obtain ⟨V,hVc,hV,_,hLift,_,_,_,hTrans,_,_⟩ := exists_upper_native_test_history Q hQ H hH
  let W : Set A := openSection V O
  have hWc : IsClosed W := hVc.preimage continuous_subtype_val
  have hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n := openSection_regular hV O
  have hEq : W = (Subtype.val : O → Y) ⁻¹' strictAlong H (zeroPlane U) :=
    congrArg (fun S : Set Y => (Subtype.val : O → Y) ⁻¹' S) hLift.carrier
  have hSub : Sec.N ∩ {x | (tangentChoice Sec (H.proj p)).2 x = 0} ⊆ zeroPlane U :=
    fun _ hz => ⟨mem_univ _,hz.1.2⟩
  have hPN : P.N ⊆ W := fun x hx => hEq.symm ▸ strictAlong_mono H hSub hx
  have hE : (geoTransformAlong (barMarked (X := X) Sec) H).E =
      (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked (X := X) Sec)
      (𝔫 := sectionBarCoefficient Q) rfl H
  have hTr : IsTransverse (n+1) W P.E := by
    change IsTransverse (n+1) ((Subtype.val : O → Y) ⁻¹' V)
      ((geoTransformAlong (barMarked Sec) H).E.map ((Subtype.val : O → Y) ⁻¹' ·))
    rw [hE]
    exact isTransverse_preimage (pullsBackCoordinates_val O) hTrans
  exact ⟨W,hWc,hW,hEq,hPN,hTr⟩

/-- The actual own zero contact on the literal section has a native
canonical lower tail with its full ordered kept boundary and exact read. -/
theorem native_section_zero_evaluator {n k : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp)
    (hZero : level (sectionMarked Q) T y = 0) (hNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let Sec := sectionMarked Q
    let j := regimeRun (stepRegime Sec 0) T y
    let H := head T j
    let S := tail T j
    let p := S.proj y
    let O := maskB Sec H p
    let A := CMfd.of (n := n+1) O
    let D := CMfd.of (n := n+1) (openPreimage S O)
    let P := lowerMarkedM Sec 0 H p
    let G := restrict O S
    ∃ (hp : p ∈ O) (W : Set A) (hWc : IsClosed W)
      (hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
      W = (Subtype.val : O → _) ⁻¹' strictAlong H (zeroPlane U) ∧
      ∃ (V : Set D) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n+1) V z n)
        (N : BlowupTower (nativeManifold (Nat.le_succ n) W hW)
          (nativeManifold (Nat.le_succ n) V hV)),
        Lift (Nat.le_succ n) W hWc hW P.E G V hVc hV N ∧
        let PN := nativePullback (Nat.le_succ n) W hW P
        IsInvDomain k PN ∧ IsCanonical PN ((invFamily hn k).inv PN) N ∧
          IsGeoTestTower PN N ∧ N.length = G.length ∧
          geoTransformAlong PN N = nativePullback (Nat.le_succ n) V hV (geoTransformAlong P G) ∧
          ∃ z : nativeManifold (Nat.le_succ n) V hV,
            z.val = (⟨y,hp⟩ : openPreimage S O) ∧ z ∈ (geoTransformAlong PN N).cosupp ∧
            Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) Sec T y =
              toLex (0,(sameIndexMap 1 k ((invFamily hn k).inv PN N z) : WithTop (ValTy k))) := by
  intro Sec j H S p O A D P G
  let I := invFamily (Nat.succ_pos n) k
  have hSec := section_projected_domain (k+1) Q.N Q.E Q.ideal Q.d hQ
  have hB := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) I Sec
    hSec hMax (Nat.succ_pos n) T hCan
  have hBarCan := (Seq.StepOneBridge.isCanonical_iff I Sec hSec hMax (Nat.succ_pos n) T).mp hCan
  have hBarCos : y ∈ (geoTransformAlong (barMarked Sec) T).cosupp := hB.2.2.symm ▸ hy
  have hH := ((isGeoTestTower_iff_head_tail Sec T j).mp hB.2.1).1
  have hPH := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mpr hH
  have hLower := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical
    (k := k+1) Sec I hSec.isWellFormed hSec.one_le_d (Nat.succ_pos n) hMax hSec.dimLE
    T hB.1 hBarCan y hBarCos hNS
  rw [hZero] at hLower
  obtain ⟨hp,hDom,hLowerCan,hEnd⟩ := hLower
  obtain ⟨W,hWc,hW,hEq,hSub,hTrans⟩ := zero_section_selected_geometry Q hQ H hPH p
  obtain ⟨V,hVc,hV,N,hLift,hNativeDom,hNativeCan,hNativeTest,hLen,hWhole,z,hz,hzEnd,hVal⟩ :=
    native_supported_canonical_read (r := k) (Nat.succ_pos n) hn (Nat.le_succ n) W hWc hW P hDom
      hSub hTrans G hLowerCan ⟨y,hp⟩ hEnd
  refine ⟨hp,W,hWc,hW,hEq,V,hVc,hV,N,hLift,hNativeDom,hNativeCan,hNativeTest,hLen,hWhole,z,hz,hzEnd,?_⟩
  have hRead : Seq.StepOneValueMasked.stepOneInvM I Sec T y =
      toLex (0,((I.inv P G (⟨y,hp⟩ : openPreimage S O) : ValTy k) : WithTop (ValTy k))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hNS,hZero]
    unfold Seq.StepOneValueMasked.lowerValueL
    rw [dif_pos hp]
    rfl
  have hDim : (n+1)-n = 1 := by omega
  rw [hDim] at hVal
  exact hRead.trans (congrArg (fun v : ValTy k => toLex (0,(v : WithTop (ValTy k)))) hVal)

#print axioms native_section_zero_evaluator

end
end Hironaka.HironakaG1NativeSectionEvaluator
