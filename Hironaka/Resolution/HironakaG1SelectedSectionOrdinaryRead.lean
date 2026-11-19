import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaG1LiteralSectionOrderEndpoint
import Hironaka.Resolution.HironakaG1NativePositivePhase

/-! A native canonical lower tail at the literal section zero phase. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set TopologicalSpace

namespace Hironaka.HironakaG1SelectedSectionOrdinaryRead

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
  HironakaActualSectionBoundaryGeometry HironakaG1NativePositivePhase
  HironakaG8MemberLoci InvDomainTowerAlong HironakaG1RecursiveMemberValueTransport HironakaG1LaterLiteralSectionCanonicalTail
  HironakaG1LaterSectionPairOrder HironakaG1OrdinaryNativeEvaluatorEndpoint
  HironakaG1NativeOrderDispatcher HironakaG1LiteralSectionOrderEndpoint
  RelativePrincipalizationSpan HironakaActualNativeSectionOriginalCuts
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  GeneralValue NonmonomialOrderLocal NonmonomialOrderRegime MonomialCaseAlong
  HironakaSmoothSubmersionCanonicalValueDimensionShift

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


/-- Both finite Step One leaves already carry the original-family canonical
history on the selected ambient record itself. This is the exact source
for a further ordinary recursion. -/
theorem actual_selected_section_ordinary_source {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp)
    (hNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let Sec := sectionMarked Q
    let l := level Sec T y
    let j := regimeRun (stepRegime Sec l) T y
    let H := head T j
    let S := tail T j
    let p := S.proj y
    ∃ (O : Opens (split T j).1) (hp : p ∈ O) (P : MarkedIdeal (n+1) O),
      ((l = 0 ∧ O = maskB Sec H p ∧ HEq P (lowerMarkedM Sec 0 H p)) ∨
       (0 < l ∧ P = positiveMemberOn Sec H p O)) ∧
      let G := restrict O S
      let z : openPreimage S O := ⟨y,hp⟩
      ∃ (W : Set (CMfd.of (n := n+1) O)) (_hWc : IsClosed W)
        (_hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
        W = (Subtype.val : O → _) ⁻¹' strictAlong H (zeroPlane U) ∧
        P.N ⊆ W ∧ IsTransverse (n+1) W P.E ∧
        IsInvDomain k P ∧ IsCanonical P ((invFamily (Nat.succ_pos n) k).inv P) G ∧
        z ∈ (geoTransformAlong P G).cosupp ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) Sec T y =
          toLex (l,((invFamily (Nat.succ_pos n) k).inv P G z : WithTop (ValTy k))) := by
  dsimp only
  cases hLevel : level (sectionMarked Q) T y with
  | zero =>
      let Sec := sectionMarked Q
      let I := invFamily (Nat.succ_pos n) k
      let j := regimeRun (stepRegime Sec 0) T y
      let H := head T j
      let S := tail T j
      let p := S.proj y
      let O := maskB Sec H p
      let P := lowerMarkedM Sec 0 H p
      let G := restrict O S
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
      rw [hLevel] at hLower
      obtain ⟨hp,hDom,hPcan,hEnd⟩ := hLower
      obtain ⟨W,hWc,hW,hEq,hSub,hTrans⟩ := zero_section_selected_geometry Q hQ H hPH p
      have hRead : Seq.StepOneValueMasked.stepOneInvM I Sec T y =
          toLex (0,((I.inv P G (⟨y,hp⟩ : openPreimage S O) : ValTy k) : WithTop (ValTy k))) := by
        unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
        rw [if_neg hNS,hLevel]
        unfold Seq.StepOneValueMasked.lowerValueL
        rw [dif_pos hp]
        rfl
      exact ⟨O,hp,P,Or.inl ⟨rfl,rfl,HEq.rfl⟩,W,hWc,hW,hEq,hSub,hTrans,hDom,hPcan,hEnd,hRead⟩
  | succ s =>
      let Sec := sectionMarked Q
      let I := invFamily (Nat.succ_pos n) k
      let j := regimeRun (stepRegime Sec (s+1)) T y
      let H := head T j
      let S := tail T j
      let p := S.proj y
      have hSec := section_projected_domain (k+1) Q.N Q.E Q.ideal Q.d hQ
      have hB := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) I Sec
        hSec hMax (Nat.succ_pos n) T hCan
      have hH := ((isGeoTestTower_iff_head_tail Sec T j).mp hB.2.1).1
      have hPH := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mpr hH
      obtain ⟨O,u,hp,_,hComp,hCanC,hCanS,hEndC,hRead⟩ :=
        later_literal_section_finite_read Q hQ T y hy hLevel hNS hMax hCan
      let P := positiveMemberOn Sec H p O
      let G := restrict O S
      let L := positiveMemberOn (properNormalMarked Q) H p O
      let C := withN (coeffMarkedAlong L) (L.N ∩ {z : O | u z.val = 0})
      have hTestC := I.isInvValue.isGeoTestTower_of_isCanonical hComp.contactDomain G hCanC
      have hEnd := ((hComp.localClass.wEquiv.2 G).2 hTestC) ▸ hEndC
      obtain ⟨W,hWc,hW,hEQ,hSub,hTrans⟩ := selected_section_supported_native_head Q hQ H hPH p O
      exact ⟨O,hp,P,Or.inr ⟨Nat.succ_pos _,rfl⟩,W,hWc,hW,hEQ,hSub,hTrans,
        hComp.sectionDomain,hCanS,hEnd,hRead⟩

/-- The literal section's finite branch feeds its actual selected lower record
and its own restricted tail into the ordinary original-family evaluator.
The same native Lift supplies the outer letter and both recursive order
branches, with the positive-order differential and coefficient dictionary. -/
theorem literal_section_recursive_native_dispatch {n q : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q+2) Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q+1)) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp) :
    let Sec := sectionMarked Q
    let l := level Sec T y
    let j := regimeRun (stepRegime Sec l) T y
    let H := head T j
    let S := tail T j
    let p := S.proj y
    let out := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q+1)) Sec T y
    (IsSpecial Sec T y ∧ out = toLex (l,(⊤ : WithTop (ValTy (q+1))))) ∨
    (¬ IsSpecial Sec T y ∧
      ∃ (O : Opens (split T j).1) (hp : p ∈ O) (P : MarkedIdeal (n+1) O),
        ((l = 0 ∧ O = maskB Sec H p ∧ HEq P (lowerMarkedM Sec 0 H p)) ∨
         (0 < l ∧ P = positiveMemberOn Sec H p O)) ∧
        let A := CMfd.of (n := n+1) O
        let B := CMfd.of (n := n+1) (openPreimage S O)
        let G := restrict O S
        let yO : openPreimage S O := ⟨y,hp⟩
        ∃ (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
          W = (Subtype.val : O → _) ⁻¹' strictAlong H (zeroPlane U) ∧
          ∃ (V : Set B) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n+1) V z n)
            (N : BlowupTower (nativeManifold (Nat.le_succ n) W hW)
              (nativeManifold (Nat.le_succ n) V hV)),
            Lift (Nat.le_succ n) W hWc hW P.E G V hVc hV N ∧
            let PN := nativePullback (Nat.le_succ n) W hW P
            let F := geoTransformAlong P G
            let FN := geoTransformAlong PN N
            IsInvDomain (q+1) P ∧ IsCanonical P ((invFamily (Nat.succ_pos n) (q+1)).inv P) G ∧
            IsInvDomain (q+1) PN ∧ IsCanonical PN ((invFamily hn (q+1)).inv PN) N ∧
            FN = nativePullback (Nat.le_succ n) V hV F ∧
            (IsGeoResolution P G → IsGeoResolution PN N) ∧
            ∃ z : nativeManifold (Nat.le_succ n) V hV,
              z.val = yO ∧ z ∈ FN.cosupp ∧
              let o := nmOrd F yO
              let v := (invFamily (Nat.succ_pos n) (q+1)).inv P G yO
              let w := (invFamily hn (q+1)).inv PN N z
              out = toLex (l,(sameIndexMap 1 (q+1) w : WithTop (ValTy (q+1)))) ∧
              o = nmOrd FN z ∧ v = sameIndexMap 1 (q+1) w ∧
              if o = 0 then
                v = monomialRead (q := q) F yO ∧ w = monomialRead (q := q) FN z ∧
                gammaAlong (n+1) F.N F.ideal F.E F.d yO =
                  dimensionValue 1 (gammaAlong n FN.N FN.ideal FN.E FN.d z)
              else
                ActualOrderHeadCoefficients hWc P G N z o ∧
                regimeRun (OrdRegime P o) G yO = regimeRun (OrdRegime PN o) N z ∧
                ∃ a b : ℕ ×ₗ WithTop (ValTy q),
                  v = positiveSuccessorRead o a ∧ w = positiveSuccessorRead o b ∧
                  PositiveOrderCompanionWitness (k := q) (Nat.succ_pos n) P G yO o
                    (fun t => t = positiveSuccessorRead o a) ∧
                  PositiveOrderCompanionWitness (k := q) hn PN N z o
                    (fun t => t = positiveSuccessorRead o b) ∧
                  a = stepDimensionMap (sameIndexMap 1 q) b ∧
                  (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤)) := by
  intro Sec l j H S p out
  by_cases hNS : ¬ IsSpecial Sec T y
  · apply Or.inr
    refine ⟨hNS,?_⟩
    obtain ⟨O,hp,P,hBranch,W,hWc,hW,hEq,hSub,hTrans,hP,hCanP,hEnd,hRead⟩ :=
      actual_selected_section_ordinary_source Q hQ T hMax hCan y hy hNS
    let G := restrict O S
    let yO : openPreimage S O := ⟨y,hp⟩
    obtain ⟨V,hVc,hV,N,hLift,hDom,hNCan,hRes,hCoefficients,hDispatch⟩ :=
      exists_ordinary_native_order_evaluator (hk := Nat.le_succ n) (hWc := hWc) (hW := hW)
        (Nat.succ_pos n) hn hP hSub hTrans hCanP
    have hCurrent := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift P hSub
    let z : nativeManifold (Nat.le_succ n) V hV := ⟨yO,hCurrent hEnd.1⟩
    have hz : z.val = yO := rfl
    obtain ⟨_,hWhole,_,hEndN,hOrd,hValue,hRecursive⟩ := hDispatch z hEnd
    have hDim : (n+1)-n = 1 := by omega
    rw [hDim] at hValue hRecursive
    refine ⟨O,hp,P,hBranch,W,hWc,hW,hEq,V,hVc,hV,N,hLift,
      hP,hCanP,hDom,hNCan,hWhole,hRes,z,hz,hEndN,?_,hOrd,hValue,?_⟩
    · exact hRead.trans (congrArg (fun w : ValTy (q+1) => toLex (l,(w : WithTop (ValTy (q+1))))) hValue)
    · dsimp only at hRecursive ⊢
      rw [hz] at hRecursive
      split_ifs with h0
      · rw [if_pos h0] at hRecursive
        exact hRecursive
      · rw [if_neg h0] at hRecursive
        exact ⟨hCoefficients z _ (Nat.pos_of_ne_zero h0),hRecursive⟩
  · have hs : IsSpecial Sec T y := not_not.mp hNS
    refine Or.inl ⟨hs,?_⟩
    unfold out Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hs]

/-- No finite leaf can survive at recursive depth zero. The originating
literal section therefore takes the actual special top branch. -/
theorem literal_section_depth_zero_dispatch {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain 1 Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) 0) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp) :
    IsSpecial (sectionMarked Q) T y ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) 0) (sectionMarked Q) T y =
        toLex (level (sectionMarked Q) T y,(⊤ : WithTop (ValTy 0))) := by
  have hs : IsSpecial (sectionMarked Q) T y := by
    by_contra hNS
    obtain ⟨O,hp,P,hBranch,W,hWc,hW,hEq,hSub,hTrans,hP,hCanP,hEnd,hRead⟩ :=
      actual_selected_section_ordinary_source Q hQ T hMax hCan y hy hNS
    let I := invFamily (Nat.succ_pos n) 0
    have hTest := I.isInvValue.isGeoTestTower_of_isCanonical hP _ hCanP
    have hEmpty := cosupp_eq_empty_of_dimLE_zero (isInvDomain_geoTransformAlong hP _ hTest)
    rw [hEmpty] at hEnd
    exact hEnd
  refine ⟨hs,?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hs]

#print axioms literal_section_depth_zero_dispatch
#print axioms literal_section_recursive_native_dispatch
#print axioms actual_selected_section_ordinary_source

end
end Hironaka.HironakaG1SelectedSectionOrdinaryRead
