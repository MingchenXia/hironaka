import Hironaka.Resolution.HironakaG1NativeOrderDispatcher
import Hironaka.Resolution.HironakaActualNativeSectionCoefficientRecords
import Hironaka.Resolution.HironakaActualNativeHistoryExistence

/-! # Actual native order dispatcher -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1OrdinaryNativeEvaluatorEndpoint
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  HomogenizedIdealAlong HomogenizedGlueingTower BoundaryCount MemberInterTowerAlong NormalCrossings SubmanifoldChartedSpace RelativePrincipalizationSpan
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionOriginalCuts HironakaActualNativeCompanionHistories
  HironakaActualNativeInvariantDomain HironakaOriginalFamilyDepthStability
  HironakaActualSectionBoundaryDimension HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime GeneralValue CompanionRebase

open HironakaG1ActualNativeCompanionPhase

section Lift

variable {n m q : ℕ} {X Y : CMfd.{0} n}
  {hk : m ≤ n} {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x m}
  {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n) V y m}
  {T : BlowupTower X Y}
  {N : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
  {M : MarkedIdeal n X}

open HironakaG1NativeCompanionBranchGeometry MonomialCaseAlong

open HironakaG1NativeOrderDispatcher HironakaActualNativeSectionCoefficientRecords
  HironakaActualNativeSectionDifferentialIdeals
  HironakaActualNativeHistoryExistence InvDomainCompanion InvDomainTowerAlong CompanionReductionAlong DerivativeIdealAlong

/-- Whole companion, coefficient, homogenized coefficient and tangential
differential records at the matched actual order head. -/
abbrev ActualOrderHeadCoefficients (hWc : IsClosed W) (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (N : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV))
    (z : nativeManifold hk V hV) (o : ℕ) : Prop :=
    let K := nativePullback hk W hW M
    let j := regimeRun (OrdRegime M o) T z.val
    j = regimeRun (OrdRegime K o) N z ∧
      ∃ (P : Set (split T j).1) (hPc : IsClosed P)
        (hP : ∀ x ∈ P, RegularAtDim (n := n) P x m)
        (e : (split N j).1 = nativeManifold hk P hP),
        Lift hk W hWc hW M.E (head T j) P hPc hP (recastTarget e (head N j)) ∧
        let A := companionOf n (geoTransformAlong M (head T j)) o
        let B := companionOf m (geoTransformAlong K (recastTarget e (head N j))) o
        nativePullback hk P hP A = B ∧
        nativePullback hk P hP (coeffMarkedAlong A) = coeffMarkedAlong B ∧
        nativePullback hk P hP (barMarked A) = barMarked B ∧
        (letI := chartedSpace hk hP
         let := isComplexManifold_chartedSpace hk hP
         ∀ l, GermIdeal.pullback (m := m) (Subtype.val : nativeManifold hk P hP → (split T j).1)
          (iterDerivIdealAlong A.N A.ideal l) = iterDerivIdealAlong B.N B.ideal l)

set_option maxHeartbeats 1500000 in
/-- The genuine companion at the shared actual order head transports as a
whole supported record. Its coefficient and homogenized coefficient records
and every tangential derivative ideal transport at their true marks. -/
theorem actual_order_head_companion_coefficients
    (hn : 0 < n) (hm : 0 < m)
    (h : Lift hk W hWc hW M.E T V hVc hV N)
    (hM : IsInvDomain (q+1) M) (hSupport : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hTest : IsGeoTestTower M T) (z : nativeManifold hk V hV) (o : ℕ) (ho : 0 < o) :
    ActualOrderHeadCoefficients hWc M T N z o := by
  unfold ActualOrderHeadCoefficients
  intro K j
  obtain ⟨hr,P,hPc,hP,e,hHead,_,hRec,_⟩ :=
    actual_order_head_companion_geometry hn hm h hM hSupport hTrans hTest z o
  have hHeadTest := ((isGeoTestTower_iff_head_tail M T j).mp hTest).1
  let MH := geoTransformAlong M (head T j)
  let A := companionOf n MH o
  have hDom := isInvDomain_geoTransformAlong hM (head T j) hHeadTest
  have hADom := isInvDomain_companionAlong hn hDom ho
  have hAS : A.N ⊆ P := by
    change (companionOf n MH o).N ⊆ P
    simp only [companionOf, companionAlong_N]
    exact Lift.current_carrier_subset hHead M hSupport
  have hHol : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hADom.isWellFormed.isCoherent hg
  have hCoeff := nativePullback_coeffMarkedAlong hk hP A hAS hHol
  have hBar := nativePullback_barMarked hk hP A hAS hHol
  rw [hRec o] at hCoeff hBar
  refine ⟨hr,P,hPc,hP,e,hHead,hRec o,hCoeff,hBar,?_⟩
  let := chartedSpace hk hP
  let := isComplexManifold_chartedSpace hk hP
  rw [← hRec o]
  intro l
  exact pullback_native_iterDerivIdealAlong hk hP A.N hAS A.ideal hHol l

set_option maxHeartbeats 2200000 in
/-- An ordinary ambient canonical tower with supported source and transverse
native carrier supplies one actual native history. That same history reads
every surviving endpoint, at both order-zero and positive order. An exhausted
ambient tower has an exhausted native history. -/
theorem exists_ordinary_native_order_evaluator
    (hn : 0 < n) (hm : 0 < m)
    (hM : IsInvDomain (q+1) M) (hSupport : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hCan : IsCanonical M ((invFamily hn (q+1)).inv M) T) :
    ∃ (V' : Set Y) (hV'c : IsClosed V') (hV' : ∀ y ∈ V', RegularAtDim (n := n) V' y m)
      (N' : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V' hV')),
      Lift hk W hWc hW M.E T V' hV'c hV' N' ∧
      IsInvDomain (q+1) (nativePullback hk W hW M) ∧
      IsCanonical (nativePullback hk W hW M)
        ((invFamily hm (q+1)).inv (nativePullback hk W hW M)) N' ∧
      (IsGeoResolution M T → IsGeoResolution (nativePullback hk W hW M) N') ∧
      (∀ (z : nativeManifold hk V' hV') (o : ℕ), 0 < o →
        ActualOrderHeadCoefficients hWc M T N' z o) ∧
      ∀ (z : nativeManifold hk V' hV'), z.val ∈ (geoTransformAlong M T).cosupp →
        let K := nativePullback hk W hW M
        let A := geoTransformAlong M T
        let B := geoTransformAlong K N'
        let o := nmOrd A z.val
        let v := (invFamily hn (q+1)).inv M T z.val
        let w := (invFamily hm (q+1)).inv K N' z
        IsInvDomain (q+1) K ∧ B = nativePullback hk V' hV' A ∧
        IsCanonical K ((invFamily hm (q+1)).inv K) N' ∧
        z ∈ B.cosupp ∧ o = nmOrd B z ∧ v = sameIndexMap (n-m) (q+1) w ∧
        if o = 0 then
          v = monomialRead (q := q) A z.val ∧ w = monomialRead (q := q) B z ∧
          gammaAlong n A.N A.ideal A.E A.d z.val =
            dimensionValue (n-m) (gammaAlong m B.N B.ideal B.E B.d z)
        else
          regimeRun (OrdRegime M o) T z.val = regimeRun (OrdRegime K o) N' z ∧
          ∃ a b : ℕ ×ₗ WithTop (ValTy q),
            v = positiveSuccessorRead o a ∧ w = positiveSuccessorRead o b ∧
            PositiveOrderCompanionWitness (k := q) hn M T z.val o (fun x => x = positiveSuccessorRead o a) ∧
            PositiveOrderCompanionWitness (k := q) hm K N' z o (fun x => x = positiveSuccessorRead o b) ∧
            a = stepDimensionMap (sameIndexMap (n-m) q) b ∧
            (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤) := by
  have hTest := (invFamily hn (q+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hCan
  obtain ⟨V',hV'c,hV',N',hLift,hNativeTest⟩ :=
    exists_native_history_of_original_test hn hk W hWc hW M hM hSupport hTrans T hTest
  have hNativeDomain := isInvDomain_nativePullback hn hk hW M hM hSupport hTrans
  have hNativeCan :=
    (HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
      hn hm M hM hSupport hTrans hLift hCan).1
  refine ⟨V',hV'c,hV',N',hLift,hNativeDomain,hNativeCan,?_,?_,?_⟩
  · intro hEnd
    refine ⟨hNativeTest,?_⟩
    rw [Lift.current_cosupport hLift hn hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg),
      hEnd.2, preimage_empty]
  · intro z o ho
    exact actual_order_head_companion_coefficients hn hm hLift hM hSupport hTrans hTest z o ho
  · intro z hz
    exact actual_native_order_dispatch hn hm hLift hM hSupport hTrans hCan z hz

end Lift
end
end Hironaka.HironakaG1OrdinaryNativeEvaluatorEndpoint
