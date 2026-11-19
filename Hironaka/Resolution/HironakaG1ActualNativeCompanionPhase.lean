import Hironaka.Resolution.HironakaG1NativePositivePhase
import Hironaka.Resolution.HironakaActualNativeCompanionHistories
import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts
import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead

/-! # Actual native order-companion reads on the same supported lift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1ActualNativeCompanionPhase
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

private theorem positive_read_injective {q : ℕ} (o : ℕ) :
    Function.Injective (positiveSuccessorRead (k := q) o) := by
  intro a b h
  exact WithTop.coe_inj.mp (Sum.inr.inj (congrArg (fun v : ValTy (q+1) => ofLex ((ofLex v).2)) h))

private theorem sameIndexMap_positive_read {q : ℕ} (t o : ℕ) (a : ℕ ×ₗ WithTop (ValTy q)) :
    sameIndexMap t (q+1) (positiveSuccessorRead o a) =
      positiveSuccessorRead o (stepDimensionMap (sameIndexMap t q) a) := rfl

private theorem realized_positive_read {n q : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (h : PositiveOrderCompanionWitness (k := q) hn M T y o
      (fun v => (invFamily hn (q+1)).inv M T y = v)) :
    ∃ v : ℕ ×ₗ WithTop (ValTy q),
      (invFamily hn (q+1)).inv M T y = positiveSuccessorRead o v ∧
      PositiveOrderCompanionWitness (k := q) hn M T y o
        (fun w => w = positiveSuccessorRead o v) := by
  obtain ⟨hp,hDom,hMax,hCan,hEnd,hVal⟩ := h
  let r := regimeRun (OrdRegime M o) T y
  let H := head T r
  let R := tail T r
  let O := ordMask (geoTransformAlong M H) o
  let J := compAt M o H
  let a : openPreimage R O := ⟨y,hp⟩
  let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) J (restrict O R) a
  exact ⟨v,hVal,hp,hDom,hMax,hCan,hEnd,rfl⟩

private theorem companion_letter_geometry {m q : ℕ} {A B : CMfd.{0} m}
    (hm : 0 < m) (J : MarkedIdeal m A) (R : BlowupTower A B) (w : B)
    (hJ : IsInvDomain (q + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hm q) J) R)
    (hw : w ∈ (geoTransformAlong J R).cosupp) (o : ℕ) (c : ℕ ×ₗ WithTop (ValTy q))
    (hVal : HironakaG1InitialPositiveGeneralRead.positiveSuccessorRead o
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hm q) J R w) =
        HironakaG1InitialPositiveGeneralRead.positiveSuccessorRead o c) :
    (ofLex c).1 = boundaryCount (J.E.map (strictAlong R)) w ∧
      ((ofLex c).2 = ⊤ ↔ IsSpecial J R w) := by
  let I := invFamily hm q
  let val := Seq.StepOneValueMasked.stepOneInvM I J R w
  have hComp : val = c := by
    have hc := congrArg (fun a : ValTy (q + 1) => ofLex ((ofLex a).2)) hVal
    have hc' : Sum.inr (val : WithTop (ℕ ×ₗ WithTop (ValTy q))) =
        Sum.inr (c : WithTop (ℕ ×ₗ WithTop (ValTy q))) := hc
    exact WithTop.coe_inj.mp (Sum.inr.inj hc')
  have hLevel : (ofLex val).1 = level J R w := by
    rw [show val = Seq.StepOneValueMasked.stepOneInvL I J (lowerMarkedM J) R w from rfl]
    exact Seq.StepOneValueMasked.stepOneInvL_fst I J (lowerMarkedM J) R w
  have hMembers : origMembers J R = J.E.map (strictAlong R) := by
    change (geoTransformAlong (barMarked J) R).E.take J.E.length = _
    exact take_E_geoTransformAlong (barMarked J) R
  have hBarTest := Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hm R hCan
  have hwBar : w ∈ (geoTransformAlong (barMarked J) R).cosupp := hBarTest.2.2.symm ▸ hw
  have hLeaf : (ofLex val).2 = ⊤ ↔ IsSpecial J R w := by
    change (ofLex (Seq.StepOneValueMasked.stepOneInvL I J (lowerMarkedM J) R w)).2 = ⊤ ↔ _
    by_cases hs : IsSpecial J R w
    · rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial I J (lowerMarkedM J) R hs]
      exact iff_of_true rfl hs
    · rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial I J (lowerMarkedM J) R hs]
      exact iff_of_false
        (Seq.StepOneValueMasked.lowerValueL_ne_top J I hJ.isWellFormed hJ.one_le_d hm
          hMax (lowerMarkedM J) R hBarTest.1 hwBar hs) hs
  rw [← hComp]
  exact ⟨hLevel.trans (by rw [level, hMembers]), hLeaf⟩

/-- A realized positive companion letter counts all incident retained slots of
its actual masked record, including slots born before the order head.
The top leaf is the literal special case on its restricted tail. -/
theorem positive_companion_witness_slot_count_and_special {n q : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (o : ℕ) (c : ℕ ×ₗ WithTop (ValTy q))
    (h : PositiveOrderCompanionWitness (k := q) hn M T y o
      (fun v => v = positiveSuccessorRead o c)) :
    let r := regimeRun (OrdRegime M o) T y
    let H := head T r
    let R := tail T r
    let O := ordMask (geoTransformAlong M H) o
    let J := compAt M o H
    ∃ hy : y ∈ openPreimage R O,
      let w : openPreimage R O := ⟨y,hy⟩
      (ofLex c).1 = boundaryCount (J.E.map (strictAlong (restrict O R))) w ∧
      ((ofLex c).2 = ⊤ ↔ IsSpecial J (restrict O R) w) := by
  obtain ⟨hp,hDom,hMax,hCan,hEnd,hVal⟩ := h
  exact ⟨hp, companion_letter_geometry hn _ _ _ hDom hMax hCan hEnd o c hVal⟩

section Lift

variable {n m q : ℕ} {X Y : CMfd.{0} n}
  {hk : m ≤ n} {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x m}
  {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n) V y m}
  {T : BlowupTower X Y}
  {N : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
  {M : MarkedIdeal n X}

set_option maxHeartbeats 1250000 in
/-- A supported ambient canonical history produces both actual positive
order-companion reads. The true order and its run clock are unchanged,
and the genuine companion values differ exactly by the recursive
dimension embedding, preserving their boundary level and the top leaf. -/
theorem actual_positive_companion_pair_on_native_lift
    (hn : 0 < n) (hm : 0 < m)
    (h : Lift hk W hWc hW M.E T V hVc hV N)
    (hM : IsInvDomain (q+1) M) (hSupport : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hCan : IsCanonical M ((invFamily hn (q+1)).inv M) T)
    (z : nativeManifold hk V hV) (hz : z.val ∈ (geoTransformAlong M T).cosupp)
    (o : ℕ) (ho : 0 < o) (hOrder : nmOrd (geoTransformAlong M T) z.val = o) :
    let K := nativePullback hk W hW M
    regimeRun (OrdRegime M o) T z.val = regimeRun (OrdRegime K o) N z ∧
    ∃ a b : ℕ ×ₗ WithTop (ValTy q),
      PositiveOrderCompanionWitness (k := q) hn M T z.val o (fun v => v = positiveSuccessorRead o a) ∧
      PositiveOrderCompanionWitness (k := q) hm K N z o (fun v => v = positiveSuccessorRead o b) ∧
      a = stepDimensionMap (sameIndexMap (n-m) q) b ∧
      (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤) := by
  intro K
  have hK := isInvDomain_nativePullback hn hk hW M hM hSupport hTrans
  have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hCut := Lift.original_order_regime_run h hn hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol o z
  have hCos := Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol
  have hzN : z ∈ (geoTransformAlong K N).cosupp := hCos.symm ▸ hz
  have hOrderN := (Lift.current_nmOrd h hn hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol z).symm.trans hOrder
  have hCompare := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (q := q+1) hn hm M hM hSupport hTrans h hCan
  obtain ⟨a,ha,hA⟩ := realized_positive_read hn M T z.val o
    (original_positive_order_successor_read hn M hM T hCan z.val hz o hOrder ho)
  obtain ⟨b,hb,hB⟩ := realized_positive_read hm K N z o
    (original_positive_order_successor_read hm K hK N hCompare.1 z hzN o hOrderN ho)
  have hValue : a = stepDimensionMap (sameIndexMap (n-m) q) b := by
    apply positive_read_injective o
    exact ha.symm.trans ((hCompare.2 z hz).trans
      ((congrArg (sameIndexMap (n-m) (q+1)) hb).trans (sameIndexMap_positive_read _ _ _)))
  refine ⟨hCut,a,b,hA,hB,hValue,?_⟩
  rw [hValue]
  change (ofLex b).1 = (ofLex b).1 ∧
    (WithTop.map (sameIndexMap (n-m) q) (ofLex b).2 = ⊤ ↔ (ofLex b).2 = ⊤)
  exact ⟨rfl, by cases (ofLex b).2 <;> simp⟩

set_option maxHeartbeats 1250000 in
/-- At the common actual order cut, both recast towers are genuine lifts.
The whole companion at that cut and membership in its literal order mask
are transported for every order, including on ordered retained divisors. -/
theorem actual_order_head_companion_geometry
    (hn : 0 < n) (hm : 0 < m)
    (h : Lift hk W hWc hW M.E T V hVc hV N)
    (hM : IsInvDomain (q+1) M) (hSupport : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hTest : IsGeoTestTower M T) (z : nativeManifold hk V hV) (o : ℕ) :
    let K := nativePullback hk W hW M
    let j := regimeRun (OrdRegime M o) T z.val
    j = regimeRun (OrdRegime K o) N z ∧
      ∃ (P : Set (split T j).1) (hPc : IsClosed P)
        (hP : ∀ x ∈ P, RegularAtDim (n := n) P x m)
        (e : (split N j).1 = nativeManifold hk P hP),
        Lift hk W hWc hW M.E (head T j) P hPc hP (recastTarget e (head N j)) ∧
        Lift hk P hPc hP (boundary M.E (head T j)) (tail T j) V hVc hV
          (recastSource e (tail N j)) ∧
        let MH := geoTransformAlong M (head T j)
        let KH := geoTransformAlong K (recastTarget e (head N j))
        (∀ u, nativePullback hk P hP (companionOf n MH u) = companionOf m KH u) ∧
          (∀ u (p : nativeManifold hk P hP), p.val ∈ ordMask MH u ↔ p ∈ ordMask KH u) := by
  intro K j
  have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hCut := Lift.original_order_regime_run h hn hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol o z
  obtain ⟨P,hPc,hP,e,hHead,hTail⟩ := Lift.original_head_tails h j
  have hHTest := ((isGeoTestTower_iff_head_tail M T j).mp hTest).1
  have hMask := Lift.original_current_companion_masks hn hm M hM hSupport hTrans hHead hHTest
  exact ⟨hCut,P,hPc,hP,e,hHead,hTail,hMask.1,hMask.2.1⟩

end Lift
end
end Hironaka.HironakaG1ActualNativeCompanionPhase
