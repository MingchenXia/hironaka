import Hironaka.Resolution.HironakaG1NativeCompanionBranchGeometry

/-! # Actual native order dispatcher -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1NativeOrderDispatcher
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

/-- The explicit monomial letter of the original successor evaluator.
Its gamma uses the entire current ordered boundary of the record. -/
abbrev monomialRead {n q : ℕ} {Y : CMfd.{0} n}
    (A : MarkedIdeal n Y) (y : Y) : ValTy (q+1) :=
  toLex (0,toLex (Sum.inl (gammaAlong n A.N A.ideal A.E A.d y)))

set_option maxHeartbeats 1500000 in
/-- The actual original successor evaluator on a supported common native
lift has matched order and an exact same-index value. At order zero it
reads the literal full-boundary monomial gamma. At positive order it
reads both actual masked companions, with exact run, retained-slot level
and special top, and recursive dimension transport of the live leaf. -/
theorem actual_native_order_dispatch
    (hn : 0 < n) (hm : 0 < m)
    (h : Lift hk W hWc hW M.E T V hVc hV N)
    (hM : IsInvDomain (q+1) M) (hSupport : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hCan : IsCanonical M ((invFamily hn (q+1)).inv M) T)
    (z : nativeManifold hk V hV) (hz : z.val ∈ (geoTransformAlong M T).cosupp) :
    let K := nativePullback hk W hW M
    let A := geoTransformAlong M T
    let B := geoTransformAlong K N
    let o := nmOrd A z.val
    let v := (invFamily hn (q+1)).inv M T z.val
    let w := (invFamily hm (q+1)).inv K N z
    IsInvDomain (q+1) K ∧ B = nativePullback hk V hV A ∧
    IsCanonical K ((invFamily hm (q+1)).inv K) N ∧
    z ∈ B.cosupp ∧ o = nmOrd B z ∧ v = sameIndexMap (n-m) (q+1) w ∧
    if o = 0 then
      v = monomialRead (q := q) A z.val ∧ w = monomialRead (q := q) B z ∧
      gammaAlong n A.N A.ideal A.E A.d z.val =
        dimensionValue (n-m) (gammaAlong m B.N B.ideal B.E B.d z)
    else
      regimeRun (OrdRegime M o) T z.val = regimeRun (OrdRegime K o) N z ∧
      ∃ a b : ℕ ×ₗ WithTop (ValTy q),
        v = positiveSuccessorRead o a ∧ w = positiveSuccessorRead o b ∧
        PositiveOrderCompanionWitness (k := q) hn M T z.val o (fun x => x = positiveSuccessorRead o a) ∧
        PositiveOrderCompanionWitness (k := q) hm K N z o (fun x => x = positiveSuccessorRead o b) ∧
        a = stepDimensionMap (sameIndexMap (n-m) q) b ∧
        (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤) := by
  intro K A B o v w
  have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hCos := Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol
  have hzN : z ∈ B.cosupp := hCos.symm ▸ hz
  have hOrd : o = nmOrd B z := Lift.current_nmOrd h hn hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol z
  have hK := isInvDomain_nativePullback hn hk hW M hM hSupport hTrans
  have hWhole := h.whole_records hn hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol
  have hCompare := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (q := q+1) hn hm M hM hSupport hTrans h hCan
  refine ⟨hK,hWhole,hCompare.1,hzN,hOrd,hCompare.2 z hz,?_⟩
  by_cases hZero : o = 0
  · rw [if_pos hZero]
    have hTest := (invFamily hn (q+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hCan
    have hg := (Lift.original_current_companion_masks hn hm M hM hSupport hTrans h hTest).2.2 z
    exact ⟨genInv_of_nmOrd_eq_zero _ M T hZero,
      genInv_of_nmOrd_eq_zero _ K N (hOrd.symm.trans hZero),hg⟩
  · rw [if_neg hZero]
    have ho := Nat.pos_of_ne_zero hZero
    obtain ⟨hr,a,b,hA,hB,hMapping,hLevel,hTop⟩ :=
      actual_positive_companion_pair_on_native_lift hn hm h hM hSupport hTrans hCan z hz o ho rfl
    obtain ⟨_,_,_,_,_,hValA⟩ := original_positive_order_successor_read hn M hM T hCan z.val hz o rfl ho
    obtain ⟨_,_,_,_,_,hValB⟩ := original_positive_order_successor_read hm K hK N hCompare.1 z hzN o hOrd.symm ho
    have hAread := hA
    have hBread := hB
    obtain ⟨_,_,_,_,_,hLetterA⟩ := hAread
    obtain ⟨_,_,_,_,_,hLetterB⟩ := hBread
    exact ⟨hr,a,b,hValA.trans hLetterA,hValB.trans hLetterB,hA,hB,hMapping,hLevel,hTop⟩

end Lift
end
end Hironaka.HironakaG1NativeOrderDispatcher
