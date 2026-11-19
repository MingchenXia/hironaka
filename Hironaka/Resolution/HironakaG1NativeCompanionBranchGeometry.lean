import Hironaka.Resolution.HironakaG1ActualNativeCompanionPhase

/-! # Literal special-branch and retained-slot comparison of actual native companions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1NativeCompanionBranchGeometry
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

set_option maxHeartbeats 1400000 in
/-- Canonicality and a surviving positive-order point force maximal order
on both actual masked companions. The literal special branches agree,
and so do the incident retained-slot counts of their actual tails. -/
theorem actual_masked_companions_maximal_and_special_on_native_lift
    (hn : 0 < n) (hm : 0 < m)
    (h : Lift hk W hWc hW M.E T V hVc hV N)
    (hM : IsInvDomain (q+1) M) (hSupport : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hCan : IsCanonical M ((invFamily hn (q+1)).inv M) T)
    (z : nativeManifold hk V hV) (hz : z.val ∈ (geoTransformAlong M T).cosupp)
    (o : ℕ) (ho : 0 < o) (hOrder : nmOrd (geoTransformAlong M T) z.val = o) :
    let K := nativePullback hk W hW M
    let r := regimeRun (OrdRegime M o) T z.val
    let s := regimeRun (OrdRegime K o) N z
    let H := head T r
    let H' := head N s
    let R := tail T r
    let R' := tail N s
    let O := ordMask (geoTransformAlong M H) o
    let O' := ordMask (geoTransformAlong K H') o
    let J := compAt M o H
    let J' := compAt K o H'
    let U := restrict O R
    let U' := restrict O' R'
    r = s ∧
      IsMaximalOrderAlong J.N J.ideal J.d ∧ IsMaximalOrderAlong J'.N J'.ideal J'.d ∧
      ∃ (hzA : z.val ∈ openPreimage R O) (hzB : z ∈ openPreimage R' O'),
        let w : openPreimage R O := ⟨z.val,hzA⟩
        let w' : openPreimage R' O' := ⟨z,hzB⟩
        (IsSpecial J U w ↔ IsSpecial J' U' w') ∧
          boundaryCount (J.E.map (strictAlong U)) w =
            boundaryCount (J'.E.map (strictAlong U')) w' := by
  obtain ⟨hr,a,b,hA,hB,_,hCount,hTop⟩ :=
    actual_positive_companion_pair_on_native_lift hn hm h hM hSupport hTrans hCan z hz o ho hOrder
  obtain ⟨hpa,hCountA,hSpecialA⟩ :=
    positive_companion_witness_slot_count_and_special hn M T z.val o a hA
  obtain ⟨hpb,hCountB,hSpecialB⟩ :=
    positive_companion_witness_slot_count_and_special hm (nativePullback hk W hW M) N z o b hB
  obtain ⟨_,_,hMaxA,_,_,_⟩ := hA
  obtain ⟨_,_,hMaxB,_,_,_⟩ := hB
  exact ⟨hr,hMaxA,hMaxB,hpa,hpb,hSpecialA.symm.trans (hTop.trans hSpecialB),
    hCountA.symm.trans (hCount.trans hCountB)⟩

end Lift
end
end Hironaka.HironakaG1NativeCompanionBranchGeometry
