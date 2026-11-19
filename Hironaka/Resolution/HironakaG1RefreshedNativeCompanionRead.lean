import Hironaka.Resolution.HironakaG1ActualNativeCompanionPhase
import Hironaka.Resolution.HironakaG1RefreshedNativeZeroLift

/-! The positive order read on the actual native Lift of a refreshed zero branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set TopologicalSpace

namespace Hironaka.HironakaG1RefreshedNativeCompanionRead

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres NormalCrossings SubmanifoldChartedSpace
  HomogenizedIdealAlong CoefficientIdealRestriction MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG8GapNormalizedExponent HironakaG1AdvancingRefreshedCoefficient
  HironakaActualNativeSectionFiniteHistory HironakaActualSectionBoundaryDimension
  HironakaG1RefreshedNativeZeroLift HironakaG1ActualNativeCompanionPhase
  HironakaG1LaterPositiveSuccessorRead HironakaG1InitialPositiveGeneralRead
  NonmonomialOrderLocal NonmonomialOrderRegime GeneralValue StepOneRegime
  HironakaSmoothSubmersionCanonicalValueDimensionShift

/-- When the selected supported record of a zero branch subsequently has
positive nonmonomial order, refresh compatibility supplies its CAN and
both actual order-companion witnesses on the same constructed native Lift.
The witnesses use the literal recursive order run and preserve level/top. -/
theorem refreshed_zero_to_native_positive_companion {n k r m : ℕ} {A Y : CMfd.{0} n}
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (M P : MarkedIdeal n A) (hM : IsInvDomain m M) (hP : IsInvDomain (r+1) P)
    (hIn : P.N ⊆ M.N) (hRefresh : RestrictEquiv P (withN (coeffMarkedAlong M) P.N))
    (hSub : P.N ⊆ W) (hTrans : IsTransverse n W P.E)
    (T : BlowupTower A Y) (hCan : HasCosupportGap P → IsCanonical P ((invFamily hn (r+1)).inv P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp)
    (o : ℕ) (ho : 0 < o) (hOrder : nmOrd (geoTransformAlong P T) y = o) :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n) V z k)
      (N : BlowupTower (nativeManifold hkn W hW) (nativeManifold hkn V hV)),
      Lift hkn W hWc hW P.E T V hVc hV N ∧
      let PN := nativePullback hkn W hW P
      IsCanonical PN ((invFamily hk (r+1)).inv PN) N ∧
      geoTransformAlong PN N = nativePullback hkn V hV (geoTransformAlong P T) ∧
      ∃ z : nativeManifold hkn V hV, z.val = y ∧ z ∈ (geoTransformAlong PN N).cosupp ∧
        regimeRun (OrdRegime P o) T z.val = regimeRun (OrdRegime PN o) N z ∧
        ∃ a b : ℕ ×ₗ WithTop (ValTy r),
          PositiveOrderCompanionWitness (k := r) hn P T z.val o (fun v => v = positiveSuccessorRead o a) ∧
          PositiveOrderCompanionWitness (k := r) hk PN N z o (fun v => v = positiveSuccessorRead o b) ∧
          a = stepDimensionMap (sameIndexMap (n-k) r) b ∧
          (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤) := by
  have hA := hCan (refreshed_restricted_coefficient_gap M P hM hIn hRefresh)
  obtain ⟨V,hVc,hV,N,hLift,_,hNCan,_,_,hWhole,z,hzy,hEnd,_⟩ :=
    native_supported_canonical_read hn hk hkn W hWc hW P hP hSub hTrans T hA y hy
  have hzY : z.val ∈ (geoTransformAlong P T).cosupp := hzy.symm ▸ hy
  have hzOrder : nmOrd (geoTransformAlong P T) z.val = o := hzy.symm ▸ hOrder
  exact ⟨V,hVc,hV,N,hLift,hNCan,hWhole,z,hzy,hEnd,
    actual_positive_companion_pair_on_native_lift hn hk hLift hP hSub hTrans hA z hzY o ho hzOrder⟩

#print axioms refreshed_zero_to_native_positive_companion

end Hironaka.HironakaG1RefreshedNativeCompanionRead
