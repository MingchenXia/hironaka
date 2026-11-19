import Hironaka.Resolution.HironakaG1NativeOrderDispatcher
import Hironaka.Resolution.HironakaG1RefreshedNativeZeroLift

/-! The recursive original order dispatcher after a literal refreshed zero branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set TopologicalSpace

namespace Hironaka.HironakaG1RefreshedNativeOrderDispatcher

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres NormalCrossings SubmanifoldChartedSpace
  HomogenizedIdealAlong CoefficientIdealRestriction MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG8GapNormalizedExponent HironakaG1AdvancingRefreshedCoefficient
  HironakaActualNativeSectionFiniteHistory HironakaActualSectionBoundaryDimension
  HironakaG1RefreshedNativeZeroLift HironakaG1NativeOrderDispatcher
  HironakaG1LaterPositiveSuccessorRead HironakaG1InitialPositiveGeneralRead
  NonmonomialOrderLocal NonmonomialOrderRegime GeneralValue StepOneRegime
  HironakaSmoothSubmersionCanonicalValueDimensionShift MonomialCaseAlong

/-- Refresh compatibility on the actual advancing zero window realizes
the native suffix and dispatches its next recursive value. The zero
recursive order uses the full current-boundary gamma; positive order
uses the actual two companion histories on that same Lift. -/
theorem refreshed_supported_native_order_dispatch {n k r m : ℕ} {A Y : CMfd.{0} n}
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (M P : MarkedIdeal n A) (hM : IsInvDomain m M) (hP : IsInvDomain (r+1) P)
    (hIn : P.N ⊆ M.N) (hRefresh : RestrictEquiv P (withN (coeffMarkedAlong M) P.N))
    (hSub : P.N ⊆ W) (hTrans : IsTransverse n W P.E)
    (T : BlowupTower A Y) (hCan : HasCosupportGap P → IsCanonical P ((invFamily hn (r+1)).inv P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n) V z k)
      (N : BlowupTower (nativeManifold hkn W hW) (nativeManifold hkn V hV)),
      Lift hkn W hWc hW P.E T V hVc hV N ∧
      let PN := nativePullback hkn W hW P
      let F := geoTransformAlong P T
      let G := geoTransformAlong PN N
      IsInvDomain (r+1) PN ∧ G = nativePullback hkn V hV F ∧
      IsCanonical PN ((invFamily hk (r+1)).inv PN) N ∧
      ∃ z : nativeManifold hkn V hV, z.val = y ∧ z ∈ G.cosupp ∧
        let o := nmOrd F z.val
        let v := (invFamily hn (r+1)).inv P T z.val
        let w := (invFamily hk (r+1)).inv PN N z
        o = nmOrd G z ∧ v = sameIndexMap (n-k) (r+1) w ∧
        if o = 0 then
          v = monomialRead (q := r) F z.val ∧ w = monomialRead (q := r) G z ∧
          gammaAlong n F.N F.ideal F.E F.d z.val =
            dimensionValue (n-k) (gammaAlong k G.N G.ideal G.E G.d z)
        else
          regimeRun (OrdRegime P o) T z.val = regimeRun (OrdRegime PN o) N z ∧
          ∃ a b : ℕ ×ₗ WithTop (ValTy r),
            v = positiveSuccessorRead o a ∧ w = positiveSuccessorRead o b ∧
            PositiveOrderCompanionWitness (k := r) hn P T z.val o (fun t => t = positiveSuccessorRead o a) ∧
            PositiveOrderCompanionWitness (k := r) hk PN N z o (fun t => t = positiveSuccessorRead o b) ∧
            a = stepDimensionMap (sameIndexMap (n-k) r) b ∧
            (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤) := by
  have hA := hCan (refreshed_restricted_coefficient_gap M P hM hIn hRefresh)
  obtain ⟨V,hVc,hV,N,hLift,_,_,_,_,_,z,hzy,_,_⟩ :=
    native_supported_canonical_read hn hk hkn W hWc hW P hP hSub hTrans T hA y hy
  have hzY : z.val ∈ (geoTransformAlong P T).cosupp := hzy.symm ▸ hy
  obtain ⟨hDomain,hWhole,hNCan,hEnd,hOrd,hValue,hBranch⟩ :=
    actual_native_order_dispatch hn hk hLift hP hSub hTrans hA z hzY
  exact ⟨V,hVc,hV,N,hLift,hDomain,hWhole,hNCan,z,hzy,hEnd,hOrd,hValue,hBranch⟩

#print axioms refreshed_supported_native_order_dispatch

end Hironaka.HironakaG1RefreshedNativeOrderDispatcher
