import Hironaka.Resolution.HironakaG1AdvancingRefreshedCoefficient
import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative

/-! Native histories on a current supported window after exact coefficient refresh. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open Set TopologicalSpace

namespace Hironaka.HironakaG1RefreshedNativeZeroLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres NormalCrossings SubmanifoldChartedSpace
  HomogenizedIdealAlong CoefficientIdealRestriction MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG8GapNormalizedExponent HironakaG1AdvancingRefreshedCoefficient
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeHistoryExistence
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryDimension RelativePrincipalizationSpan

/-- On a fixed smooth supported window, a genuine canonical selected tail
has a native lift carrying the entire record, ordered boundary and value.
This applies to either branch once its own canonical tail has been selected. -/
theorem native_supported_canonical_read {n k r : ℕ} {A Y : CMfd.{0} n}
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (P : MarkedIdeal n A) (hP : IsInvDomain r P) (hSub : P.N ⊆ W) (hTrans : IsTransverse n W P.E)
    (T : BlowupTower A Y) (hCan : IsCanonical P ((invFamily hn r).inv P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n) V z k)
      (N : BlowupTower (nativeManifold hkn W hW) (nativeManifold hkn V hV)),
      Lift hkn W hWc hW P.E T V hVc hV N ∧
      let PN := nativePullback hkn W hW P
      IsInvDomain r PN ∧ IsCanonical PN ((invFamily hk r).inv PN) N ∧
        IsGeoTestTower PN N ∧ N.length = T.length ∧
        geoTransformAlong PN N = nativePullback hkn V hV (geoTransformAlong P T) ∧
        ∃ z : nativeManifold hkn V hV, z.val = y ∧ z ∈ (geoTransformAlong PN N).cosupp ∧
          (invFamily hn r).inv P T y = sameIndexMap (n-k) r ((invFamily hk r).inv PN N z) := by
  have hT := (invFamily hn r).isInvValue.isGeoTestTower_of_isCanonical hP T hCan
  obtain ⟨V,hVc,hV,N,hLift,hTest⟩ :=
    exists_native_history_of_original_test hn hkn W hWc hW P hP hSub hTrans T hT
  have hDomain := isInvDomain_nativePullback hn hkn hW P hP hSub hTrans
  have hValue := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (n := n) (k := k) (q := r) (X := A) (hk := hkn) (W := W) (hWc := hWc) (hW := hW)
    (T := T) (V := V) (hVc := hVc) (hV := hV) (Q := N)
    hn hk P hP hSub hTrans hLift hCan
  have hHol : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg
  have hWhole := hLift.whole_records hn hP.isWellFormed.isSNCDivisor hTrans P rfl hSub hHol
  have hCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift hn
    hP.isWellFormed.isSNCDivisor hTrans P rfl hSub hHol
  have hSupport := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift P hSub
  let z : nativeManifold hkn V hV := ⟨y,hSupport hy.1⟩
  exact ⟨V,hVc,hV,N,hLift,hDomain,hValue.1,hTest,hLift.length,hWhole,z,rfl,
    hCos.symm ▸ hy,hValue.2 z hy⟩

/-- Exact refreshed coefficients close the actual zero-head CAN gate before
native realization, without changing the source, suffix or ordered boundary. -/
theorem refreshed_supported_native_read {n k r m : ℕ} {A Y : CMfd.{0} n}
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (M P : MarkedIdeal n A) (hM : IsInvDomain m M) (hP : IsInvDomain r P)
    (hIn : P.N ⊆ M.N) (hRefresh : RestrictEquiv P (withN (coeffMarkedAlong M) P.N))
    (hSub : P.N ⊆ W) (hTrans : IsTransverse n W P.E)
    (T : BlowupTower A Y) (hCan : HasCosupportGap P → IsCanonical P ((invFamily hn r).inv P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n) V z k)
      (N : BlowupTower (nativeManifold hkn W hW) (nativeManifold hkn V hV)),
      Lift hkn W hWc hW P.E T V hVc hV N ∧
      let PN := nativePullback hkn W hW P
      IsInvDomain r PN ∧ IsCanonical PN ((invFamily hk r).inv PN) N ∧
        IsGeoTestTower PN N ∧ N.length = T.length ∧
        geoTransformAlong PN N = nativePullback hkn V hV (geoTransformAlong P T) ∧
        ∃ z : nativeManifold hkn V hV, z.val = y ∧ z ∈ (geoTransformAlong PN N).cosupp ∧
          (invFamily hn r).inv P T y = sameIndexMap (n-k) r ((invFamily hk r).inv PN N z) :=
  native_supported_canonical_read hn hk hkn W hWc hW P hP hSub hTrans T
    (hCan (refreshed_restricted_coefficient_gap M P hM hIn hRefresh)) y hy

#print axioms native_supported_canonical_read
#print axioms refreshed_supported_native_read

end Hironaka.HironakaG1RefreshedNativeZeroLift
