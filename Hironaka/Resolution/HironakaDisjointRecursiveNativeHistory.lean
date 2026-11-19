import Hironaka.Resolution.HironakaActualNativeSectionOrderHistory
import Hironaka.Resolution.HironakaDisjointNativeOpenLift

/-! Original native test histories supply actual ambient admissibility.
Recursive values and canonicality are separate obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointRecursiveNativeHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  SubmanifoldChartedSpace MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowerIsomorphism NormalCrossingsInvariance BlowupRestrictOpen

theorem ambient_test_of_native_test {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W}
    {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n := n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    IsGeoTestTower (nativePullback hk W hW M) Q → IsGeoTestTower M T := by
  induction h with
  | refl => intro _;trivial
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    intro hTest
    refine ⟨ih hTest.1, hπ.1, ?_, ?_⟩
    · rintro _ ⟨p,hp,rfl⟩
      have hpCos := hTest.2.2.1 hp
      rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport
        h hn hE hTrans M hME hMN hhol] at hpCos
      exact hpCos
    · have hBoundary : (geoTransformAlong M T).E=boundary E T :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
          (𝔪 := M) (𝔫 := (⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T
      rw [hBoundary]
      exact hNC

theorem native_open_initial_record {n k : ℕ} {X : CMfd.{0} n}
    (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) (O : Opens X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    nativePullback hk (openSection W O) (openSection_regular hW O)
      (MarkedIdeal.pullback (Subtype.val : O→X) M)=
      MarkedIdeal.pullback (windowEquiv hk W hW hWc O)
        (MarkedIdeal.pullback
          (Subtype.val : nativeWindow hk W hW O→nativeManifold hk W hW)
          (nativePullback hk W hW M)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk (openSection_regular hW O)
  have := isComplexManifold_chartedSpace hk (openSection_regular hW O)
  change markedPullback (m := k) (Subtype.val : openSection W O→O)
      (markedPullback (m := n) (Subtype.val : O→X) M)=_
  calc
    _=markedPullback (m := k) ((Subtype.val : O→X) ∘
        (Subtype.val : openSection W O→O)) M :=
      (whole_markedPullback_comp contMDiff_subtype_val
        (contMDiff_val hk (openSection_regular hW O)) M hI).symm
    _=markedPullback (m := k) ((Subtype.val : nativeManifold hk W hW→X) ∘
        ((Subtype.val : nativeWindow hk W hW O→nativeManifold hk W hW) ∘
          windowEquiv hk W hW hWc O)) M := rfl
    _=markedPullback (m := k)
        ((Subtype.val : nativeWindow hk W hW O→nativeManifold hk W hW) ∘
          windowEquiv hk W hW hWc O) (nativePullback hk W hW M) :=
      whole_markedPullback_comp (contMDiff_val hk hW)
        (contMDiff_subtype_val.comp (windowEquiv hk W hW hWc O).contMDiff) M hI
    _=_ := whole_markedPullback_comp contMDiff_subtype_val
      (windowEquiv hk W hW hWc O).contMDiff (nativePullback hk W hW M)
      (GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_val hk hW) hI)

theorem ambient_test_on_native_reference {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W}
    {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n := n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hI : M.ideal.IsCoherent) (hB : (nativePullback hk W hW M).IsWellFormed)
    (O : Opens X)
    (hNative : IsGeoTestTower
      (MarkedIdeal.pullback
        (Subtype.val : nativeWindow hk W hW O→nativeManifold hk W hW)
        (nativePullback hk W hW M)) (restrict (nativeWindow hk W hW O) Q)) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O→X) M) (restrict O T) := by
  obtain ⟨hSc,hS,P,hLift,hIso⟩:=exists_open_lift h O
  have hBO:=MarkedIdealRestrictOpen.IsWellFormed.pullback_val
    hB (nativeWindow hk W hW O)
  have hNativeP := (IsTowerIso.isGeoTestTower_iff
    (windowEquiv hk W hW hWc O) hBO.isClosedSubmanifold_N hBO.isCoherent hIso).mpr hNative
  rw [←native_open_initial_record hk W hWc hW O M hI] at hNativeP
  exact ambient_test_of_native_test hLift hn
    (isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE)
    (isTransverse_preimage (pullsBackCoordinates_val O) hTrans)
    (MarkedIdeal.pullback (Subtype.val : O→X) M)
    (congrArg (List.map ((Subtype.val : O→X) ⁻¹' ·)) hME)
    (preimage_mono hMN) (fun _ _ hg=>hg.1) hNativeP

end
end Hironaka.HironakaDisjointRecursiveNativeHistory
