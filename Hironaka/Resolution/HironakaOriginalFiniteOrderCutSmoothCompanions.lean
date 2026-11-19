/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutCompanionTests
/-! Genuine smooth CURRENT-companion TEST and whole controlled histories
following actual preparation, without new upper/source canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteOrderCutSmoothCompanions
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue GeneralCompare GeneralCanonicalTail HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalSimultaneousHSAdmissibleCentre
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionHistoricalCompanionMasks HironakaSmoothSubmersionHistoricalControlledTail
  HironakaSmoothSubmersionNonmonomialHistory HironakaHolomorphicJetChartInvariance ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m b : ℕ} {X D Z : CMfd.{u} n} {Y Z' : CMfd.{u} m}

/-- A genuine smooth Cartesian source inherits every literal original cut. -/
theorem IsActualTowerPullback.orderCutTower_pullback
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    {f : Y → X} {g : Z' → Z} {Q : BlowupTower Y Z'} {P : BlowupTower X Z}
    (h : IsActualTowerPullback f Q P g) (hP : IsOrderCutTower M P) :
    IsOrderCutTower (markedPullback (m := m) f M) Q := by
  induction h with
  | refl => trivial
  | @step D' D V' V Q T g h hg C π hπ ρ hρ ih =>
    have hTest := orderCutTower_geoTest M (.step T C π hπ) hP
    have hSource := (IsActualTowerPullback.relative_marked_dictionary
      (IsActualTowerPullback.step h hg hπ hρ) M hM.isWellFormed hTest).1
    refine ⟨ih hP.1,hSource.2,?_⟩
    intro y hy hp c hc
    have hOrd := IsActualTowerPullback.orderAt_dictionary hn h M hM hTest.1
    change ∀ z,nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z=
      nmOrd (geoTransformAlong M T) (g z) at hOrd
    rw [IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hTest.1] at hy
    rw [hOrd y] at hp
    rw [hOrd y,hOrd c]
    exact hP.2.2 (g y) hy hp (g c) hc

private theorem base_submersion {f : Y → X} {g : Z' → Z}
    {Q : BlowupTower Y Z'} {P : BlowupTower X Z} (h : IsActualTowerPullback f Q P g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

/-- Elaborate the genuine relative-domain and all-head theorem at literal
manifold variables before instantiating two competing actual open carriers. -/
private theorem actual_relative_domains_and_heads 
    {p : Y → X} {q : Z' → Z} {R' : BlowupTower Y Z'} {R : BlowupTower X Z}
    (h : IsActualTowerPullback p R' R q) (J : MarkedIdeal n X)
    (hJ : IsInvDomain b J) (hR : IsGeoTestTower J R) :
    let K := markedPullback (m := m) p J
    IsInvDomain (b+(m-n)) K ∧ IsGeoTestTower K R' ∧
      IsInvDomain (b+(m-n)) (geoTransformAlong K R') ∧
      geoTransformAlong K R'=markedPullback (m := m) q (geoTransformAlong J R) ∧
      (geoTransformAlong K R').cosupp=q ⁻¹' (geoTransformAlong J R).cosupp ∧
      ∀ i : ℕ,∃ a : (split R' i).1 → (split R i).1,
        IsActualTowerPullback p (head R' i) (head R i) a ∧ IsGeoTestTower K (head R' i) ∧
        geoTransformAlong K (head R' i)=markedPullback (m := m) a (geoTransformAlong J (head R i)) ∧
        (geoTransformAlong K (head R' i)).cosupp=a ⁻¹' (geoTransformAlong J (head R i)).cosupp := by
  have hK := isInvDomain_markedPullback_submersion (base_submersion h) J hJ
  obtain ⟨hSourceTest,hWhole⟩ := IsActualTowerPullback.relative_marked_dictionary h J hJ.isWellFormed hR
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary h J hJ.isWellFormed hR
  refine ⟨hK,hSourceTest,InvDomainTowerAlong.isInvDomain_geoTransformAlong hK R' hSourceTest,hWhole,hCos,?_⟩
  intro i
  obtain ⟨a,ha⟩ := h.head i
  have hTi := ((isGeoTestTower_iff_head_tail J R i).mp hR).1
  obtain ⟨hQi,hWi⟩ := IsActualTowerPullback.relative_marked_dictionary ha J hJ.isWellFormed hTi
  have hCi := IsActualTowerPullback.relative_cosupport_dictionary ha J hJ.isWellFormed hTi
  exact ⟨a,ha,hQi,hWi,hCi⟩

/-- Actual finite-cut companion TESTs are proved internally before any source diagram. -/
theorem orderCutTower_current_companion_smooth_diagram
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (P : BlowupTower X Z) (hRecipe : IsOrderCutTower M P)
    {f : Y → X} {g : Z' → Z} {Q : BlowupTower Y Z'} (h : IsActualTowerPullback f Q P g)
    (z : Z') (hz : g z ∈ (geoTransformAlong M P).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M P) (g z)) :
    let N := markedPullback (m := m) f M
    let o := nmOrd (geoTransformAlong M P) (g z)
    let r := regimeRun (OrdRegime M o) P (g z)
    let U := ordMask (geoTransformAlong M (head P r)) o
    let V := ordMask (geoTransformAlong N (head Q r)) o
    let J := compAt M o (head P r)
    let J' := compAt N o (head Q r)
    let R := restrict U (tail P r)
    let R' := restrict V (tail Q r)
    nmOrd (geoTransformAlong N Q) z=o ∧ regimeRun (OrdRegime N o) Q z=r ∧
      ∃ (hp : (tail P r).proj (g z) ∈ U) (hp' : (tail Q r).proj z ∈ V)
        (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail P r) U),
        markedPullback (m := m) p J=J' ∧ IsActualTowerPullback p R' R q ∧
        (∀ w,(q w : Z)=g (w : Z')) ∧ q ⟨z,hp'⟩=⟨g z,hp⟩ ∧
        IsInvDomain b J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
        IsGeoTestTower J R ∧ IsInvDomain b (geoTransformAlong J R) ∧
        (⟨g z,hp⟩ : openPreimage (tail P r) U) ∈ (geoTransformAlong J R).cosupp ∧
        IsInvDomain (b+(m-n)) J' ∧ IsGeoTestTower J' R' ∧
        IsInvDomain (b+(m-n)) (geoTransformAlong J' R') ∧
        (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' R').cosupp ∧
        geoTransformAlong J' R'=markedPullback (m := m) q (geoTransformAlong J R) ∧
        (geoTransformAlong J' R').cosupp=q ⁻¹' (geoTransformAlong J R).cosupp ∧
        ∀ i : ℕ,∃ a : (split R' i).1 → (split R i).1,
          IsActualTowerPullback p (head R' i) (head R i) a ∧ IsGeoTestTower J' (head R' i) ∧
          geoTransformAlong J' (head R' i)=markedPullback (m := m) a (geoTransformAlong J (head R i)) ∧
          (geoTransformAlong J' (head R' i)).cosupp=a ⁻¹' (geoTransformAlong J (head R i)).cosupp := by
  dsimp only
  have hP := orderCutTower_geoTest M P hRecipe
  have hComp := orderCutTower_current_companion_test hn M hM P hRecipe
    (nmOrd (geoTransformAlong M P) (g z)) hp (g z)
  let N := markedPullback (m := m) f M
  let o := nmOrd (geoTransformAlong M P) (g z)
  let r := regimeRun (OrdRegime M o) P (g z)
  let U := ordMask (geoTransformAlong M (head P r)) o
  let V := ordMask (geoTransformAlong N (head Q r)) o
  let J := compAt M o (head P r)
  let J' := compAt N o (head Q r)
  let R := restrict U (tail P r)
  let R' := restrict V (tail Q r)
  obtain ⟨hHeadT,hTailT⟩ := (isGeoTestTower_iff_head_tail M P r).mp hP
  have hDom := isInvDomain_compAt hn hp (head P r)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (head P r) hHeadT)
  have hMax := isMaximalOrderAlong_compAt hn o (head P r)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (head P r) hHeadT)
  have hTest : IsGeoTestTower J R := hComp
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom R hTest
  have hMask : (tail P r).proj (g z) ∈ U := (proj_tail_mem_ordMask hn hM P hP hz (o := o) rfl).2
  have hTargetPoint : (⟨g z,hMask⟩ : openPreimage (tail P r) U) ∈ (geoTransformAlong J R).cosupp := by
    apply (mem_cosupp_compAt_iff hn hM hp (head P r) (tail P r) hHeadT hTailT hTest ⟨g z,hMask⟩).mpr
    rw [←geoTransformAlong_head_tail M P r]
    exact ⟨hz,rfl⟩
  obtain ⟨p,q,hRecord,hCoord,hCart⟩ := IsActualTowerPullback.exists_actual_historical_tail hn h M hM hP r o
  change markedPullback (m := m) p J=J' at hRecord
  change IsActualTowerPullback p R' R q at hCart
  obtain ⟨a,hHead,hTail⟩ := IsActualTowerPullback.simultaneous_split h r
  have hTH := ((isGeoTestTower_iff_head_tail M P r).mp hP).1
  have hPre : (V : Set (split Q r).1)=a ⁻¹' (U : Set (split P r).1) :=
    IsActualTowerPullback.order_mask_dictionary hn hHead M hM hTH o
  have hSourceMask : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hPre]
    change a ((tail Q r).proj z) ∈ U
    rw [←hTail.proj_comm z]
    exact hMask
  have hPoint : q (⟨z,hSourceMask⟩ : openPreimage (tail Q r) V)=⟨g z,hMask⟩ :=
    Subtype.ext (hCoord ⟨z,hSourceMask⟩)
  have hSourceData := actual_relative_domains_and_heads hCart J hDom hTest
  rw [hRecord] at hSourceData
  obtain ⟨hSourceDom,hSourceTest,hSourceCurrent,hWhole,hCos,hHeads⟩ := hSourceData
  have hSourcePoint : (⟨z,hSourceMask⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' R').cosupp := by
    rw [hCos]
    change q ⟨z,hSourceMask⟩ ∈ (geoTransformAlong J R).cosupp
    rw [hPoint]
    exact hTargetPoint
  refine ⟨IsActualTowerPullback.orderAt_dictionary hn h M hM hP z,
    IsActualTowerPullback.fixed_order_regime_run hn h M hM hP o z,
    hMask,hSourceMask,p,q,hRecord,hCart,hCoord,hPoint,hDom,hMax,hTest,hCurrent,hTargetPoint,
    hSourceDom,hSourceTest,hSourceCurrent,hSourcePoint,hWhole,hCos,hHeads⟩

end
end Hironaka.HironakaOriginalFiniteOrderCutSmoothCompanions
