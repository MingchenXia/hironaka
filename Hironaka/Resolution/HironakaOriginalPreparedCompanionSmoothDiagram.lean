/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentCompanion
/-! Genuine smooth CURRENT-companion TEST and whole controlled histories
following actual preparation, without new upper/source canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedCompanionSmoothDiagram
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue GeneralCompare GeneralCanonicalTail HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime
  HironakaOriginalPreparedCurrentCompanion HironakaOriginalSimultaneousHSAdmissibleCentre
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionHistoricalCompanionMasks HironakaSmoothSubmersionHistoricalControlledTail
  HironakaSmoothSubmersionNonmonomialHistory HironakaHolomorphicJetChartInvariance ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X D Z : CMfd.{u} n} {Y Z' : CMfd.{u} m}

private theorem base_submersion {f : Y → X} {g : Z' → Z}
    {Q : BlowupTower Y Z'} {P : BlowupTower X Z} (h : IsActualTowerPullback f Q P g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

/-- Elaborate the genuine relative-domain and all-head theorem at literal
manifold variables before instantiating two competing actual open carriers. -/
private theorem actual_relative_domains_and_heads {b : ℕ}
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

/-- The complete actual diagram is elaborated at an ABSTRACT genuine upper
history before instantiation by a real blowup step. The companion TEST is
an internally proved input at the public preparation consumer below. -/
private theorem actual_current_companion_diagram
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (P : BlowupTower X Z) (hP : IsGeoTestTower M P)
    {f : Y → X} {g : Z' → Z} {Q : BlowupTower Y Z'} (h : IsActualTowerPullback f Q P g)
    (z : Z') (hz : g z ∈ (geoTransformAlong M P).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M P) (g z))
    (hComp : let o := nmOrd (geoTransformAlong M P) (g z)
      let r := regimeRun (OrdRegime M o) P (g z)
      IsGeoTestTower (compAt M o (head P r))
        (restrict (ordMask (geoTransformAlong M (head P r)) o) (tail P r))) :
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
        IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
        IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
        (⟨g z,hp⟩ : openPreimage (tail P r) U) ∈ (geoTransformAlong J R).cosupp ∧
        IsInvDomain ((k+1)+(m-n)) J' ∧ IsGeoTestTower J' R' ∧
        IsInvDomain ((k+1)+(m-n)) (geoTransformAlong J' R') ∧
        (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' R').cosupp ∧
        geoTransformAlong J' R'=markedPullback (m := m) q (geoTransformAlong J R) ∧
        (geoTransformAlong J' R').cosupp=q ⁻¹' (geoTransformAlong J R).cosupp ∧
        ∀ i : ℕ,∃ a : (split R' i).1 → (split R i).1,
          IsActualTowerPullback p (head R' i) (head R i) a ∧ IsGeoTestTower J' (head R' i) ∧
          geoTransformAlong J' (head R' i)=markedPullback (m := m) a (geoTransformAlong J (head R i)) ∧
          (geoTransformAlong J' (head R' i)).cosupp=a ⁻¹' (geoTransformAlong J (head R i)).cosupp := by
  dsimp only
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

/-- Actual target current-companion TEST precedes all actual source masked
TESTs, domains, whole-record identities and current cosupport points. -/
theorem prepared_current_companion_smooth_diagram
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c)
    {f : Y → X} {g : Z' → Z} {Q : BlowupTower Y Z'}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g)
    (z : Z') (hz : g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M (.step T C π hπ)) (g z)) :
    let P := .step T C π hπ
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
        IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
        IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
        (⟨g z,hp⟩ : openPreimage (tail P r) U) ∈ (geoTransformAlong J R).cosupp ∧
        IsInvDomain ((k+1)+(m-n)) J' ∧ IsGeoTestTower J' R' ∧
        IsInvDomain ((k+1)+(m-n)) (geoTransformAlong J' R') ∧
        (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' R').cosupp ∧
        geoTransformAlong J' R'=markedPullback (m := m) q (geoTransformAlong J R) ∧
        (geoTransformAlong J' R').cosupp=q ⁻¹' (geoTransformAlong J R).cosupp ∧
        ∀ i : ℕ,∃ a : (split R' i).1 → (split R i).1,
          IsActualTowerPullback p (head R' i) (head R i) a ∧ IsGeoTestTower J' (head R' i) ∧
          geoTransformAlong J' (head R' i)=markedPullback (m := m) a (geoTransformAlong J (head R i)) ∧
          (geoTransformAlong J' (head R' i)).cosupp=a ⁻¹' (geoTransformAlong J (head R i)).cosupp := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  have hComp := current_compAt_test_after_full_cut hn M hM T hc C hC π hπ hCuts (g z) hp
  exact actual_current_companion_diagram hn M hM (.step T C π hπ) hP h z hz hp hComp

/-- ONE actual whole upper pullback history precedes EVERY current companion
diagram; all centres, inequalities and lower TESTs are internally supplied. -/
theorem exists_original_compact_prepared_companion_smooth_history
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (hK : IsCompact (geoTransformAlong M T).cosupp)
    (hne : (geoTransformAlong M T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    {f : Y → X} (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
    ∃ (a : D) (C : Set D) (Z : CMfd.{u} n) (π : Z → D) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ (geoTransformAlong M T).IsAdmissibleCentre C ∧
      (∀ c ∈ C,(invFamily hn (k+1)).inv M T c=(invFamily hn (k+1)).inv M T a) ∧
      (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      ∃ (Z' : CMfd.{u} m) (Q : BlowupTower Y Z') (g : Z' → Z),
        IsActualTowerPullback f Q (.step T C π hπ) g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
        ∀ z : Z',g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp →
          0<nmOrd (geoTransformAlong M (.step T C π hπ)) (g z) →
          let P := .step T C π hπ
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
              IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
              IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
              (⟨g z,hp⟩ : openPreimage (tail P r) U) ∈ (geoTransformAlong J R).cosupp ∧
              IsInvDomain ((k+1)+(m-n)) J' ∧ IsGeoTestTower J' R' ∧
              IsInvDomain ((k+1)+(m-n)) (geoTransformAlong J' R') ∧
              (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' R').cosupp ∧
              geoTransformAlong J' R'=markedPullback (m := m) q (geoTransformAlong J R) ∧
              (geoTransformAlong J' R').cosupp=q ⁻¹' (geoTransformAlong J R).cosupp ∧
              ∀ i : ℕ,∃ a : (split R' i).1 → (split R i).1,
                IsActualTowerPullback p (head R' i) (head R i) a ∧ IsGeoTestTower J' (head R' i) ∧
                geoTransformAlong J' (head R' i)=markedPullback (m := m) a (geoTransformAlong J (head R i)) ∧
                (geoTransformAlong J' (head R' i)).cosupp=a ⁻¹' (geoTransformAlong J (head R i)).cosupp := by
  obtain ⟨a,C,Z,π,_ha,hCne,hCL,hC,hR,hHS,hπ,hProper,hHolo,_hw,hSNC⟩ :=
    exists_original_current_compact_simultaneous_first_blowup hn (k+1) M hM T hc hK hne A hA
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  obtain ⟨Z',Q,g,h,_hg,_hLength,_hUniversal,hQ,_hWhole,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed (.step T C π hπ) hP
  have hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c :=
    fun y hy _hp c hc => (hCL hc).2 y hy
  refine ⟨a,C,Z,π,hπ,hCne,hC,hR,hHS,hP,hProper,hHolo,hSNC,Z',Q,g,h,hQ,?_⟩
  intro z hz hp
  exact prepared_current_companion_smooth_diagram hn M hM T hc C hC π hπ hCuts h z hz hp

end
end Hironaka.HironakaOriginalPreparedCompanionSmoothDiagram
