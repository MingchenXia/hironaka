/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSimultaneousCompanionTestStep
/-! The actual NEW order-run companion after a simultaneous preparation step:
true run increment/reset before genuine TEST, current domain and current point. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedCurrentCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue GeneralCompare GeneralCanonicalTail HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime
  HironakaOriginalFullCutCompanionTestStep HironakaOriginalSimultaneousHSAdmissibleCentre
  HironakaHolomorphicJetChartInvariance ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

/-- True run increment or true reset, before identifying the actual computed
new companion TEST; no canonicality of the next upper step is inferred. -/
theorem current_compAt_test_after_full_cut
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c)
    (z : Z) (hp : 0<nmOrd (geoTransformAlong M (.step T C π hπ)) z) :
    let P := .step T C π hπ
    let q := nmOrd (geoTransformAlong M P) z
    let r := regimeRun (OrdRegime M q) P z
    let H := head P r
    let S := tail P r
    let W := ordMask (geoTransformAlong M H) q
    let J := compAt M q H
    let R := restrict W S
    IsGeoTestTower J R := by
  dsimp only
  let q := nmOrd (geoTransformAlong M (.step T C π hπ)) z
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  by_cases hOld : OrdRegime M q T (π z)
  · have hpOld : 0<nmOrd (geoTransformAlong M T) (π z) := by rw [hOld.2]; exact hp
    have hTest := (original_full_value_cut_compAt_test hn M hM T hT hc (π z)
      hOld.1 hpOld C hC π hπ (hCuts (π z) hOld.1 hpOld)).1
    rw [regimeRun_step_of (OrdRegime M q) T C π hπ hOld]
    rw [hOld.2] at hTest
    exact hTest
  · rw [regimeRun_step_of_not (OrdRegime M q) T C π hπ hOld]
    trivial

/-- Only original current membership is assumed; actual current COMPANION
membership is constructed after the genuine newly computed TEST and domains. -/
theorem current_compAt_data_after_full_cut
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M (.step T C π hπ)) z) :
    let P := .step T C π hπ
    let q := nmOrd (geoTransformAlong M P) z
    let r := regimeRun (OrdRegime M q) P z
    let H := head P r
    let S := tail P r
    let W := ordMask (geoTransformAlong M H) q
    let J := compAt M q H
    let R := restrict W S
    IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
        ∃ hp : S.proj z ∈ W,(⟨z,hp⟩ : openPreimage S W) ∈ (geoTransformAlong J R).cosupp := by
  dsimp only
  let P : BlowupTower X Z := .step T C π hπ
  let q := nmOrd (geoTransformAlong M P) z
  let r := regimeRun (OrdRegime M q) P z
  let H := head P r
  let S := tail P r
  let W := ordMask (geoTransformAlong M H) q
  let J := compAt M q H
  let R := restrict W S
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M P := ⟨hT,hC⟩
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M P r).mp hP
  have hJ := isInvDomain_compAt hn hp H (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM H hH)
  have hMax := isMaximalOrderAlong_compAt hn q H
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM H hH)
  have hTest := current_compAt_test_after_full_cut hn M hM T hc C hC π hπ hCuts z hp
  have hMask : S.proj z ∈ W := (proj_tail_mem_ordMask hn hM P hP hz (o := q) rfl).2
  have hPoint : (⟨z,hMask⟩ : openPreimage S W) ∈ (geoTransformAlong J R).cosupp := by
    apply (mem_cosupp_compAt_iff hn hM hp H S hH hS hTest ⟨z,hMask⟩).mpr
    rw [←geoTransformAlong_head_tail M P r]
    exact ⟨hz,rfl⟩
  exact ⟨hJ,hMax,hTest,InvDomainTowerAlong.isInvDomain_geoTransformAlong hJ R hTest,hMask,hPoint⟩

/-- ONE original-input-only actual preparation step has genuine CURRENT
computed companion data at EVERY new positive cosupport point. -/
theorem exists_original_current_compact_prepared_companion_step
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (hK : IsCompact (geoTransformAlong M T).cosupp)
    (hne : (geoTransformAlong M T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (a : Y) (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      a ∈ maxLocus ((invFamily hn (k+1)).inv M T) (geoTransformAlong M T).cosupp ∧
      C.Nonempty ∧ C ⊆ maxLocus ((invFamily hn (k+1)).inv M T) (geoTransformAlong M T).cosupp ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      (∀ c ∈ C,(invFamily hn (k+1)).inv M T c=(invFamily hn (k+1)).inv M T a) ∧
      (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      ((geoTransformAlong M T).geoTransform C π).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      ∀ z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp,
        0<nmOrd (geoTransformAlong M (.step T C π hπ)) z →
      let P := .step T C π hπ
      let q := nmOrd (geoTransformAlong M P) z
      let r := regimeRun (OrdRegime M q) P z
      let H := head P r
      let S := tail P r
      let W := ordMask (geoTransformAlong M H) q
      let J := compAt M q H
      let R := restrict W S
      IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
        IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
          ∃ hp : S.proj z ∈ W,(⟨z,hp⟩ : openPreimage S W) ∈ (geoTransformAlong J R).cosupp := by
  obtain ⟨a,C,Z,π,ha,hCne,hCL,hC,hR,hHS,hπ,hProper,hHolo,hw,hSNC⟩ :=
    exists_original_current_compact_simultaneous_first_blowup hn (k+1) M hM T hc hK hne A hA
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c :=
    fun y hy _hp c hc => (hCL hc).2 y hy
  refine ⟨a,C,Z,π,hπ,ha,hCne,hCL,hC,hR,hHS,⟨hT,hC⟩,hProper,hHolo,hw,hSNC,?_⟩
  intro z hz hp
  exact current_compAt_data_after_full_cut hn M hM T hc C hC π hπ hCuts z hz hp

end
end Hironaka.HironakaOriginalPreparedCurrentCompanion
