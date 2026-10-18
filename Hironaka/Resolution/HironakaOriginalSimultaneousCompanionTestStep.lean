/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutCompanionTestStep
import Hironaka.Resolution.HironakaOriginalVariationPreservingSimultaneousCentre
/-! Actual simultaneous centres internally supply the ENTIRE full-value cut
before genuine old-run companion TESTs; no next canonicality is inferred. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSimultaneousCompanionTestStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  GeneralValue StepOneRegime ResolutionDriver ResolutionInvariantDriver HironakaHolomorphicJetChartInvariance
  HironakaOriginalFullCutCompanionTestStep HironakaOriginalSimultaneousHSAdmissibleCentre
  HironakaOriginalVariationPreservingSimultaneousCentre HironakaOriginalFullValueVariationLocus
  AnalyticDimensionBasics
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

private theorem actual_companion_data_of_full_cut
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (hT : IsGeoTestTower M T) (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M T) y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c) :
      let q := nmOrd (geoTransformAlong M T) y
      let r := regimeRun (OrdRegime M q) T y
      let W := ordMask (geoTransformAlong M (head T r)) q
      let J := compAt M q (head T r)
      let R := restrict W (.step (tail T r) C π hπ)
      IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
        ∀ z : openPreimage (.step (tail T r) C π hπ) W,
          z ∈ (geoTransformAlong J R).cosupp ↔
            z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp ∧
              nmOrd (geoTransformAlong M (.step T C π hπ)) z.val=q := by
  obtain ⟨hTest,hDomain⟩ := original_full_value_cut_compAt_test hn M hM T hT hc y hy hp C hC π hπ hCut
  exact ⟨hTest,hDomain,
    original_full_value_cut_compAt_next_cosupport hn M hM T hT hc y hy hp C hC π hπ hCut⟩

/-- ONE internally selected simultaneous step works for EVERY old positive
reference in the entire compact current cosupport, without next canonicality. -/
theorem exists_original_current_compact_simultaneous_companion_test_step
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
      ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      let q := nmOrd (geoTransformAlong M T) y
      let r := regimeRun (OrdRegime M q) T y
      let W := ordMask (geoTransformAlong M (head T r)) q
      let J := compAt M q (head T r)
      let R := restrict W (.step (tail T r) C π hπ)
      IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
        ∀ z : openPreimage (.step (tail T r) C π hπ) W,
          z ∈ (geoTransformAlong J R).cosupp ↔
            z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp ∧
              nmOrd (geoTransformAlong M (.step T C π hπ)) z.val=q := by
  obtain ⟨a,C,Z,π,ha,hCne,hCL,hC,hR,hHS,hπ,hProper,hHolo,hw,hSNC⟩ :=
    exists_original_current_compact_simultaneous_first_blowup hn (k+1) M hM T hc hK hne A hA
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  refine ⟨a,C,Z,π,hπ,ha,hCne,hCL,hC,hR,hHS,⟨hT,hC⟩,hProper,hHolo,hw,hSNC,?_⟩
  intro y hy hp
  have hCut : ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c :=
    fun c hc => (hCL hc).2 y hy
  exact actual_companion_data_of_full_cut hn M hM T hc hT y hy hp C hC π hπ hCut

/-- A true compact analytic subset supplies the whole-centre cut internally
for EVERY old positive reference in that subset; no outside reference is claimed. -/
theorem exists_original_compact_subset_simultaneous_companion_test_step
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    {K : Set Y} (hKa : IsComplexAnalyticSubset (n := n) K) (hK : IsCompact K)
    (hne : K.Nonempty) (hKP : K ⊆ (geoTransformAlong M T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (a : Y) (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      a ∈ K ∧ (∀ y ∈ K,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T a) ∧
      C.Nonempty ∧ C ⊆ K ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      (∀ c ∈ C,(invFamily hn (k+1)).inv M T c=(invFamily hn (k+1)).inv M T a) ∧
      (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      ((geoTransformAlong M T).geoTransform C π).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      ∀ y ∈ K,0<nmOrd (geoTransformAlong M T) y →
      let q := nmOrd (geoTransformAlong M T) y
      let r := regimeRun (OrdRegime M q) T y
      let W := ordMask (geoTransformAlong M (head T r)) q
      let J := compAt M q (head T r)
      let R := restrict W (.step (tail T r) C π hπ)
      IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
        ∀ z : openPreimage (.step (tail T r) C π hπ) W,
          z ∈ (geoTransformAlong J R).cosupp ↔
            z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp ∧
              nmOrd (geoTransformAlong M (.step T C π hπ)) z.val=q := by
  obtain ⟨a,C,ha,hMax,hCne,hCK,hC,hR,hHS⟩ :=
    exists_original_compact_analytic_subset_simultaneous_centre hn (k+1) M hM T hc hKa hK hne hKP A hA
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hC.2.1).trans (interior_cosupp_eq_empty hCurrent).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup C hC.1 hint
  have hw := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hCurrent.isWellFormed hC hπ
  refine ⟨a,C,Z,π,hπ,ha,hMax,hCne,hCK,hC,hR,hHS,⟨hT,hC⟩,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hw,hw.isSNCDivisor,?_⟩
  intro y hy hp
  have hCut : ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c := by
    intro c hc
    exact (hMax y hy).trans (hR c hc).ge
  exact actual_companion_data_of_full_cut hn M hM T hc hT y (hKP hy) hp C hC π hπ hCut

/-- The literal original full-value bad set internally supplies its actual
analytic compact subset and SAME proper preparation map preserving ALL good points. -/
theorem exists_original_actual_variation_companion_test_step
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := n) S) (hK : IsCompact S) {d : ℕ}
    (hPure : IsPureDim (n := n) S d) (hSP : S ⊆ (geoTransformAlong M T).cosupp)
    (hne : (actualValueVariationLocus (n := n) ((invFamily hn (k+1)).inv M T) S d).Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    let F := actualValueVariationLocus (n := n) ((invFamily hn (k+1)).inv M T) S d
    IsComplexAnalyticSubset (n := n) F ∧ IsCompact F ∧ DimLE (n := n) F (d-1) ∧
      ∃ (a : Y) (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
        a ∈ F ∧ C.Nonempty ∧ C ⊆ F ∧ (geoTransformAlong M T).IsAdmissibleCentre C ∧
        (∀ c ∈ C,(invFamily hn (k+1)).inv M T c=(invFamily hn (k+1)).inv M T a) ∧
        (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
        IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
        ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
        IsIsomorphismOver n π Fᶜ ∧
        ((geoTransformAlong M T).geoTransform C π).IsWellFormed ∧
        NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
          (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
        ∀ y ∈ F,0<nmOrd (geoTransformAlong M T) y →
          let q := nmOrd (geoTransformAlong M T) y
          let r := regimeRun (OrdRegime M q) T y
          let W := ordMask (geoTransformAlong M (head T r)) q
          let J := compAt M q (head T r)
          let R := restrict W (.step (tail T r) C π hπ)
          IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) ∧
            ∀ z : openPreimage (.step (tail T r) C π hπ) W,
              z ∈ (geoTransformAlong J R).cosupp ↔
                z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp ∧
                  nmOrd (geoTransformAlong M (.step T C π hπ)) z.val=q := by
  dsimp only
  let F := actualValueVariationLocus (n := n) ((invFamily hn (k+1)).inv M T) S d
  obtain ⟨hFa,hDim⟩ := original_full_value_variation_locus_analytic hn (k+1) M hM T hc hS hPure hSP
  have hFk := hK.of_isClosed_subset hFa.isClosed (fun _ hx => hx.1)
  obtain ⟨a,C,Z,π,hπ,ha,_hMax,hCne,hCF,hC,hR,hHS,hTest,hProper,hHolo,hw,hSNC,hComp⟩ :=
    exists_original_compact_subset_simultaneous_companion_test_step hn M hM T hc hFa hFk hne
      (fun y hy => hSP hy.1) A hA
  have hGsub : Fᶜ ⊆ Cᶜ := fun _ hx hmem => hx (hCF hmem)
  have hOff := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hIso : IsIsomorphismOver n π Fᶜ := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hOff.2.mono_left (preimage_mono hGsub)⟩
    · exact hOff.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨z,_hz,hπz⟩ := hOff.1.2.2 (hGsub hx)
      exact ⟨z,by change π z ∈ Fᶜ; rwa [hπz],hπz⟩
  exact ⟨hFa,hFk,hDim,a,C,Z,π,hπ,ha,hCne,hCF,hC,hR,hHS,hTest,hProper,hHolo,hIso,hw,hSNC,hComp⟩

end
end Hironaka.HironakaOriginalSimultaneousCompanionTestStep
