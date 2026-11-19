/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSimultaneousHSAdmissibleCentre
import Hironaka.Resolution.HironakaOriginalFullValueVariationLocus
/-! Genuine compact-pure-space full-invariant bad-set selection and original
prefix extension preserving its ENTIRE actual good region. HS-only bad phases,
noncanonical invariant transport and general iteration remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalVariationPreservingSimultaneousCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaOriginalSimultaneousHSAdmissibleCentre HironakaOriginalFullValueVariationLocus
  HironakaOriginalFullHistorySuperlevelsAnalytic HironakaOriginalCompactUpperCutGlobalPhase
  HironakaHolomorphicJetChartInvariance HironakaActualReferenceHSSingularCentre
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  ResolutionDriver ResolutionInvariantDriver AnalyticDimensionBasics
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- ONLY actual compact analytic-subset geometry supplies the true restricted
full maximum and simultaneous-profile original-admissible centre internally. -/
theorem exists_original_compact_analytic_subset_simultaneous_centre (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    {K : Set Y} (hKa : IsComplexAnalyticSubset (n := n) K) (hK : IsCompact K) (hne : K.Nonempty)
    (hKP : K ⊆ (geoTransformAlong m T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (a : Y) (C : Set Y),a ∈ K ∧
      (∀ y ∈ K,(invFamily hn d).inv m T y≤(invFamily hn d).inv m T a) ∧
      C.Nonempty ∧ C ⊆ K ∧ (geoTransformAlong m T).IsAdmissibleCentre C ∧
      (∀ x ∈ C,(invFamily hn d).inv m T x=(invFamily hn d).inv m T a) ∧
      ∀ i,∀ x ∈ C,∀ ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ := by
  let R := invFamily hn d
  let P := geoTransformAlong m T
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcur := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  obtain ⟨b,hb,hmax⟩ := ((R.isInvValue.usc m h T hc).mono hKP).exists_isMaxOn hK hne
  let L := maxLocus (R.inv m T) K
  have hLb : b ∈ L := ⟨hb,hmax⟩
  have hLcut : L=K ∩ actualUpperCut R m T (R.inv m T b) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,hKP hx.1,hx.2 b hb⟩
    · rintro ⟨hxK,_hxP,hbx⟩
      exact ⟨hxK,fun y hy => (hmax y hy).trans hbx⟩
  have hLa : IsComplexAnalyticSubset (n := n) L := hLcut.symm ▸ hKa.inter
    (original_all_depth_full_history_global_analytic hn d m h T hc (R.inv m T b))
  have hLk : IsCompact L := hK.of_isClosed_subset hLa.isClosed (maxLocus_subset _ _)
  obtain ⟨a,ha,hSne,hSa,hSk,hSeq⟩ :=
    exists_actual_finite_compact_constant_hs_cut A hA hLa hLk ⟨b,hLb⟩
  let S := finiteReferenceHSCut A L a
  have hSL : S ⊆ L := fun _ hx => hx.1
  have hSP : S ⊆ P.cosupp := hSL.trans ((maxLocus_subset _ _).trans hKP)
  have hint : interior S=∅ := eq_empty_of_subset_empty
    ((interior_mono hSP).trans (interior_cosupp_eq_empty hcur).subset)
  let Q : MarkedIdeal n Y := ⟨univ,P.E,vanishingIdeal (n := n) S,1⟩
  have hQ : IsInvDomain n Q := HironakaEmbeddedBoundary.isInvDomain_boundary hSa hint hcur.isWellFormed.isSNCDivisor
  have hcos : Q.cosupp=S := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hSa.isClosed P.E
  let B := canonicalInvariant n
  have husc := B.isInvValue.usc Q hQ (.refl : BlowupTower Y Y) trivial
  rw [geoTransformAlong_refl] at husc
  obtain ⟨c,hcS,hcmax⟩ := husc.exists_isMaxOn (hcos.symm ▸ hSk) (hcos.symm ▸ hSne)
  let C := maxLocus (B.inv Q (.refl : BlowupTower Y Y)) Q.cosupp
  have hadm := B.isInvValue.isAdmissibleCentre_maxLocus hQ (.refl : BlowupTower Y Y) trivial trivial
  rw [geoTransformAlong_refl] at hadm
  have hCS : C ⊆ S := hcos ▸ hadm.2.1
  have hCL : C ⊆ L := hCS.trans hSL
  have hOrig : P.IsAdmissibleCentre C :=
    ⟨hadm.1,(hCL.trans (maxLocus_subset _ _)).trans hKP,hadm.2.2⟩
  refine ⟨a,C,ha.1,ha.2,⟨c,hcS,hcmax⟩,hCL.trans (maxLocus_subset _ _),hOrig,?_,?_⟩
  · intro x hx
    exact le_antisymm (ha.2 x (hCL hx).1) ((hCL hx).2 a ha.1)
  · intro i x hx ℓ
    have hh : x ∈ {x | x ∈ L ∧ ∀ i ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ} :=
      hSeq ▸ hCS hx
    exact hh.2 i ℓ

/-- The LITERAL full-R bad locus is computed and proved analytic/compact BEFORE
actual simultaneous original-admissible centre selection; no bad-set certificate. -/
theorem exists_original_actual_variation_simultaneous_centre (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := n) S) (hK : IsCompact S) {q : ℕ}
    (hpure : IsPureDim (n := n) S q) (hSP : S ⊆ (geoTransformAlong m T).cosupp)
    (hne : (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q).Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    let F := actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q
    IsComplexAnalyticSubset (n := n) F ∧ IsCompact F ∧ DimLE (n := n) F (q-1) ∧
      ∃ (a : Y) (C : Set Y),a ∈ F ∧
        (∀ y ∈ F,(invFamily hn d).inv m T y≤(invFamily hn d).inv m T a) ∧
        C.Nonempty ∧ C ⊆ F ∧ (geoTransformAlong m T).IsAdmissibleCentre C ∧
        (∀ x ∈ C,(invFamily hn d).inv m T x=(invFamily hn d).inv m T a) ∧
        ∀ i,∀ x ∈ C,∀ ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ := by
  dsimp only
  obtain ⟨hFa,hdF⟩ := original_full_value_variation_locus_analytic hn d m h T hc hS hpure hSP
  have hFk := hK.of_isClosed_subset hFa.isClosed (fun _ hx => hx.1)
  exact ⟨hFa,hFk,hdF,exists_original_compact_analytic_subset_simultaneous_centre hn d m h T hc
    hFa hFk hne (fun y hy => hSP hy.1) A hA⟩

/-- The SAME internally selected centre extends the SAME ORIGINAL test prefix,
with a REAL whole good-region inverse, actual map and ORIGINAL transformed SNC. -/
theorem exists_original_variation_preserving_simultaneous_blowup_prefix (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := n) S) (hK : IsCompact S) {q : ℕ}
    (hpure : IsPureDim (n := n) S q) (hSP : S ⊆ (geoTransformAlong m T).cosupp)
    (hne : (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q).Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    let F := actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q
    ∃ (a : Y) (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      a ∈ F ∧ C.Nonempty ∧ C ⊆ F ∧ (geoTransformAlong m T).IsAdmissibleCentre C ∧
      (∀ x ∈ C,(invFamily hn d).inv m T x=(invFamily hn d).inv m T a) ∧
      (∀ i,∀ x ∈ C,∀ ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower m (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π Fᶜ ∧ ((geoTransformAlong m T).geoTransform C π).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong m T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  dsimp only
  obtain ⟨_hFa,_hFk,_hdF,a,C,ha,_hmax,hCne,hCF,hCadm,hR,hHS⟩ :=
    exists_original_actual_variation_simultaneous_centre hn d m h T hc hS hK hpure hSP hne A hA
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcur := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (interior_cosupp_eq_empty hcur).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup C hCadm.1 hint
  have hGsub : (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q)ᶜ ⊆ Cᶜ :=
    fun _ hx hC => hx (hCF hC)
  have hisoC := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q)ᶜ := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hisoC.2.mono_left (preimage_mono hGsub)⟩
    · exact hisoC.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨y,_hy,hπy⟩ := hisoC.1.2.2 (hGsub hx)
      exact ⟨y,by change π y ∈ (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q)ᶜ; rwa [hπy],hπy⟩
  have hw := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hcur.isWellFormed hCadm hπ
  exact ⟨a,C,Z,π,hπ,ha,hCne,hCF,hCadm,hR,hHS,⟨ht,hCadm⟩,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hw,hw.isSNCDivisor⟩

end
end Hironaka.HironakaOriginalVariationPreservingSimultaneousCentre
