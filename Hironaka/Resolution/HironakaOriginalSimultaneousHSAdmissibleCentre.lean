/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullHistorySuperlevelsAnalytic
import Hironaka.Resolution.HironakaActualCompactIntrinsicHSMaximum
/-! Actual original-admissible first centres constant for the full invariant and
ALL orders of a finite original HS family. No exceptional comparison or driver. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSimultaneousHSAdmissibleCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualCompactIntrinsicHSMaximum HironakaActualReferenceHSSingularCentre
  HironakaActualWholeAmbientHSSuperlevel HironakaHolomorphicJetChartInvariance
  HironakaOriginalFullHistorySuperlevelsAnalytic HironakaOriginalCompactUpperCutGlobalPhase
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  ResolutionDriver ResolutionInvariantDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Literal simultaneous componentwise ALL-order threshold on the actual set. -/
def finiteReferenceHSCut {ι : Type*} (A : ι → GermIdeal n M) (K : Set M) (a : M) : Set M :=
  {x | x ∈ K ∧ ∀ i ℓ,hilbertSamuelAt (A i) a ℓ ≤ hilbertSamuelAt (A i) x ℓ}

private theorem analytic_finite_intersection {ι : Type*} [Fintype ι]
    (S : ι → Set M) (hS : ∀ i,IsComplexAnalyticSubset (n := n) (S i)) :
    IsComplexAnalyticSubset (n := n) (⋂ i,S i) := by
  have hf : ∀ F : Finset ι,IsComplexAnalyticSubset (n := n) (⋂ i ∈ F,S i) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp
    | insert i F _ ih => simpa only [Finset.mem_insert,iInter_iInter_eq_or_left] using (hS i).inter ih
  simpa using hf Finset.univ

/-- Only original coherence and genuine compactness select a simultaneous
ALL-order profile before its actual analytic constant cut is constructed. -/
theorem exists_actual_finite_compact_constant_hs_cut {ι : Type*} [Fintype ι]
    (A : ι → GermIdeal n M) (hA : ∀ i,(A i).IsCoherent)
    {K : Set M} (hKa : IsComplexAnalyticSubset (n := n) K) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ a ∈ K,(finiteReferenceHSCut A K a).Nonempty ∧
      IsComplexAnalyticSubset (n := n) (finiteReferenceHSCut A K a) ∧
      IsCompact (finiteReferenceHSCut A K a) ∧
      finiteReferenceHSCut A K a={x | x ∈ K ∧ ∀ i ℓ,
        hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  let e := Fintype.equivFin ι
  let f : K → ℕ → ℕ := fun x k => if h : k.unpair.1<Fintype.card ι then
    hilbertSamuelAt (A (e.symm ⟨k.unpair.1,h⟩)) x k.unpair.2 else 0
  have hf : ∀ k,UpperSemicontinuous (fun x => f x k) := by
    intro k
    dsimp only [f]
    split_ifs with h
    · apply upperSemicontinuous_iff_isClosed_preimage.mpr
      intro r
      exact (isComplexAnalyticSubset_hilbertSamuelAt_superlevel
        (A (e.symm ⟨k.unpair.1,h⟩)) (hA _) k.unpair.2 r).isClosed.preimage continuous_subtype_val
    · exact continuous_const.upperSemicontinuous
  have hcode (x : K) (i : ι) (ℓ : ℕ) :
      f x (Nat.pair (e i).val ℓ)=hilbertSamuelAt (A i) x ℓ := by
    simp only [f,Nat.unpair_pair]
    rw [dif_pos (e i).isLt]
    exact congrArg (fun i => hilbertSamuelAt (A i) x ℓ) (e.symm_apply_apply i)
  obtain ⟨a,_hlex,ha⟩ := exists_actual_compact_countable_usc_lexmax f hf
  have hconst : ∀ x ∈ K,(∀ i ℓ,hilbertSamuelAt (A i) a ℓ≤hilbertSamuelAt (A i) x ℓ) ↔
      ∀ i ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ := by
    intro x hx
    constructor
    · intro hdom
      have hdomf : ∀ k,f a k≤f ⟨x,hx⟩ k := by
        intro k
        dsimp only [f]
        split_ifs with h
        · exact hdom (e.symm ⟨k.unpair.1,h⟩) k.unpair.2
        · exact le_rfl
      have heq := (ha ⟨x,hx⟩).mp hdomf
      intro i ℓ
      simpa only [hcode] using heq (Nat.pair (e i).val ℓ)
    · exact fun heq i ℓ => (heq i ℓ).ge
  have hS : finiteReferenceHSCut A K a=K ∩ ⋂ i,actualReferenceHSLocus (A i) a := by
    ext x
    simp only [finiteReferenceHSCut,mem_ofPred_eq,mem_inter_iff,mem_iInter,actualReferenceHSLocus,
      actualWholeAmbientHSSuperlevel]
  have hSa : IsComplexAnalyticSubset (n := n) (finiteReferenceHSCut A K a) := by
    rw [hS]
    exact hKa.inter (analytic_finite_intersection _ (fun i =>
      isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel (A i) (hA i) (hilbertSamuelAt (A i) a)))
  refine ⟨a,a.property,⟨a,a.property,fun _ _ => le_rfl⟩,hSa,
    hK.of_isClosed_subset hSa.isClosed (fun _ hx => hx.1),?_⟩
  ext x
  exact and_congr_right fun hx => hconst x hx

variable {X Y : CMfd.{u} n}

/-- ONLY original inputs select a genuine ORIGINAL-admissible first centre
constant for the original FULL invariant and EVERY finite-family HS order. -/
theorem exists_original_current_compact_simultaneous_first_centre (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (hK : IsCompact (geoTransformAlong m T).cosupp) (hne : (geoTransformAlong m T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (a : Y) (C : Set Y),a ∈ maxLocus ((invFamily hn d).inv m T) (geoTransformAlong m T).cosupp ∧
      C.Nonempty ∧ C ⊆ maxLocus ((invFamily hn d).inv m T) (geoTransformAlong m T).cosupp ∧
      (geoTransformAlong m T).IsAdmissibleCentre C ∧
      (∀ x ∈ C,(invFamily hn d).inv m T x=(invFamily hn d).inv m T a) ∧
      ∀ i,∀ x ∈ C,∀ ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ := by
  let R := invFamily hn d
  let P := geoTransformAlong m T
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcur := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  obtain ⟨b,hb,hmax⟩ := (R.isInvValue.usc m h T hc).exists_isMaxOn hK hne
  let L := maxLocus (R.inv m T) P.cosupp
  have hLb : b ∈ L := ⟨hb,hmax⟩
  have hLcut : L=actualUpperCut R m T (R.inv m T b) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,hx.2 b hb⟩
    · rintro ⟨hx,hbx⟩
      exact ⟨hx,fun y hy => (hmax y hy).trans hbx⟩
  have hLa : IsComplexAnalyticSubset (n := n) L := hLcut.symm ▸
    original_all_depth_full_history_global_analytic hn d m h T hc (R.inv m T b)
  have hLk : IsCompact L := hK.of_isClosed_subset hLa.isClosed (maxLocus_subset _ _)
  obtain ⟨a,ha,hSne,hSa,hSk,hSeq⟩ := exists_actual_finite_compact_constant_hs_cut A hA hLa hLk ⟨b,hLb⟩
  let S := finiteReferenceHSCut A L a
  have hSL : S ⊆ L := fun _ hx => hx.1
  have hSP : S ⊆ P.cosupp := hSL.trans (maxLocus_subset _ _)
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
  have hOrig : P.IsAdmissibleCentre C := ⟨hadm.1,hCL.trans (maxLocus_subset _ _),hadm.2.2⟩
  refine ⟨a,C,ha,⟨c,hcS,hcmax⟩,hCL,hOrig,?_,?_⟩
  · intro x hx
    exact le_antisymm (ha.2 x (hCL hx).1) ((hCL hx).2 a ha.1)
  · intro i x hx ℓ
    have hh : x ∈ {x | x ∈ L ∧ ∀ i ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ} :=
      hSeq ▸ hCS hx
    exact hh.2 i ℓ

/-- The SAME actual centre gives a real proper holomorphic ORIGINAL-admissible
blowup with true transformed wellformedness and ordered whole-boundary SNC. -/
theorem exists_original_current_compact_simultaneous_first_blowup (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (hK : IsCompact (geoTransformAlong m T).cosupp) (hne : (geoTransformAlong m T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n Y) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (a : Y) (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y),
      a ∈ maxLocus ((invFamily hn d).inv m T) (geoTransformAlong m T).cosupp ∧
      C.Nonempty ∧ C ⊆ maxLocus ((invFamily hn d).inv m T) (geoTransformAlong m T).cosupp ∧
      (geoTransformAlong m T).IsAdmissibleCentre C ∧
      (∀ x ∈ C,(invFamily hn d).inv m T x=(invFamily hn d).inv m T a) ∧
      (∀ i,∀ x ∈ C,∀ ℓ,hilbertSamuelAt (A i) x ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      ((geoTransformAlong m T).geoTransform C π).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong m T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  obtain ⟨a,C,ha,hCne,hCL,hCadm,hR,hHS⟩ :=
    exists_original_current_compact_simultaneous_first_centre hn d m h T hc hK hne A hA
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcur := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (interior_cosupp_eq_empty hcur).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup C hCadm.1 hint
  have hw := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hcur.isWellFormed hCadm hπ
  exact ⟨a,C,Z,π,ha,hCne,hCL,hCadm,hR,hHS,hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hw,hw.isSNCDivisor⟩

end
end Hironaka.HironakaOriginalSimultaneousHSAdmissibleCentre
