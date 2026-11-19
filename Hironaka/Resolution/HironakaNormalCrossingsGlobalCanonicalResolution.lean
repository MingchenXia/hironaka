/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsCanonicalChartHistories
import Hironaka.Resolution.HironakaCanonicalWordHistoryUniqueness

/-!
# Actual global canonical resolution of original general normal-crossing carriers

Finite actual full-history recipes give finite attained coordinate maxima.
Internally produced actual chart histories make these values attained cofinal
bounds on the original whole cosupport. Hence the actual global maximum exists
at every prefix, and genuine strict drop/WF constructs a literal finite suffix.
No ambient or cosupport compactness, model/max/history certificate is assumed.
Blueprint: `hironaka-normal-crossings-global-canonical-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaNormalCrossingsGlobalCanonicalResolution
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq ResolutionDriver
  HironakaHomogeneousCanonicalTowerMaxima HironakaHomogeneousCanonicalNeighbourhoods
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsInitialFullMaximum HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsCanonicalChartHistories HironakaCanonicalWordHistoryUniqueness
  HironakaHomogeneousCanonicalResolution
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X Y Z : CMfd.{u} n}

private theorem nc_domain {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (hnk : n≤k) :
    IsInvDomain k (originalMarkedIdeal H) := by
  have h := isInvDomain_originalMarkedIdeal hH
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans hnk,hreg⟩

/-- The actual entire coordinate maxima which are attained at the given literal history length. -/
def coordinateMaximumCandidates (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (j : ℕ) : Set Λ :=
  {a | ∃ (S : Finset (Fin n)) (Y : CMfd.{u} n) (W : BlowupTower (CoordinateBase.{u} n) Y),
    W.length=j ∧ IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) W ∧
    ∃ x ∈ maxLocus (R.inv (coordinateMarked S) W) (geoTransformAlong (coordinateMarked S) W).cosupp,
      R.inv (coordinateMarked S) W x=a}

/-- Finite coordinate subsets and finite actual recipe words give finite ENTIRE attained candidates. -/
theorem finite_coordinate_maximum_candidates
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n≤k) (j : ℕ) :
    (coordinateMaximumCandidates R j).Finite := by
  let B (S : Finset (Fin n)) : Set Λ :=
    {a | ∃ (Y : CMfd.{u} n) (W : BlowupTower (CoordinateBase.{u} n) Y),W.length=j ∧
      IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) W ∧
      ∃ x ∈ maxLocus (R.inv (coordinateMarked S) W) (geoTransformAlong (coordinateMarked S) W).cosupp,
        R.inv (coordinateMarked S) W x=a}
  have hB (S : Finset (Fin n)) : (B S).Finite :=
    finite_attained_maximum_values R (coordinateMarked S)
      (nc_domain (X := CoordinateBase.{u} n) (coordinateCarrier_isNormalCrossings.{u} S) hnk) j
  have hUnion := Set.finite_iUnion hB
  convert hUnion using 1
  ext a
  simp only [coordinateMaximumCandidates,B,mem_ofPred_eq,mem_iUnion]

private theorem exists_attained_cofinal_candidate
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n≤k)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (T : BlowupTower X Y)
    (hcan : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp) :
    ∃ z ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp,
      R.inv (originalMarkedIdeal H) T z ∈ coordinateMaximumCandidates R T.length ∧
      R.inv (originalMarkedIdeal H) T y≤R.inv (originalMarkedIdeal H) T z := by
  obtain ⟨Q,Z,W,hmodel,hlen,e,hiso⟩ := exists_original_nc_chart_model_history R hnk hH T hcan (T.proj y)
  let p : openPreimage T Q.U := ⟨y,Q.hx⟩
  have hp := chart_history_cosupp_value R hnk hH Q T hcan W hmodel e hiso p
  have hne : (geoTransformAlong (coordinateMarked Q.S) W).cosupp.Nonempty := ⟨(e p).val,hp.1.mp hy⟩
  obtain ⟨z₀,hz₀⟩ := homogeneous_maxLocus_nonempty R hnk Q.S W hmodel hne
  obtain ⟨z,hzV,hzcos,hzvalue⟩ :=
    exists_value_representative_over_neighbourhood R hnk Q.S W hmodel Q.V Q.h0 z₀ hz₀.1
  let q : openPreimage W Q.V := ⟨z,hzV⟩
  let p' := e.symm q
  have hp' := chart_history_cosupp_value R hnk hH Q T hcan W hmodel e hiso p'
  have hp'cos : (p' : Y) ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp :=
    hp'.1.mpr (by simpa only [p',q,e.apply_symm_apply] using hzcos)
  have hp'val : R.inv (originalMarkedIdeal H) T p'=R.inv (coordinateMarked Q.S) W z := by
    simpa only [p',q,e.apply_symm_apply] using hp'.2 hp'cos
  refine ⟨p',hp'cos,?_,?_⟩
  · rw [hp'val,hzvalue]
    exact ⟨Q.S,Z,W,hlen,hmodel,z₀,hz₀,rfl⟩
  · calc
      _ = R.inv (coordinateMarked Q.S) W (e p) := hp.2 hy
      _ ≤ R.inv (coordinateMarked Q.S) W z₀ := hz₀.2 _ (hp.1.mp hy)
      _ = R.inv (originalMarkedIdeal H) T p' := hzvalue.symm.trans hp'val.symm

/-- Original general NC geometry ALONE ensures every nonterminal weak prefix has an ENTIRE attained maximum. -/
theorem nc_maxLocus_nonempty
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n≤k)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (T : BlowupTower X Y)
    (hcan : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T)
    (hne : (geoTransformAlong (originalMarkedIdeal H) T).cosupp.Nonempty) :
    (maxLocus (R.inv (originalMarkedIdeal H) T) (geoTransformAlong (originalMarkedIdeal H) T).cosupp).Nonempty := by
  let B := coordinateMaximumCandidates R T.length ∩
    (R.inv (originalMarkedIdeal H) T) '' (geoTransformAlong (originalMarkedIdeal H) T).cosupp
  have hB : B.Finite := (finite_coordinate_maximum_candidates R hnk T.length).subset inter_subset_left
  have hBne : B.Nonempty := by
    obtain ⟨y,hy⟩ := hne
    obtain ⟨z,hz,hcand,_hle⟩ := exists_attained_cofinal_candidate R hnk hH T hcan y hy
    exact ⟨_,hcand,z,hz,rfl⟩
  obtain ⟨a,ha,hmax⟩ := Set.exists_max_image B id hB hBne
  obtain ⟨z,hz,he⟩ := ha.2
  refine ⟨z,hz,?_⟩
  intro y hy
  obtain ⟨q,hq,hcand,hle⟩ := exists_attained_cofinal_candidate R hnk hH T hcan y hy
  exact hle.trans ((hmax _ ⟨hcand,q,hq,rfl⟩).trans_eq he.symm)

/-- The actual original prefix internally supplies a genuine blowup of its nonempty entire maximum. -/
theorem exists_nc_canonical_successor
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n≤k)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (T : BlowupTower X Y)
    (hcan : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T)
    (hne : (geoTransformAlong (originalMarkedIdeal H) T).cosupp.Nonempty) :
    ∃ C : Set Y,C.Nonempty ∧ C=maxLocus (R.inv (originalMarkedIdeal H) T)
      (geoTransformAlong (originalMarkedIdeal H) T).cosupp ∧
      ∃ Z : CMfd.{u} n,∃ π : Z → Y,∃ hπ : IsBlowupAlong n C π,
        IsGeoTestTower (originalMarkedIdeal H) (.step T C π hπ) ∧
        IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) (.step T C π hπ) := by
  let M := originalMarkedIdeal H
  have hdom := nc_domain hH hnk
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  let C := maxLocus (R.inv M T) (geoTransformAlong M T).cosupp
  have hCne := nc_maxLocus_nonempty R hnk hH T hcan hne
  have hC := R.isInvValue.isAdmissibleCentre_maxLocus hdom T hcan ht
  have hCint : interior C=∅ := ResolutionInvariantDriver.interior_maxLocus_eq_empty hdom T ht (R.inv M T)
  obtain ⟨Z,hZtop,hZchart,hZcm,π,hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC.1 hCint
  let := hZtop
  let := hZchart
  let := hZcm
  exact ⟨C,hCne,rfl,CMfd.of (n := n) Z,π,hπ,⟨ht,hC⟩,⟨hcan,Or.inr rfl⟩⟩

/-- A genuine literal finite appended suffix resolves the SAME original general NC datum. -/
theorem exists_nc_resolution_suffix [WellFoundedLT Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n≤k)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (T : BlowupTower X Y)
    (hseg : IsCanonicalSegment (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T) :
    ∃ Z : CMfd.{u} n,∃ U : BlowupTower Y Z,
      IsCanonicalSegment (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) (T.append U) ∧
      IsGeoResolution (originalMarkedIdeal H) (T.append U) := by
  let M := originalMarkedIdeal H
  have hdom := nc_domain hH hnk
  suffices h : ∀ a : Λ,∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonicalSegment M (R.inv M) T →
      (∀ y ∈ (geoTransformAlong M T).cosupp,R.inv M T y≤a) →
      ∃ Z : CMfd.{u} n,∃ U : BlowupTower Y Z,
        IsCanonicalSegment M (R.inv M) (T.append U) ∧ IsGeoResolution M (T.append U) by
    have hcan := ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv M) T hseg
    by_cases hne : (geoTransformAlong M T).cosupp.Nonempty
    · obtain ⟨x,hx,hmax⟩ := nc_maxLocus_nonempty R hnk hH T hcan hne
      exact h _ T hseg hmax
    · exact ⟨Y,.refl,hseg,R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan,
        not_nonempty_iff_eq_empty.mp hne⟩
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    intro Y T hseg ha
    have hcan := ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv M) T hseg
    have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
    by_cases hne : (geoTransformAlong M T).cosupp.Nonempty
    · obtain ⟨C,hCne,rfl,Z,π,hπ,htest',hcan'⟩ :=
        exists_nc_canonical_successor R hnk hH T hcan hne
      let C := maxLocus (R.inv M T) (geoTransformAlong M T).cosupp
      let T' := BlowupTower.step T C π hπ
      have hseg' : IsCanonicalSegment M (R.inv M) T' := ⟨hseg,hCne,rfl⟩
      by_cases hne' : (geoTransformAlong M T').cosupp.Nonempty
      · obtain ⟨z,hz,hzmax⟩ := nc_maxLocus_nonempty R hnk hH T' hcan' hne'
        obtain ⟨x,hx⟩ := hCne
        have hlt : R.inv M T' z<a :=
          (value_lt_old_maximum_after_blowup R M hdom T hcan hx π hπ z hz).trans_le (ha x hx.1)
        obtain ⟨W,V,hsegV,hresV⟩ := ih _ hlt T' hseg' hzmax
        let P : BlowupTower Y Z := .step .refl C π hπ
        have happend : T.append (P.append V)=T'.append V := by
          rw [←BlowupTower.append_assoc]
          rfl
        exact ⟨W,P.append V,happend.symm ▸ hsegV,happend.symm ▸ hresV⟩
      · exact ⟨Z,.step .refl C π hπ,hseg',htest',not_nonempty_iff_eq_empty.mp hne'⟩
    · exact ⟨Y,.refl,hseg,htest,not_nonempty_iff_eq_empty.mp hne⟩

/-- Original NC data ONLY produce a finite actual canonicalInvariant n resolution, without compactness. -/
theorem exists_canonicalInvariant_nc_resolution
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∃ Y : CMfd.{u} n,∃ T : BlowupTower X Y,
      IsCanonicalSegment (originalMarkedIdeal H)
        ((CanonicalCentres.canonicalInvariant.{u} n).inv (originalMarkedIdeal H)) T ∧
      IsGeoResolution (originalMarkedIdeal H) T := by
  obtain ⟨Y,T,hseg,hres⟩ := exists_nc_resolution_suffix
    (CanonicalCentres.canonicalInvariant.{u} n) le_rfl hH .refl trivial
  exact ⟨Y,T,by simpa only [BlowupTower.refl_append] using hseg,
    by simpa only [BlowupTower.refl_append] using hres⟩

end
end Hironaka.HironakaNormalCrossingsGlobalCanonicalResolution
