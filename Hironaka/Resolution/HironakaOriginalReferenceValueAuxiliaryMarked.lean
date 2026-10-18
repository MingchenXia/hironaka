/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalReferenceValueOpenNaturality
/-! Actual full-reference auxiliary marked inputs at every original depth,
with the SAME current ordered boundary and genuine whole open-record equality.
Complete source-first math precedes Lean. Global scheduling and transformed
coefficient semicoherent comparison remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalReferenceValueAuxiliaryMarked
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HironakaOriginalReferenceValueOpenNaturality HironakaOriginalAllDepthReferenceValueAnalytic
  GermIdealOrder NormalCrossings SimultaneousNormalCrossings InvDomainCompanion HironakaStepOneMemberLowerExtension
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual whole carrier, SAME current ordered boundary, genuine full-reference ideal and mark one. -/
def referenceMarked (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) (W : Opens Y) : MarkedIdeal n W :=
  ⟨univ,(MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)).E,
    windowIdeal hn d m T x W,1⟩

private theorem auxiliary_domain_of_actual_thin_current {M : CMfd.{u} n} {d : ℕ}
    {J : MarkedIdeal n M} (hJ : IsInvDomain d J) {I : GermIdeal n M}
    (hI : I.IsCoherent) (hsub : I.zeroLocus ⊆ J.cosupp) :
    IsInvDomain n (⟨univ,J.E,I,1⟩ : MarkedIdeal n M) := by
  have hi : interior I.zeroLocus=∅ := eq_empty_of_subset_empty
    ((interior_mono hsub).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hJ).subset)
  have hN : IsClosedSubmanifold n (univ : Set M) :=
    ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN,hI,hJ.isWellFormed.isSNCDivisor,isTransverse_univ_of_isSNCDivisor hJ.isWellFormed.isSNCDivisor⟩,
    (fun x _ => ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩),le_rfl,?_⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := 1) hI
  · intro O hO hOA
    change O ∩ univ ⊆ cosupport n univ I 1 at hOA
    change O ∩ univ=∅
    rw [inter_univ] at hOA ⊢
    rw [cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
      univ_inter] at hOA
    have hsubO : O ⊆ interior I.zeroLocus := by
      rw [← hO.interior_eq]
      exact interior_mono hOA
    rw [hi] at hsubO
    exact eq_empty_iff_forall_notMem.mpr fun y hy => hsubO hy
  · exact hx

private theorem actual_referenceMarked_domain (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (x : Y) (W : Opens Y)
    (hI : (windowIdeal hn d m T x W).IsCoherent)
    (hZ : (windowIdeal hn d m T x W).zeroLocus = (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) :
    IsInvDomain n (referenceMarked hn d m T x W) := by
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hdW := InvDomainTowerAlong.isInvDomain_pullback_val W hd
  change IsInvDomain n (⟨univ,(MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)).E,
    windowIdeal hn d m T x W,1⟩ : MarkedIdeal n (CMfd.of (n := n) W))
  apply auxiliary_domain_of_actual_thin_current (M := CMfd.of (n := n) W) hdW hI
  intro z hz
  have hz' : (z : Y) ∈ (geoTransformAlong m T).cosupp := (hZ ▸ hz).1
  rw [cosupp_pullback_val _ (fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg) W]
  exact hz'

private theorem actual_referenceMarked_cosupp (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) (W : Opens Y)
    (hI : (windowIdeal hn d m T x W).IsCoherent)
    (hZ : (windowIdeal hn d m T x W).zeroLocus = (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) :
    (referenceMarked hn d m T x W).cosupp = (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x := by
  change cosupport n univ (windowIdeal hn d m T x W) 1 = _
  rw [cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
    univ_inter,hZ]

/-- ONLY original input internally supplies a true all-depth full-reference auxiliary domain and ENTIRE cosupport dictionary. -/
theorem exists_original_referenceMarked_isInvDomain (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧ IsInvDomain n (referenceMarked hn d m T x W) ∧
      (referenceMarked hn d m T x W).cosupp = (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x := by
  obtain ⟨W,hxW,hI,hZ⟩ := exists_coherent_original_reference_superlevel hn d m h T hc x hx
  exact ⟨W,hxW,actual_referenceMarked_domain (X := X) (Y := Y) hn d m h T hc x W hI hZ,
    actual_referenceMarked_cosupp (X := X) (Y := Y) hn d m T x W hI hZ⟩

/-- Actual original controlled open-history equality and genuine whole ideal equality prove ALL FOUR marked fields. -/
theorem pullback_referenceMarked_open (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (U : Opens X)
    (x : openPreimage T U) (hx : (x : Y) ∈ (geoTransformAlong m T).cosupp) (W : Opens Y) :
    MarkedIdeal.pullback (traceMap (openPreimage T U) W) (referenceMarked hn d m T x W) =
      referenceMarked hn d (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) x
        (traceOpen (openPreimage T U) W) := by
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hgeo := geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T ht
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · change ((MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)).E.map
      (fun H => (traceMap (openPreimage T U) W) ⁻¹' H)) =
      (MarkedIdeal.pullback (Subtype.val : traceOpen (openPreimage T U) W → openPreimage T U)
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T))).E
    rw [hgeo]
    simp only [MarkedIdeal.pullback,List.map_map]
    rfl
  · change GermIdeal.pullback (m := n) (traceMap (openPreimage T U) W) (windowIdeal hn d m T x W) =
      windowIdeal hn d (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) x (traceOpen (openPreimage T U) W)
    unfold windowIdeal
    rw [pullback_trace_window_vanishingIdeal,full_reference_locus_open hn d m h T hc U x hx]
  · rfl

/-- ONLY original inputs internally supply both actual marked domains, BOTH entire cosupport dictionaries and whole open-record identity. -/
theorem exists_original_referenceMarked_open_domains (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧ IsInvDomain n (referenceMarked hn d m T x W) ∧
      (referenceMarked hn d m T x W).cosupp = (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x ∧
      ∀ (U : Opens X) (hxu : T.proj x ∈ U),
        let O := openPreimage T U
        let xU : O := ⟨x,hxu⟩
        let mU := MarkedIdeal.pullback (Subtype.val : U → X) m
        let B := referenceMarked hn d mU (restrict U T) xU (traceOpen O W)
        xU ∈ traceOpen O W ∧ IsInvDomain n B ∧
          B.cosupp = (Subtype.val : traceOpen O W → O) ⁻¹' fullReferenceLocus hn d mU (restrict U T) xU ∧
          MarkedIdeal.pullback (traceMap O W) (referenceMarked hn d m T x W)=B := by
  obtain ⟨W,hxW,hI,hZ,hwindows⟩ := exists_coherent_original_reference_open_windows (X := X) (Y := Y) hn d m h T hc x hx
  have hD := actual_referenceMarked_domain (X := X) (Y := Y) hn d m h T hc x W hI hZ
  refine ⟨W,hxW,hD,actual_referenceMarked_cosupp (X := X) (Y := Y) hn d m T x W hI hZ,?_⟩
  intro U hxu
  let O := openPreimage T U
  let xU : O := ⟨x,hxu⟩
  let mU := MarkedIdeal.pullback (Subtype.val : U → X) m
  obtain ⟨hxW',_hEq,hI',hZ'⟩ := hwindows U hxu
  have hU := InvDomainTowerAlong.isInvDomain_pullback_val U h
  have hcan : IsCanonical mU ((invFamily hn d).inv mU) (restrict U T) :=
    Seq.ResolutionInvariantExt.isCanonical_restrict (invFamily hn d) h U T hc
  exact ⟨hxW',actual_referenceMarked_domain (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) O) hn d mU hU (restrict U T) hcan xU (traceOpen O W) hI' hZ',
    actual_referenceMarked_cosupp (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) O) hn d mU (restrict U T) xU (traceOpen O W) hI' hZ',
    pullback_referenceMarked_open (X := X) (Y := Y) hn d m h T hc U xU hx W⟩

end
end Hironaka.HironakaOriginalReferenceValueAuxiliaryMarked
