/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCompactUpperCutGlobalPhase
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Analytic.ProperMappingTheorem
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
/-! Actual finite canonical centre images give BOTH full-threshold directions
and genuine analytic sets. Original-only arbitrary GLOBAL full thresholds at
REFLEXIVE histories follow from actual canonical local terminal constructors.
Arbitrary retained-prefix local continuation/coefficient semicoherence OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalFiniteCentreImageSuperlevels
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres HironakaOriginalCompactUpperCutGlobalPhase
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- BOTH literal whole-cut directions under the SAME actual original step. -/
theorem canonical_step_cut_eq_centre_union_image
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (b : Λ)
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hc : IsCanonical m (R.inv m) (.step T C π hπ)) :
    actualUpperCut R m T b=(C ∩ actualUpperCut R m T b) ∪ π '' actualUpperCut R m (.step T C π hπ) b := by
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hc.1
  have hw := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht).isWellFormed
  ext x
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · exact Or.inl ⟨hxC,hx⟩
    · obtain ⟨z,rfl⟩ := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ x
      have hz : z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp :=
        (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong m T)
          hw.isClosedSubmanifold_N.1 (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hw.isCoherent hg)
          hπ hxC).mpr hx.1
      have hv := (stepDrop_of_isInvValue R.isInvValue h T C π hπ hc z hz).2.2 hxC
      have hv' : R.inv m (.step T C π hπ) z=R.inv m T (π z) := hv
      refine Or.inr ⟨z,⟨hz,?_⟩,rfl⟩
      rw [hv']
      exact hx.2
  · rintro (hx | ⟨z,hz,rfl⟩)
    · exact hx.2
    · have hd := stepDrop_of_isInvValue R.isInvValue h T C π hπ hc z hz.1
      have hle : R.inv m (.step T C π hπ) z ≤ R.inv m T (π z) := by
        by_cases hp : π z ∈ C
        · exact (hd.2.1 hp).le
        · exact (hd.2.2 hp).le
      exact ⟨hd.1,hz.2.trans hle⟩

/-- Genuine actual canonicality makes the selected centre whole or empty,
BEFORE any desired full-cut analyticity is known. -/
theorem canonical_selected_centre_analytic
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ)
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hc : IsCanonical m (R.inv m) (.step T C π hπ)) :
    IsComplexAnalyticSubset (n := n) (C ∩ actualUpperCut R m T b) := by
  by_cases hne : (C ∩ actualUpperCut R m T b).Nonempty
  · obtain ⟨x,hxC,hx⟩ := hne
    have hC : C=maxLocus (R.inv m T) (geoTransformAlong m T).cosupp := by
      rcases hc.2 with he | he
      · exact False.elim (by rw [he] at hxC; exact hxC)
      · exact he
    have heq : C ∩ actualUpperCut R m T b=C := inter_eq_left.mpr (fun y hy => by
      have hyM : y ∈ maxLocus (R.inv m T) (geoTransformAlong m T).cosupp := hC ▸ hy
      exact ⟨hyM.1,hx.2.trans (hyM.2 x hx.1)⟩)
    rw [heq]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact isComplexAnalyticSubset_empty

/-- Real finite-tower recursion of selected ACTUAL centre images. -/
def selectedTailCentreImages (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ) :
    {Z : CMfd.{u} n} → BlowupTower Y Z → Set Y
  | _, .refl => ∅
  | _, .step S C _ _ => selectedTailCentreImages R m T b S ∪
    S.proj '' (C ∩ actualUpperCut R m (T.append S) b)

/-- BOTH full-threshold directions equal the ACTUAL finite selected centre
images plus the genuine original final-cut projection image. -/
theorem full_cut_eq_selected_images_union_final_image
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (b : Λ) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),IsCanonical m (R.inv m) (T.append S) →
      actualUpperCut R m T b=selectedTailCentreImages R m T b S ∪ S.proj '' actualUpperCut R m (T.append S) b
  | _, .refl, _ => by simp only [selectedTailCentreImages,BlowupTower.append_refl,BlowupTower.proj_refl,image_id,empty_union]
  | _, .step S C π hπ, hc => by
    rw [full_cut_eq_selected_images_union_final_image R m h T b S hc.1,
      canonical_step_cut_eq_centre_union_image R m h (T.append S) b hπ hc,
      image_union,image_image]
    exact (union_assoc _ _ _).symm

/-- Actual closed analytic selected centres and genuine proper projections,
not a supplied analytic-cut certificate, produce the true finite union. -/
theorem selectedTailCentreImages_analytic
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),IsCanonical m (R.inv m) (T.append S) →
      IsComplexAnalyticSubset (n := n) (selectedTailCentreImages R m T b S)
  | _, .refl, _ => isComplexAnalyticSubset_empty
  | _, .step S C π hπ, hc => by
    have hs := canonical_selected_centre_analytic R m (T.append S) b hπ hc
    have himg := ProperMappingTheorem.isComplexAnalyticSubset_image S.contMDiff_proj hs
      (fun K hK => ((HironakaLocalPrincipalization.isProperMap_proj S).isCompact_preimage hK).inter_left hs.isClosed)
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (selectedTailCentreImages_analytic R m T b S hc.1) himg

/-- Any ACTUAL original finite canonical erasure internally produces full-cut
analyticity from real centres/images; no analytic or compactness premise. -/
theorem full_cut_analytic_of_actual_erasure
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (b : Λ)
    (S : BlowupTower Y Z) (hc : IsCanonical m (R.inv m) (T.append S))
    (hclear : actualUpperCut R m (T.append S) b=∅) :
    IsComplexAnalyticSubset (n := n) (actualUpperCut R m T b) := by
  have he := full_cut_eq_selected_images_union_final_image R m h T b S hc
  rw [hclear,image_empty,union_empty] at he
  rw [he]
  exact selectedTailCentreImages_analytic R m T b S hc

/-- Arbitrary fixed full thresholds obey the TRUE original open value law,
with both genuine cosupport directions at the SAME retained history. -/
theorem actual_upper_cut_open_preimage
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (U : Opens X)
    (T : BlowupTower X Y) (hc : IsCanonical m (R.inv m) T) (b : Λ) :
    actualUpperCut R (pullback (Subtype.val : U → X) m) (restrict U T) b=
      (Subtype.val : openPreimage T U → Y) ⁻¹' actualUpperCut R m T b := by
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcos := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U T ht
  ext p
  constructor
  · intro hp
    have hpU := hp.1
    rw [hcos] at hpU
    have hv := R.isInvValue.restrictOpen m h U T hc p hpU
    have hv' : R.inv (pullback (Subtype.val : U → X) m) (restrict U T) p=R.inv m T (p : Y) := hv
    refine ⟨hpU,?_⟩
    have hb := hp.2
    change b ≤ R.inv (pullback (Subtype.val : U → X) m) (restrict U T) p at hb
    rw [hv'] at hb
    exact hb
  · intro hp
    have hpU : p ∈ (geoTransformAlong (pullback (Subtype.val : U → X) m) (restrict U T)).cosupp := by
      rw [hcos]
      exact hp.1
    have hv := R.isInvValue.restrictOpen m h U T hc p hp.1
    have hv' : R.inv (pullback (Subtype.val : U → X) m) (restrict U T) p=R.inv m T (p : Y) := hv
    refine ⟨hpU,?_⟩
    rw [hv']
    exact hp.2

/-- ONLY original domain and the genuine canonical local driver internally
supply all actual erasing towers for arbitrary GLOBAL REFLEXIVE full thresholds. -/
theorem reflexive_full_upper_cut_global_analytic [WellFoundedLT Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (b : Λ) :
    IsComplexAnalyticSubset (n := n) (actualUpperCut R m (.refl : BlowupTower X X) b) := by
  intro x
  obtain ⟨U,hxU,Y,T,hc,hr⟩ := HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical R h
    (K := ({x} : Set X)) isCompact_singleton
  let M := pullback (Subtype.val : U → X) m
  have hM := InvDomainTowerAlong.isInvDomain_pullback_val U h
  have hclear : actualUpperCut R M T b=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hh := hz.1
    rw [hr.2] at hh
    exact hh
  have hc' : IsCanonical M (R.inv M) ((.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)).append T) := by
    simpa only [BlowupTower.refl_append] using hc
  have hclear' : actualUpperCut R M ((.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)).append T) b=∅ := by
    simpa only [BlowupTower.refl_append] using hclear
  have ha := full_cut_analytic_of_actual_erasure R M hM (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) b T hc' hclear'
  have he := actual_upper_cut_open_preimage R m h U (.refl : BlowupTower X X) trivial b
  have hpre : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → X) ⁻¹' actualUpperCut R m (.refl : BlowupTower X X) b) := he ▸ ha
  let p : U := ⟨x,hxU (mem_singleton x)⟩
  obtain ⟨P⟩ := hpre p
  exact ⟨AnalyticSubsetOpens.presentationOfPreimageVal p P⟩

/-- ONLY actual original all-depth input: ANY full initial threshold is
GLOBAL analytic. Arbitrary nonreflexive ORIGINAL history is not re-based. -/
theorem original_reflexive_arbitrary_full_threshold_global_analytic (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (b : ValTy d) :
    IsComplexAnalyticSubset (n := n) (actualUpperCut (invFamily hn d) m (.refl : BlowupTower X X) b) :=
  reflexive_full_upper_cut_global_analytic (invFamily hn d) m h b

end
end Hironaka.HironakaOriginalFiniteCentreImageSuperlevels
