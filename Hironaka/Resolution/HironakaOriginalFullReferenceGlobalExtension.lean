/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullHistorySuperlevelsAnalytic
import Hironaka.Resolution.HironakaOriginalReferenceValueLocalBlowup
import Hironaka.Resolution.HironakaAnalyticCentreExtension
/-! Genuine BM97 13.4 full-reference dimensional extension, with original-only
local regularity/admissibility and WHOLE reduced ideal trace constructed internally.
Outside-window smoothification/simultaneous-chain HS/global scheduler remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullReferenceGlobalExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdealBiholomorphism
  HironakaOriginalFullHistorySuperlevelsAnalytic HironakaOriginalReferenceValueOpenNaturality
  HironakaOriginalReferenceValueLocalBlowup HironakaOriginalCompactUpperCutGlobalPhase
  HironakaEmbeddedDimensionParts HironakaDimensionGlobalComponents HironakaAnalyticCentreExtension
  AnalyticDimensionBasics GlobalComponents
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- ONLY actual original input internally supplies fixed-dimensional genuine
regularity and SAME-current-record admissibility of the real full reference cut. -/
theorem exists_original_reference_pure_admissible_window (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ (q : ℕ) (U : Opens Y),x ∈ U ∧ q ≤ n ∧
      (∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ U →
        (invFamily hn d).inv m T y ≤ (invFamily hn d).inv m T x) ∧
      (∀ y ∈ fullReferenceLocus hn d m T x,y ∈ U →
        RegularAtDim (n := n) (fullReferenceLocus hn d m T x) y q) ∧
      (MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong m T)).IsAdmissibleCentre
        ((Subtype.val : U → Y) ⁻¹' fullReferenceLocus hn d m T x) := by
  obtain ⟨W,hxW,hbound,_hne,hC,_hB,_hcos⟩ :=
    exists_original_reference_admissible_open hn d m h T hc x hx
  have hxC : (⟨x,hxW⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x := ⟨hx,le_rfl⟩
  obtain ⟨q,hq⟩ := hC.1.2 ⟨x,hxW⟩ hxC
  have hreg : RegularAtDim (n := n) (fullReferenceLocus hn d m T x) x q :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hq
  have hevW : ∀ᶠ y in 𝓝 x,y ∈ W := W.isOpen.mem_nhds hxW
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp
    (hevW.and (RegularPatchNeighborhood.eventually_regularAtDim hreg))
  let U : Opens Y := ⟨V,hVo⟩
  have hb : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ U →
      (invFamily hn d).inv m T y ≤ (invFamily hn d).inv m T x :=
    fun y hy hyU => hbound y hy (hV hyU).1
  have hAdm := (invFamily hn d).isInvValue.admissible m h T hc U
    ((invFamily hn d).inv m T x) hb
  have he : (Subtype.val : U → Y) ⁻¹' fullReferenceLocus hn d m T x=
      (Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        (invFamily hn d).inv m T y=(invFamily hn d).inv m T x} := by
    ext p
    constructor
    · rintro ⟨hp,hv⟩
      exact ⟨hp,(hb p hp p.property).antisymm hv⟩
    · rintro ⟨hp,hv⟩
      exact ⟨hp,by rw [hv]⟩
  exact ⟨q,U,hxV,hreg.1,hb,(fun y hy hyU => (hV hyU).2 hy),he.symm ▸ hAdm⟩

/-- Genuine global dimension-part extension and whole vanishing-ideal trace from
ONLY original inputs; no supplied local regularity, centre or extension. -/
theorem exists_original_full_reference_pure_global_extension (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ (q : ℕ) (U : Opens Y) (S : Set Y),q ≤ n ∧ x ∈ U ∧ x ∈ S ∧
      IsComplexAnalyticSubset (n := n) S ∧ IsPureDim (n := n) S q ∧
      S ⊆ fullReferenceLocus hn d m T x ∧
      S ∩ U=fullReferenceLocus hn d m T x ∩ U ∧
      (∀ y ∈ S,y ∈ U → RegularAtDim (n := n) S y q) ∧
      S=⋃₀ {B | B ∈ globalComponents (n := n) (fullReferenceLocus hn d m T x) ∧ IsPureDim (n := n) B q} ∧
      (MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong m T)).IsAdmissibleCentre
        ((Subtype.val : U → Y) ⁻¹' S) ∧
      (vanishingIdeal (n := n) S).IsCoherent ∧ (vanishingIdeal (n := n) S).zeroLocus=S ∧
      GermIdeal.pullback (m := n) (Subtype.val : U → Y) (vanishingIdeal (n := n) S)=
        windowIdeal hn d m T x U := by
  obtain ⟨q,U,hxU,hqn,_hb,hreg,hAdm⟩ :=
    exists_original_reference_pure_admissible_window hn d m h T hc x hx
  have hA : IsComplexAnalyticSubset (n := n) (fullReferenceLocus hn d m T x) :=
    original_all_depth_full_history_global_analytic hn d m h T hc ((invFamily hn d).inv m T x)
  let S := dimensionPart (n := n) (fullReferenceLocus hn d m T x) q
  have hSa : IsComplexAnalyticSubset (n := n) S := isComplexAnalyticSubset_dimensionPart hA q
  have hsub : S ⊆ fullReferenceLocus hn d m T x := dimensionPart_subset hA.isClosed q
  have htrace : S ∩ U=fullReferenceLocus hn d m T x ∩ U :=
    dimensionPart_inter_eq_of_regularOn hA.isClosed q hreg
  have hpre : (Subtype.val : U → Y) ⁻¹' S=(Subtype.val : U → Y) ⁻¹' fullReferenceLocus hn d m T x := by
    ext p
    constructor
    · exact fun hp => hsub hp
    · intro hp
      have hh : (p : Y) ∈ S ∩ U := htrace.symm ▸ (show (p : Y) ∈ fullReferenceLocus hn d m T x ∩ U from ⟨hp,p.property⟩)
      exact hh.1
  refine ⟨q,U,S,hqn,hxU,subset_closure (hreg x ⟨hx,le_rfl⟩ hxU),hSa,
    isPureDim_dimensionPart hA q,hsub,htrace,?_,dimensionPart_eq_sUnion_globalComponents hA q,
    hpre.symm ▸ hAdm,CartanIrreducible.cartanCoherence S hSa,
    BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hSa.isClosed,?_⟩
  · intro y hy hyU
    exact regularAtDim_dimensionPart_of_regularAtDim hA.isClosed (hreg y (hsub hy) hyU)
  · rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal,hpre]
    rfl

end
end Hironaka.HironakaOriginalFullReferenceGlobalExtension
