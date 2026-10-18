/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupStrictIdealControlled
import Hironaka.Support.UnitIdealCosupportExact
import Hironaka.Resolution.HironakaOriginalReferenceValueAuxiliaryMarked
/-! Genuine local full-reference admissible centre and actual whole auxiliary
unit transform. This reference-CUT ideal is not identified with the original
coefficient ideal. Global scheduling and transformed coefficient comparison OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalReferenceValueLocalBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HironakaOriginalReferenceValueOpenNaturality HironakaOriginalReferenceValueAuxiliaryMarked
  GermIdealOrder NormalCrossings SimultaneousNormalCrossings
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- ONLY original inputs internally construct the bounded original full-level centre
with genuine original-current AND same-boundary auxiliary admissibility. -/
theorem exists_original_reference_admissible_open (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧
      (∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ (invFamily hn d).inv m T x) ∧
      let C := (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x
      C.Nonempty ∧ (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)).IsAdmissibleCentre C ∧
      (referenceMarked hn d m T x W).IsAdmissibleCentre C ∧
      (referenceMarked hn d m T x W).cosupp=C := by
  let R := invFamily hn d
  let f := R.inv m T
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp (R.isInvValue.usc m h T hc x hx)
  let W : Opens Y := ⟨V,hVo⟩
  let C := (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x
  have hAdm := R.isInvValue.admissible m h T hc W (f x) (fun y hy hyW => hV hyW hy)
  have heq : C = (Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧ f y=f x} := by
    ext p
    constructor
    · rintro ⟨hp,hv⟩
      exact ⟨hp,(hV p.property hp).antisymm hv⟩
    · rintro ⟨hp,hv⟩
      exact ⟨hp,by change f x ≤ f p; rw [hv]⟩
  have hC : (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)).IsAdmissibleCentre C := by
    rw [heq]
    exact hAdm
  have hI : (vanishingIdeal (n := n) C).IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hC.1
  have hBcos : (referenceMarked hn d m T x W).cosupp=C := by
    change cosupport n univ (vanishingIdeal (n := n) C) 1=C
    rw [cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
      univ_inter,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hC.1.1]
  have hB : (referenceMarked hn d m T x W).IsAdmissibleCentre C := by
    refine ⟨hC.1,?_,hC.2.2⟩
    rw [hBcos]
  exact ⟨W,hxV,(fun y hy hyW => hV hyW hy),⟨⟨x,hxV⟩,hx,le_rfl⟩,hC,hB,hBcos⟩

/-- The SAME WHOLE reference vanishing ideal/mark1 record has actual controlled
and geometric UNIT ideals and empty cosupport along its real full centre. -/
theorem referenceMarked_geoTransform_unit_of_full_centre (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) (W : Opens Y)
    (hC : IsClosedSubmanifold n ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x))
    {Z : CMfd.{u} n} {π : Z → W}
    (hπ : IsBlowupAlong n ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) π) :
    BlowupControlledTransform.controlledTransform hπ (windowIdeal hn d m T x W) 1 = IdealWeightPowers.unitIdeal n Z ∧
    ((referenceMarked hn d m T x W).geoTransform ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) π).ideal=IdealWeightPowers.unitIdeal n Z ∧
    ((referenceMarked hn d m T x W).geoTransform ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) π).cosupp=∅ := by
  let C := (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x
  have hI : (windowIdeal hn d m T x W).IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hC
  have hunit : BlowupControlledTransform.controlledTransform hπ (windowIdeal hn d m T x W) 1 =
      IdealWeightPowers.unitIdeal n Z := by
    change BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := n) C) 1 = _
    rw [BlowupStrictIdeal.controlledTransform_vanishingIdeal hπ hC subset_rfl,
      BlowupStrictIdeal.geoStrictTransform_self]
    refine GermIdeal.ext (funext fun z => funext fun g => propext ⟨fun hg => hg.1,fun hg => ?_⟩)
    exact ⟨hg,Eventually.of_forall fun _ hz => hz.elim⟩
  have hgeo : ((referenceMarked hn d m T x W).geoTransform C π).ideal=IdealWeightPowers.unitIdeal n Z := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪 := referenceMarked hn d m T x W) rfl hI hπ]
    exact hunit
  refine ⟨hunit,hgeo,?_⟩
  change cosupport n _ ((referenceMarked hn d m T x W).geoTransform C π).ideal 1=∅
  rw [hgeo]
  exact cosupport_unitIdeal le_rfl

/-- ONLY original input constructs the actual SAME local reference centre and true
proper whole-complement isomorphism, auxiliary unit transform and ordered SNC. -/
theorem exists_original_reference_local_unit_blowup (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ (W : Opens Y),x ∈ W ∧ ∃ (Z : CMfd.{u} n) (π : Z → W),
      let C := (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x
      let J := MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)
      let B := referenceMarked hn d m T x W
      C.Nonempty ∧ J.IsAdmissibleCentre C ∧ B.IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π Cᶜ ∧ (B.geoTransform C π).ideal=IdealWeightPowers.unitIdeal n Z ∧
      (B.geoTransform C π).cosupp=∅ ∧
      IsSNCDivisor n (J.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  obtain ⟨W,hxW,_hbound,hCne,hCadm,hBadm,_hBcos⟩ := exists_original_reference_admissible_open hn d m h T hc x hx
  let C := (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x
  let J := MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong m T)
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hdW : IsInvDomain d J := InvDomainTowerAlong.isInvDomain_pullback_val W hd
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hdW).subset)
  obtain ⟨Z,π,hπ⟩ := ResolutionDriver.exists_blowup (Y := CMfd.of (n := n) W) C hCadm.1 hint
  obtain ⟨_hcontrolled,hunit,hcos⟩ := referenceMarked_geoTransform_unit_of_full_centre hn d m T x W hCadm.1 hπ
  have hE := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hdW.isWellFormed hCadm hπ).isSNCDivisor
  exact ⟨W,hxW,Z,π,hCne,hCadm,hBadm,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,
    hπ.contMDiff,BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ,hunit,hcos,hE⟩

end
end Hironaka.HironakaOriginalReferenceValueLocalBlowup
