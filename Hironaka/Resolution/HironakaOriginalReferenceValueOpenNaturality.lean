/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAllDepthReferenceValueAnalytic
/-! Actual original full-reference ideals over true open histories and overlaps.
Only original inputs internally construct actual coherent windows. Complete
source-first math precedes code; transformed semicoherence/scheduler OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalReferenceValueOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism HironakaOriginalAllDepthReferenceValueAnalytic CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Literal attained FULL original reference locus on the entire actual final manifold. -/
def fullReferenceLocus (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) : Set Y :=
  {y | y ∈ (geoTransformAlong m T).cosupp ∧
    (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m T y}

/-- Actual vanishing ideal, with no unproved global coherence assertion. -/
def referenceIdeal (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) : GermIdeal n Y :=
  vanishingIdeal (n := n) (fullReferenceLocus hn d m T x)

/-- Actual vanishing ideal of the SAME full reference locus in a true window. -/
def windowIdeal (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) (W : Opens Y) : GermIdeal n W :=
  vanishingIdeal (n := n) ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x)

/-- True inverse image of one actual original open in another. -/
def traceOpen (O W : Opens Y) : Opens O :=
  ⟨(Subtype.val : O → Y) ⁻¹' (W : Set Y),W.isOpen.preimage continuous_subtype_val⟩

/-- The actual trace point lies in the SAME original window. -/
def traceMap (O W : Opens Y) : traceOpen O W → W :=
  fun p => ⟨((p : O) : Y),p.property⟩

/-- Genuine whole original cosupport and BOTH value equalities internally give the ENTIRE reference dictionary. -/
theorem full_reference_locus_open (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (U : Opens X)
    (x : openPreimage T U) (hx : (x : Y) ∈ (geoTransformAlong m T).cosupp) :
    fullReferenceLocus hn d (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) x =
      (Subtype.val : openPreimage T U → Y) ⁻¹' fullReferenceLocus hn d m T x := by
  let R := invFamily hn d
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcos := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U T ht
  have hxval := R.isInvValue.restrictOpen m h U T hc x hx
  ext y
  constructor
  · rintro ⟨hy,hv⟩
    have hy' : (y : Y) ∈ (geoTransformAlong m T).cosupp := by
      have hh : y ∈ (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong m T).cosupp := hcos ▸ hy
      exact hh
    have hyval := R.isInvValue.restrictOpen m h U T hc y hy'
    exact ⟨hy',by change R.inv m T x ≤ R.inv m T y; exact hxval ▸ (hyval ▸ hv)⟩
  · rintro ⟨hy,hv⟩
    have hy' : y ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T)).cosupp :=
      hcos.symm ▸ hy
    have hyval := R.isInvValue.restrictOpen m h U T hc y hy
    exact ⟨hy',by change R.inv _ (restrict U T) x ≤ R.inv _ (restrict U T) y; rw [hxval,hyval]; exact hv⟩

/-- BOTH actual vanishing-germ directions give whole ideal equality without global coherence. -/
theorem pullback_referenceIdeal_open (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (U : Opens X)
    (x : openPreimage T U) (hx : (x : Y) ∈ (geoTransformAlong m T).cosupp) :
    GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y) (referenceIdeal hn d m T x) =
      referenceIdeal hn d (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) x := by
  unfold referenceIdeal
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal,
    full_reference_locus_open hn d m h T hc U x hx]

/-- True source and target open inclusions make the actual trace map holomorphic. -/
theorem traceMap_holomorphic (O W : Opens Y) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (traceMap O W) := by
  apply (ContMDiff.subtypeVal_comp_iff _ _).mp
  change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun p : traceOpen O W => ((p : O) : Y))
  exact (contMDiff_subtype_val (U := O)).comp (contMDiff_subtype_val (U := traceOpen O W))

/-- Actual same-point composites give complete vanishing-ideal pullback, before any coherence claim. -/
theorem pullback_trace_window_vanishingIdeal (O W : Opens Y) (A : Set Y) :
    GermIdeal.pullback (m := n) (traceMap O W)
      (vanishingIdeal (n := n) ((Subtype.val : W → Y) ⁻¹' A)) =
    vanishingIdeal (n := n) ((Subtype.val : traceOpen O W → O) ⁻¹'
      ((Subtype.val : O → Y) ⁻¹' A)) := by
  rw [BlowupRestrictOpen.pullback_vanishingIdeal_opens W (traceMap O W) A]
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) O
    (Subtype.val : traceOpen O W → O) A
  change GermIdeal.pullback (m := n)
    ((Subtype.val : O → Y) ∘ (Subtype.val : traceOpen O W → O)) (vanishingIdeal (n := n) A) = _
  rw [← h]
  exact SmoothCentreHomogeneity.pullback_val_vanishingIdeal (traceOpen O W) _

private def overlapMap (W V : Opens Y) : (W ⊓ V : Opens Y) → W := fun p => ⟨p,p.property.1⟩
private def overlapMapRight (W V : Opens Y) : (W ⊓ V : Opens Y) → V := fun p => ⟨p,p.property.2⟩

/-- Complete actual ideal predicates agree on ANY true reference-window overlap. -/
theorem full_reference_window_overlap (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) (W V : Opens Y) :
    GermIdeal.pullback (m := n) (overlapMap W V) (windowIdeal hn d m T x W) =
      GermIdeal.pullback (m := n) (overlapMapRight W V) (windowIdeal hn d m T x V) := by
  unfold windowIdeal
  rw [BlowupRestrictOpen.pullback_vanishingIdeal_opens W (overlapMap W V),
    BlowupRestrictOpen.pullback_vanishingIdeal_opens V (overlapMapRight W V)]
  rfl

/-- ONLY original inputs internally construct a coherent window and EVERY true open-history comparison on its actual trace. -/
theorem exists_coherent_original_reference_open_windows (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧ (windowIdeal hn d m T x W).IsCoherent ∧
      (windowIdeal hn d m T x W).zeroLocus = (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x ∧
      ∀ (U : Opens X) (hxu : T.proj x ∈ U),
        let O := openPreimage T U
        let xU : O := ⟨x,hxu⟩
        let mU := MarkedIdeal.pullback (Subtype.val : U → X) m
        xU ∈ traceOpen O W ∧
        GermIdeal.pullback (m := n) (traceMap O W) (windowIdeal hn d m T x W) =
          windowIdeal hn d mU (restrict U T) xU (traceOpen O W) ∧
        (windowIdeal hn d mU (restrict U T) xU (traceOpen O W)).IsCoherent ∧
        (windowIdeal hn d mU (restrict U T) xU (traceOpen O W)).zeroLocus =
          (Subtype.val : traceOpen O W → O) ⁻¹' fullReferenceLocus hn d mU (restrict U T) xU := by
  obtain ⟨W,hxW,hI,hZ⟩ := exists_coherent_original_reference_superlevel hn d m h T hc x hx
  have hIw : (windowIdeal hn d m T x W).IsCoherent := hI
  have hZw : (windowIdeal hn d m T x W).zeroLocus =
      (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x := hZ
  refine ⟨W,hxW,hIw,hZw,?_⟩
  intro U hxu
  let O := openPreimage T U
  let xU : O := ⟨x,hxu⟩
  let mU := MarkedIdeal.pullback (Subtype.val : U → X) m
  have hset := full_reference_locus_open hn d m h T hc U xU hx
  have heq : GermIdeal.pullback (m := n) (traceMap O W) (windowIdeal hn d m T x W) =
      windowIdeal hn d mU (restrict U T) xU (traceOpen O W) := by
    unfold windowIdeal
    rw [pullback_trace_window_vanishingIdeal,hset]
  refine ⟨hxW,heq,heq ▸ GermIdealPullbackCalculus.isCoherent_pullback (traceMap_holomorphic O W) hIw,?_⟩
  change (windowIdeal hn d mU (restrict U T) xU (traceOpen O W)).zeroLocus =
    (Subtype.val : traceOpen O W → O) ⁻¹' fullReferenceLocus hn d mU (restrict U T) xU
  rw [← heq,BlowupExceptionalDivisor.zeroLocus_pullback (traceMap_holomorphic O W) hIw,hZw,hset]
  rfl

end
end Hironaka.HironakaOriginalReferenceValueOpenNaturality
