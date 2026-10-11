/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Resolution.HironakaNormalCrossingsTransversality
import Hironaka.Blowup.BlowupStrictIdealControlled

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Literal centre positions for an initially smooth analytic set

Blueprint `hironaka-smooth-stage-centres-extension.tex`. The genuine controlled
transform of a smooth vanishing ideal is the ideal of the current strict
transform at every recorded prefix. The proof uses the coordinate ideal
factorization and actual density, and produces centre containment rather than
requiring it. This is the smooth-input branch of G8, not the singular-input one.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaSmoothStageCenters

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
open HironakaStageCenters HironakaAdmissibleSequence RestrictEmptyTower

noncomputable section

variable {n : ℕ}

/-- A smooth initial set stays smooth at every prefix, and its actual current
controlled ideal equals its strict-transform ideal, when centres avoid a dense open part. -/
theorem smooth_strictTransform_and_ideal_geoTransformAlong_of_centresAvoid {X : CMfd.{u} n}
    {W : Set X} {E₀ : List (Set X)} (hW : IsClosedSubmanifold n W) (O : Opens X)
    (hdense : W ⊆ closure (W ∩ (O : Set X))) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T →
      CentresAvoid O T → IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).ideal =
        vanishingIdeal (n := n) (strictTransform n T.proj W)
  | _, .refl, _, _ => by
      simpa [strictTransform, exceptionalLocus_id, hW.1.closure_eq] using
        And.intro hW (rfl : vanishingIdeal (n := n) W = vanishingIdeal (n := n) W)
  | _, .step T C π hπ, hT, hO => by
      obtain ⟨hS, hI⟩ := smooth_strictTransform_and_ideal_geoTransformAlong_of_centresAvoid hW O hdense T hT.1 hO.1
      let 𝔪 : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
      have hcoh : 𝔪.ideal.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hW
      obtain ⟨hNT, hcT, _⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := 𝔪) rfl hcoh T hT.1
      have hcos : (geoTransformAlong 𝔪 T).cosupp = strictTransform n T.proj W := by
        rw [MarkedIdeal.cosupp, hNT, hI, d_geoTransformAlong]
        exact SmoothCentreLocus.cosupp_vanishingIdeal hS.1 (subset_univ _)
      have hCS : C ⊆ strictTransform n T.proj W := by
        rw [← hcos]
        exact hT.2.2.1
      have hSDense : strictTransform n T.proj W ⊆ closure (strictTransform n T.proj W \ C) := by
        have hD := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff T.contMDiff_proj hW.1
          (F := (O : Set X)ᶜ) (by simpa only [Set.sdiff_compl] using hdense)
        refine hD.trans (closure_mono ?_)
        rintro z ⟨hzS, hzO⟩
        exact ⟨hzS, fun hzC => Set.disjoint_left.mp hO.2 hzC (by simpa using hzO)⟩
      have hgeo : geoStrictTransform π C (strictTransform n T.proj W) =
          strictTransform n (.step T C π hπ : BlowupTower X _).proj W := by
        rw [BlowupTower.proj_step, StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
        exact BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hSDense
      refine ⟨?_, ?_⟩
      · rw [← hgeo]
        exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hS hCS
      · rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcT hπ,
          d_geoTransformAlong, hI]
        exact (BlowupStrictIdeal.controlledTransform_vanishingIdeal hπ hS hCS).trans (congrArg _ hgeo)

/-- For an initially smooth set with centres over its initial boundary, every
actual prefix is smooth and its next actual centre lies in the current set and current boundary. -/
theorem stageCentresSmoothInBoundary_of_isGeoTestTower {X : CMfd.{u} n}
    {W : Set X} {E₀ : List (Set X)} (hW : IsClosedSubmanifold n W) (O : Opens X)
    (hdense : W ⊆ closure (W ∩ (O : Set X))) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T →
      CentresAvoid O T → CentresOver (W ∩ ⋃ H ∈ E₀, H) T →
      StageCentres (fun S C => IsClosedSubmanifold n (strictTransform n S.proj W) ∧
        C ⊆ strictTransform n S.proj W ∩ ⋃ H ∈
          (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) T
  | _, .refl, _, _, _ => trivial
  | _, .step T _C _π _hπ, hT, hO, hF => by
      refine ⟨stageCentresSmoothInBoundary_of_isGeoTestTower hW O hdense T hT.1 hO.1 hF.1, ?_⟩
      obtain ⟨hS, hI⟩ := smooth_strictTransform_and_ideal_geoTransformAlong_of_centresAvoid hW O hdense T hT.1 hO.1
      let 𝔪 : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
      have hcoh : 𝔪.ideal.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hW
      have hNT := (pullback_eq_mul_geoTransformAlong (𝔪 := 𝔪) rfl hcoh T hT.1).1
      have hcos : (geoTransformAlong 𝔪 T).cosupp = strictTransform n T.proj W := by
        rw [MarkedIdeal.cosupp, hNT, hI, d_geoTransformAlong]
        exact SmoothCentreLocus.cosupp_vanishingIdeal hS.1 (subset_univ _)
      refine ⟨hS, fun c hc => ⟨?_, ?_⟩⟩
      · rw [← hcos]
        exact hT.2.2.1 hc
      · by_contra hcE
        exact notMem_initial_boundary_of_notMem_boundary 𝔪 T hcE (hF.2 hc).2

/-- Construct an actual boundary-resolution tower for a smooth compact analytic
set. Every recorded current strict transform is smooth and every actual centre
is contained in its intersection with the actual current SNC boundary. -/
theorem exists_tower_embeddedResolution_smooth_boundary_stage_centres {X : CMfd.{u} n}
    {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) (hW : IsClosedSubmanifold n W)
    (hK : IsCompact W) {d : ℕ} (hd : d < n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    {E₀ : List (Set X)} (hE₀ : NormalCrossings.IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
      IsAdmissibleBlowupSequence n X E₀ (W ∩ ⋃ H ∈ E₀, H) Y T.proj
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E ∧
      NormalCrossings.IsSNCDivisor n
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ x ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) x d) ∧
      NormalCrossings.HasNormalCrossings n (strictTransform n T.proj W)
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E ∧
      NormalCrossings.IsTransverse n (strictTransform n T.proj W)
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E ∧
      StageCentres (fun S C => IsClosedSubmanifold n (strictTransform n S.proj W) ∧
        C ⊆ strictTransform n S.proj W ∩ ⋃ H ∈
          (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) T := by
  let 𝔪 : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  have hpure : W ⊆ closure (regularLocus (n := n) W d) := fun x hx => subset_closure (hreg x hx)
  have hdom : ResolutionInvariantSpec.IsInvDomain n 𝔪 := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  have hcos : 𝔪.cosupp = W := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWa.isClosed E₀
  let O : Opens X := ⟨(⋃ H ∈ E₀, H)ᶜ,
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1).isOpen_compl⟩
  have hEO : ∀ H ∈ E₀, Disjoint H (O : Set X) := fun H hH =>
    disjoint_left.mpr fun x hxH hxO => hxO (mem_iUnion₂.mpr ⟨H, hH, hxH⟩)
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := by
    exact hE₀W
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hK)
  obtain ⟨Y, T, hT, hTO, hSM, hregS, hNC⟩ := HironakaEmbeddedBoundary.exists_tower_embedded_of_isCanonical
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n))
    hWa O hEO (fun x hx _ => hreg x hx) hdense hdom T₀ hcan₀ hres₀
  have hTF : CentresOver (W ∩ ⋃ H ∈ E₀, H) T := by
    refine HironakaEmbeddedBoundary.centresOver_of_inter_subset (F := 𝔪.cosupp) (G := (O : Set X)ᶜ)
      ?_ T (centresOver_cosupp 𝔪 hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent T hT)
      (centresOver_compl_of_centresAvoid O T hTO)
    rintro x ⟨hxW, hxE⟩
    rw [hcos] at hxW
    exact ⟨hxW, by simpa [O] using hxE⟩
  have hadm := isAdmissibleBlowupSequence_proj 𝔪 _ T hT hTF
  have hEsnc := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hdom.isWellFormed T hT).isSNCDivisor
  have hTr := HironakaNormalCrossingsTransversality.isTransverse_strictTransform_of_admissible hadm hE₀.1
    hWa.isClosed (hE₀W.trans (closure_mono (by
      rintro x ⟨hxW, hxE⟩
      exact ⟨hxW, fun h => h.elim hxE (fun h => hxE h.2)⟩))) hNC
  exact ⟨Y, T, hT, hadm, hEsnc, hSM, hregS, hNC, hTr,
    stageCentresSmoothInBoundary_of_isGeoTestTower hW O hdense T hT hTO hTF⟩

end

end Hironaka.HironakaSmoothStageCenters
