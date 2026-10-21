/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualClosedContactBlowupRestriction
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.Blowup.BlowupControlledTransform

/-!
# Whole controlled ideals on the SAME actual closed regular contact blowup

Actual native closed-contact geometry supplies the literal lower blowup.
Original admissibility, whole holomorphic product/power pullback and actual
invertible-factor uniqueness give its entire controlled ideal. No submersion
of a closed inclusion or colon-pullback compatibility is assumed.
Blueprint: `hironaka-actual-closed-contact-controlled-restriction-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualClosedContactControlledRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualClosedContactBlowupRestriction SubmanifoldChartedSpace
  BlowupStrictSubmanifold HironakaSmoothSubmersionOrderedChoiceImageTrace
  GermIdealPullbackCalculus IdealWeightPowers BlowupExceptionalDivisor
  BlowupControlledTransform

variable {n k : ℕ} {A Y : Type} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A]
  [IsComplexManifold n A] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {N : Set A} (hk : k≤n) (hNc : IsClosed N)
  (hN : ∀ x∈N,RegularAtDim (n := n) N x k) {D : Set N} {π : Y → A}
  (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π)

include hk hNc hN hπ
local notation "S" => geoStrictTransform π ((Subtype.val : N → A) '' D) N
local notation "σ" => restrictedProjection hNc D hπ

private theorem strict_inclusion_contMDiff :
    letI := strictChartedSpace hk hNc hN hπ
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ (Subtype.val : S → Y) := by
  let := strictChartedSpace hk hNc hN hπ
  exact contMDiff_val hk (fun y hy => regularAtDim_geoStrictTransform hπ hNc hN
    (fun _ ⟨x,_hx,he⟩ => he ▸ x.property) hy)

omit hNc in
/-- ORIGINAL ambient admissibility gives the genuine WHOLE lower centre-power inclusion. -/
theorem restricted_original_admissibility (I : GermIdeal n A) (μ : ℕ)
    (hle : I.Le (idealPow (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D)) μ)) :
    letI := chartedSpace hk hN
    (GermIdeal.pullback (m := k) (Subtype.val : N → A) I).Le
      (idealPow (vanishingIdeal (n := k) D) μ) := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  have h := pullback_le_pullback (m := k) (f := (Subtype.val : N → A)) hle
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (contMDiff_val hk hN)
    (isCoherent_vanishingIdeal_centre hπ) μ,centre_pullback hk hN D] at h
  exact h

/-- The ENTIRE original total transform square uses the SAME literal native contact projection. -/
theorem restricted_totalTransform (I : GermIdeal n A) (hI : I.IsCoherent) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    GermIdeal.pullback (m := k) (Subtype.val : S → Y)
      (GermIdeal.pullback (m := n) π I)=
        GermIdeal.pullback (m := k) σ
          (GermIdeal.pullback (m := k) (Subtype.val : N → A) I) := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  rw [←coherent_pullback_comp hπ.contMDiff (strict_inclusion_contMDiff hk hNc hN hπ) I hI,
    restrictedProjection_factor hNc hπ,
    coherent_pullback_comp (contMDiff_val hk hN)
      (restrictedProjection_contMDiff hk hNc hN hπ) I hI]

/-- The genuine SAME lower blowup has the exact WHOLE restricted exceptional ideal. -/
theorem restricted_exceptionalIdeal :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    ∀ (hD : IsClosedSubmanifold k D) (hDint : interior D=∅),
    GermIdeal.pullback (m := k) (Subtype.val : S → Y) (exceptionalDivisor hπ).ideal=
      (exceptionalDivisor (restrictedProjection_isBlowupAlong hk hNc hN D hπ hD hDint)).ideal := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  intro hD hDint
  rw [exceptionalDivisor_ideal,exceptionalDivisor_ideal,
    restricted_totalTransform hk hNc hN hπ _ (isCoherent_vanishingIdeal_centre hπ),
    centre_pullback hk hN D]

/-- EVERY entire exceptional power restricts to the SAME actual lower exceptional denominator. -/
theorem restricted_exceptionalIdeal_power (q : ℕ) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    ∀ (hD : IsClosedSubmanifold k D) (hDint : interior D=∅),
    GermIdeal.pullback (m := k) (Subtype.val : S → Y) (idealPow (exceptionalDivisor hπ).ideal q)=
      idealPow (exceptionalDivisor
        (restrictedProjection_isBlowupAlong hk hNc hN D hπ hD hDint)).ideal q := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  intro hD hDint
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow
    (strict_inclusion_contMDiff hk hNc hN hπ) (isCoherent_ideal (exceptionalDivisor hπ)) q,
    restricted_exceptionalIdeal hk hNc hN hπ hD hDint]

/-- Original admissibility and actual invertible-factor uniqueness prove WHOLE controlled ideal restriction. -/
theorem restricted_controlledTransform (I : GermIdeal n A) (hI : I.IsCoherent) (μ : ℕ)
    (hle : I.Le (idealPow (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D)) μ)) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    ∀ (hD : IsClosedSubmanifold k D) (hDint : interior D=∅),
    GermIdeal.pullback (m := k) (Subtype.val : S → Y) (controlledTransform hπ I μ)=
      controlledTransform (restrictedProjection_isBlowupAlong hk hNc hN D hπ hD hDint)
        (GermIdeal.pullback (m := k) (Subtype.val : N → A) I) μ := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  intro hD hDint
  have hσ := restrictedProjection_isBlowupAlong hk hNc hN D hπ hD hDint
  have hjS := strict_inclusion_contMDiff hk hNc hN hπ
  have hQ := isCoherent_controlledTransform hπ hI hle
  have hL := GermIdealPullbackCalculus.isCoherent_idealPow (isCoherent_ideal (exceptionalDivisor hπ)) μ
  apply eq_controlledTransform_of_eq_mul hσ (isCoherent_pullback hjS hQ)
  rw [←restricted_totalTransform hk hNc hN hπ I hI,
    pullback_eq_mul_controlledTransform hπ hI hle,
    HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hjS hL hQ,
    restricted_exceptionalIdeal_power hk hNc hN hπ μ hD hDint]

end
end Hironaka.HironakaActualClosedContactControlledRestriction
