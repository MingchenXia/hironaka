/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPureBoundaryCanonicalPrefix
import Hironaka.Resolution.HironakaSmoothSubmersionRegularityReflection

/-!
# Whole intrinsic regular, singular and boundary-good sets under submersions

The existing actual forward and reverse regularity theorems give exact
whole regular loci. Openness supplies pure and boundary density; literal
set operations give the original singular, boundary-bad and genuine open
good-locus equalities. No ideal identification is used.

Empty sources are included without imposing a false global dimension bound.
Blueprint: `hironaka-original-smooth-intrinsic-regular-loci-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalSmoothIntrinsicRegularLoci

noncomputable section

open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRegularityReflection
  HironakaSmoothSubmersionNormalCrossings HironakaOriginalPureBoundaryCanonicalPrefix

variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {b : Y → X}

/-- Actual pointwise regularity is equivalent at precisely the true shifted dimension. -/
theorem regularAtDim_preimage_iff {y : Y}
    (hb : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b y)
    (W : Set X) (d : ℕ) :
    RegularAtDim (n := m) (b ⁻¹' W) y (d+(m-n)) ↔ RegularAtDim (n := n) W (b y) d := by
  constructor
  · intro h
    have hh := regularAtDim_of_preimage_submersion hb h
    simpa only [Nat.add_sub_cancel] using hh.2
  · exact regularAtDim_preimage_submersion hb

/-- Exact equality of the ENTIRE intrinsic regular loci, including empty sources. -/
theorem regularLocus_preimage_eq
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (d : ℕ) :
    regularLocus (n := m) (b ⁻¹' W) (d+(m-n)) = b ⁻¹' regularLocus (n := n) W d := by
  ext y
  exact regularAtDim_preimage_iff (hb.isSubmersionAt y) W d

/-- The original intrinsic pure-dimensional density is inherited by the actual source. -/
theorem pure_regular_density_preimage
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (d : ℕ) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    b ⁻¹' W ⊆ closure (regularLocus (n := m) (b ⁻¹' W) (d+(m-n))) := by
  have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
  intro y hy
  have hh := preimage_mono (f := b) hpure hy
  rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous,
    ← regularLocus_preimage_eq hb W d] at hh
  exact hh

/-- Literal original boundary-density pulls back to the literal source boundary list. -/
theorem boundary_density_preimage
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (E₀ : List (Set X)) (hdense : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    b ⁻¹' W ⊆ closure ((b ⁻¹' W) \ ⋃ H ∈ E₀.map (b ⁻¹' ·), H) := by
  have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
  intro y hy
  have hh := preimage_mono (f := b) hdense hy
  rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous,preimage_sdiff,
    HironakaEmbeddedBoundary.preimage_biUnion_list b E₀] at hh
  exact hh

/-- The intrinsic singular set is a genuine exact inverse image, with no ideal premise. -/
theorem singular_set_preimage_eq
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (d : ℕ) :
    b ⁻¹' (W \ regularLocus (n := n) W d) =
      (b ⁻¹' W) \ regularLocus (n := m) (b ⁻¹' W) (d+(m-n)) := by
  rw [preimage_sdiff,regularLocus_preimage_eq hb W d]

/-- Exact intrinsic bad sets for the original and the literal source boundary. -/
theorem boundary_bad_set_preimage_eq
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (d : ℕ) (E₀ : List (Set X)) :
    b ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) =
      ((b ⁻¹' W) \ regularLocus (n := m) (b ⁻¹' W) (d+(m-n))) ∪
        (b ⁻¹' W) ∩ ⋃ H ∈ E₀.map (b ⁻¹' ·), H := by
  rw [preimage_union,singular_set_preimage_eq hb W d,preimage_inter,
    HironakaEmbeddedBoundary.preimage_biUnion_list b E₀]

/-- Genuine intrinsic good OPENS agree after internally constructing source
analyticity and the literal pulled SNC family. -/
theorem boundary_good_open_preimage_eq
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (d : ℕ)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
    let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
    boundaryGoodOpen (b ⁻¹' W) hWaY (d+(m-n)) (E₀.map (b ⁻¹' ·)) hEY =
      (⟨b ⁻¹' (boundaryGoodOpen W hWa d E₀ hE₀ : Set X),
        (boundaryGoodOpen W hWa d E₀ hE₀).isOpen.preimage hb.contMDiff.continuous⟩ : Opens Y) := by
  dsimp only
  apply Opens.ext
  change (((b ⁻¹' W) \ regularLocus (n := m) (b ⁻¹' W) (d+(m-n))) ∪
      ⋃ H ∈ E₀.map (b ⁻¹' ·), H)ᶜ = b ⁻¹' ((W \ regularLocus (n := n) W d) ∪ ⋃ H ∈ E₀, H)ᶜ
  rw [preimage_compl,preimage_union,singular_set_preimage_eq hb W d,
    HironakaEmbeddedBoundary.preimage_biUnion_list b E₀]

end

end Hironaka.HironakaOriginalSmoothIntrinsicRegularLoci
