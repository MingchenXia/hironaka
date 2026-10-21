/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionPartResolution

/-! # Exact original pure empty-boundary and compact-ambient families
The entire accepted target-before-sources result is retained verbatim.
Blueprint: `hironaka-original-pure-canonical-specializations-extension.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace
universe u
namespace Hironaka.HironakaOriginalPureCanonicalSpecializations
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaOriginalCanonicalDimensionPartResolution
variable {n : ℕ} {X : CMfd.{u} n}

/-- Literal empty boundary retains the SAME target/source exact support fields. -/
theorem exists_original_compact_pure_empty_boundary_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (d : ℕ) (hd : d<n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    HasIndependentPureBoundaryResolution W hWa d [] isSNCDivisor_nil := by
  apply exists_original_compact_pure_fixed_target_family W hWa hK d hd hpure [] isSNCDivisor_nil
  simpa using (subset_closure : W ⊆ closure W)

/-- The original closed analytic carrier is internally compact. -/
theorem exists_original_pure_boundary_family_of_compactSpace [CompactSpace X]
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d<n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H)) :
    HasIndependentPureBoundaryResolution W hWa d E₀ hE₀ :=
  exists_original_compact_pure_fixed_target_family W hWa hWa.isClosed.isCompact
    d hd hpure E₀ hE₀ hE₀W

/-- Original compact ambient, literal empty boundary, and whole exact source family. -/
theorem exists_original_pure_empty_boundary_family_of_compactSpace [CompactSpace X]
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d<n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    HasIndependentPureBoundaryResolution W hWa d [] isSNCDivisor_nil :=
  exists_original_compact_pure_empty_boundary_family W hWa hWa.isClosed.isCompact d hd hpure

end
end Hironaka.HironakaOriginalPureCanonicalSpecializations
