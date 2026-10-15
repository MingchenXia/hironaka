/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.StepOneWellFounded

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneWellFounded

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.ResolutionInvariantOrder Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment isCanonicalSegment_step_iff)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level
  interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

section StepOne

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
variable (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (𝔍 : MarkedIdeal n X)

/-- **The masked Step 1 value has the drop property** along its canonical segments, for the marked ideals of the domain of
maximal order (`StepOneBridge.decrease_field`, `StepOneBridge.emptyStep_field`). -/
theorem stepDrop_stepOneInvM (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    StepDrop 𝔍 (stepOneInvM R 𝔍) := by
  intro Y Z T C π hπ hcan z hz
  have hTs := (StepOneBridge.isGeoTestTower_of_isCanonical R 𝔍 h hmax hn _ hcan).2.1
  obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (stepOneInvM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
  refine ⟨proj_mem_cosupp_step h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T C π hπ hTs hz, ?_⟩
  rcases hC with hC | hC
  · refine ⟨fun hzC => ?_, fun _ => StepOneBridge.emptyStep_field R 𝔍 h hmax hn T C π hπ hC hT z hz⟩
    rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · exact StepOneBridge.decrease_field R 𝔍 h hmax hn T C π hπ hT hC z hz

end StepOne
end
end Hironaka.StepOneWellFounded
