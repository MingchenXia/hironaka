/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.ResolutionInvariantExt

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.StepOneValue
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

open Classical in
/-- **The lower value**: the inductive invariant of the lower marked ideal formed at the last stage of `T₀` around the image
of `y`, along the restricted tail `T₁`, at `y` (`∞` if the image of `y` is not in the mask, which does not happen for
well-formed marked ideals). -/
def lowerValue (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) : WithTop Λ :=
  if h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y) then
    ((R.inv (lowerMarked 𝔍 s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) : Λ) : WithTop Λ)
  else ⊤


end
end Hironaka.StepOneValue
