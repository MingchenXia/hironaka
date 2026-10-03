/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
set_option autoImplicit false

/-!
# Open subsets of `ℂⁿ` as complex manifolds in an arbitrary universe

The universal property `Hironaka.BlowupSequences.IsBlowupAlong` quantifies over test
manifolds in the universe of the blowup, while open subsets of `ℂⁿ` live in `Type`.
`LiftedModel.{u} n` is `ULift.{u} ℂⁿ` with the single chart `ULift.down`, and
`LiftedOpen.{u} S` is the open submanifold over an open `S ⊆ ℂⁿ`.

* `LiftedOpen.contMDiff_toModel`: the coordinate `LiftedOpen S → ℂⁿ` is holomorphic, so
  holomorphic functions near `S` pull back (`LiftedOpen.mdifferentiableAt_comp_toModel`).
* `LiftedOpen.contMDiffAt_of_toModel`: a map into `LiftedOpen S` is holomorphic once its
  coordinate is.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

noncomputable section

variable {n : ℕ}

/-- `ℂⁿ` lifted to the universe `u`, with the single chart `ULift.down`. -/
def LiftedModel (n : ℕ) : Type u := ULift.{u} (ComplexModel n)

namespace LiftedModel

instance : TopologicalSpace (LiftedModel.{u} n) :=
  inferInstanceAs (TopologicalSpace (ULift (ComplexModel n)))

/-- The chart of the lifted model. -/
def chart : OpenPartialHomeomorph (LiftedModel.{u} n) (ComplexModel n) :=
  (Homeomorph.ulift : ULift.{u} (ComplexModel n) ≃ₜ ComplexModel n).toOpenPartialHomeomorph

instance : ChartedSpace (ComplexModel n) (LiftedModel.{u} n) :=
  chart.singletonChartedSpace (Homeomorph.toOpenPartialHomeomorph_source _)

instance : IsComplexManifold n (LiftedModel.{u} n) where
  toT2Space := inferInstanceAs (T2Space (ULift (ComplexModel n)))
  toSecondCountableTopology := Homeomorph.ulift.isEmbedding.secondCountableTopology
  toIsManifold := by
    have := chart.singleton_hasGroupoid (Homeomorph.toOpenPartialHomeomorph_source _)
      (contDiffGroupoid ∞ 𝓘(ℂ, ComplexModel n))
    exact { }

end LiftedModel

/-- An open subset of `ℂⁿ`, lifted to the universe `u`, as an open submanifold of
`LiftedModel n`. -/
def liftedOpens (S : TopologicalSpace.Opens (ComplexModel n)) :
    TopologicalSpace.Opens (LiftedModel.{u} n) :=
  ⟨ULift.down ⁻¹' S, S.isOpen.preimage continuous_uliftDown⟩

/-- An open subset of `ℂⁿ`, lifted to the universe `u`. -/
abbrev LiftedOpen (S : TopologicalSpace.Opens (ComplexModel n)) : Type u :=
  liftedOpens.{u} S

namespace LiftedOpen

variable (S : TopologicalSpace.Opens (ComplexModel n))

/-- The coordinate of a point of a lifted open subset. -/
def toModel : LiftedOpen.{u} S → ComplexModel n := fun p => (p.1 : ULift (ComplexModel n)).down

/-- The point of `LiftedOpen S` over `w ∈ S`. -/
def mk (w : ComplexModel n) (hw : w ∈ S) : LiftedOpen.{u} S := ⟨ULift.up w, hw⟩

@[simp] theorem toModel_mk (w : ComplexModel n) (hw : w ∈ S) :
    toModel S (mk.{u} S w hw) = w := rfl

@[simp] theorem mk_toModel (p : LiftedOpen.{u} S) : mk S (toModel S p) p.2 = p := rfl

theorem toModel_mem (p : LiftedOpen.{u} S) : toModel S p ∈ S := p.2

theorem isOpenEmbedding_toModel : Topology.IsOpenEmbedding (toModel.{u} S) :=
  (Homeomorph.ulift.isOpenEmbedding).comp (liftedOpens.{u} S).isOpen.isOpenEmbedding_subtypeVal

theorem isEmbedding_toModel : Topology.IsEmbedding (toModel.{u} S) :=
  (Homeomorph.ulift.isEmbedding).comp Topology.IsEmbedding.subtypeVal

instance : IsComplexManifold n (LiftedOpen.{u} S) where

theorem extChartAt_eq (p : LiftedOpen.{u} S) :
    ⇑(extChartAt 𝓘(ℂ, ComplexModel n) p) = toModel S := rfl

theorem contMDiff_toModel :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (toModel.{u} S) := by
  intro p
  rw [← extChartAt_eq S p]
  exact contMDiffAt_extChartAt

/-- A map into a lifted open subset is smooth once its coordinate is. -/
theorem contMDiffAt_of_toModel {m : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (ComplexModel m) W] {G : W → LiftedOpen.{u} S} {x : W}
    (hG : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (toModel S ∘ G) x) :
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G x := by
  rw [contMDiffAt_iff_target]
  refine ⟨?_, hG⟩
  exact (isEmbedding_toModel S).continuousAt_iff.mpr hG.continuousAt

/-- A holomorphic function near the coordinate of `p` pulls back to a holomorphic function
near `p`. -/
theorem mdifferentiableAt_comp_toModel {f : ComplexModel n → ℂ} {p : LiftedOpen.{u} S}
    (hf : DifferentiableAt ℂ f (toModel S p)) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f ∘ toModel S) p :=
  hf.mdifferentiableAt.comp p ((contMDiff_toModel S p).mdifferentiableAt (by simp))

end LiftedOpen

end

end Hironaka
