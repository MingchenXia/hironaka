/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A generator of the ideal of a submanifold has multiplicity one

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), Lemma `le:Gi` (2) (the controlled transform `u'` of a tangent
direction `u` is again of multiplicity one).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.GeneratorMultiplicityOne

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupStrictSubmanifold BlowupFunctionTransform DerivativeIdeal

noncomputable section

variable {n : ℕ}

/-- The differential of a local holomorphic equivalence is surjective at the points of its
source. -/
theorem surjective_fderiv_toFun {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    {q : ComplexModel n} (hq : q ∈ Φ.source) : Function.Surjective (fderiv ℂ Φ.toFun q) := by
  have hdq : DifferentiableAt ℂ Φ.toFun q :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hq)
  have hqt : Φ.toFun q ∈ Φ.target := Φ.mapsTo_toFun hq
  have hdi : DifferentiableAt ℂ Φ.invFun (Φ.toFun q) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hqt)
  have hcomp : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w))
      ((fderiv ℂ Φ.invFun (Φ.toFun q)).comp (fderiv ℂ Φ.toFun q)) q :=
    hdi.hasFDerivAt.comp q hdq.hasFDerivAt
  have hid : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w)) (ContinuousLinearMap.id ℂ _) q := by
    refine (hasFDerivAt_id q).congr_of_eventuallyEq ?_
    filter_upwards [Φ.isOpen_source.mem_nhds hq] with w hw
    exact Φ.left_inv w hw
  have hEq := hcomp.unique hid
  have hinj : Function.Injective (fderiv ℂ Φ.toFun q) := by
    intro v w hvw
    have := congrArg (fderiv ℂ Φ.invFun (Φ.toFun q)) hvw
    have h1 := DFunLike.congr_fun hEq v
    have h2 := DFunLike.congr_fun hEq w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, this]
  set L : ComplexModel n →ₗ[ℂ] ComplexModel n := (fderiv ℂ Φ.toFun q).toLinearMap
  exact LinearMap.injective_iff_surjective (f := L) |>.mp hinj

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

end

end Hironaka.GeneratorMultiplicityOne
