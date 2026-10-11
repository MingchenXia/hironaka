/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.AnalyticJacobianSingularCore
import Hironaka.Analytic.HolomorphicGermRing

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.HolomorphicGermReducednessBridge

open Hironaka

noncomputable section

variable {n : ℕ}

/-- A coordinate projection is holomorphic as a germ at the origin. -/
theorem eventually_differentiableAt_coordinate (j : Fin n) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z : ComplexModel n => z j) z :=
  Eventually.of_forall fun z => by
    simpa using (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt

/-- A locally unit-times-coordinate factorization has a nonzero derivative in
that coordinate direction.  The equality is only required as a genuine germ
equality (`EventuallyEq`) at `q`; it is not an added regularity assumption. -/
theorem fderiv_apply_coordinateDirection_ne_zero_of_eventuallyEq_unit_mul_coordinate
    {f u : ComplexModel n → ℂ} {q : ComplexModel n} {j : Fin n}
    (hu : DifferentiableAt ℂ u q) (huq : u q ≠ 0)
    (hfac : f =ᶠ[𝓝 q] fun z => u z * (z j - q j)) :
    fderiv ℂ f q (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
  rw [hfac.fderiv_eq]
  have hcoord : HasFDerivAt (fun z : ComplexModel n => z j - q j)
      (EuclideanSpace.proj (𝕜 := ℂ) j) q := by
    simpa using (EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt.sub_const (q j)
  have hprod := hu.hasFDerivAt.mul hcoord
  change fderiv ℂ (u * fun z : ComplexModel n => z j - q j) q
    (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0
  rw [hprod.fderiv]
  simp [AnalyticJacobianSingularCore.coordinateDirection, huq]


end
end Hironaka.HolomorphicGermReducednessBridge
