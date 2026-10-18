/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false

namespace Hironaka.AnalyticDimensionBasics

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Geometric pure dimension: every regular point has the indicated local
manifold dimension. This is the original analytic predicate, with no assigned
dimension labels or existence certificate. -/
def IsPureDim (A : Set M) (k : ℕ) : Prop :=
  ∀ y j, RegularAtDim (n := n) A y j → j = k

end Hironaka.AnalyticDimensionBasics
