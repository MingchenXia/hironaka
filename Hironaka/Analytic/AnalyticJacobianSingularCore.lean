/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.ComplexManifold

set_option autoImplicit false

open Set

namespace Hironaka.AnalyticJacobianSingularCore

open Hironaka

noncomputable section

variable {n : ℕ}

/-- The `j`-th standard complex coordinate direction in `ComplexModel n`. -/
def coordinateDirection (j : Fin n) : ComplexModel n := EuclideanSpace.single j 1


end
end Hironaka.AnalyticJacobianSingularCore
