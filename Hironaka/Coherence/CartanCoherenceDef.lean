/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# The statement of Cartan's coherence theorem, in a light module

`CartanCoherence n X`: the ideal sheaf of every analytic subset of the complex manifold `X` is coherent (H. Cartan
1950). The definition is moved here verbatim from `Hironaka.CartanComponentIdeal`. It keeps its namespace
`Hironaka.CartanComponentIdeal`, its name, binders, body and docstring, so it is the same constant.

The proof of Cartan's theorem (`CartanLocalReduction` -> `CoherentIdealColon` -> `CartanIrreducibleReduction` ->
`CartanIrreducible.cartanCoherence`) needs only this definition.

No statement is changed.
-/

universe u

namespace Hironaka.CartanComponentIdeal

noncomputable section

open Hironaka.HolomorphicIdealSheaves

/-- **Cartan's coherence theorem** (H. Cartan 1950): the ideal sheaf of every analytic subset is
coherent.  Recorded as a proposition: it is a hypothesis of theorems in `CartanComponentIdeal`,
and it is proved as `CartanIrreducible.cartanCoherence`. -/
def CartanCoherence (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] : Prop :=
  ∀ A : Set X, IsComplexAnalyticSubset (n := n) A → (vanishingIdeal (n := n) A).IsCoherent

end

end Hironaka.CartanComponentIdeal
