import Mathlib.Analysis.CStarAlgebra.Classes
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.ComplexAnalyticSubvarieties

set_option autoImplicit false

/-!
# The statement of Cartan's coherence theorem, in a light module

`CartanCoherence n X`: the ideal sheaf of every analytic subset of the complex manifold `X` is
coherent (H. Cartan 1950).  The definition is moved here verbatim from `Hironaka.CartanComponentIdeal`.
It keeps its namespace `Hironaka.CartanComponentIdeal`, its name, binders,
body and docstring, so it is the same constant. `Hironaka.CartanComponentIdeal` imports this module
and re-exports it.

Why it moved: the closure of `Hironaka.CartanComponentIdeal` contains `Hironaka.RelativePrincipalization`.
The proof of Cartan's theorem (`CartanLocalReduction` -> `CoherentIdealColon` ->
`CartanIrreducibleReduction` -> `CartanIrreducible.cartanCoherence`) needs only this definition.
It now imports this module, so it lies outside the import closures of both Hironaka statements.

The extra import `Mathlib.Analysis.CStarAlgebra.Classes` makes the instances in the binders
elaborate exactly as they did in `Hironaka.CartanComponentIdeal`.

Sorry-free.  No statement is changed.
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
