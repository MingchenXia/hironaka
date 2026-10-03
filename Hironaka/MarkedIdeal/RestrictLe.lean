/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.IdealPresentation
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false

/-!
# Inclusion of ideal sheaves along a subset

`RestrictLe W 𝔞 𝔟`: at every point of `W`, every germ of `𝔞` agrees on `W`, near the point, with a holomorphic
combination of germs of `𝔟`.

Declarations:
* `RestrictLe`
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.RestrictedIdealWeight

noncomputable section

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightComparison
open Hironaka.RelativePrincipalizationSpan

/-! ### From a restricted inclusion of ideals to a comparison of weights on `W` -/

section Ideal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable {W : Set M} {𝔞 𝔟 : GermIdeal n M}

def RestrictLe (W : Set M) (𝔞 𝔟 : GermIdeal n M) : Prop :=
  ∀ x ∈ W, ∀ g, 𝔞.mem x g → IsInSpanOnAt (n := n) W (𝔟.mem x) x g

end Ideal

end

end Hironaka.RestrictedIdealWeight
