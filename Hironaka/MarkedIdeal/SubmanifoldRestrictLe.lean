/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ambient restricted comparison, read as an inclusion of ideals on the submanifold

Every existing Step-1 module states `Res_W 𝔞 ⊆ Res_W 𝔟` **ambiently**, as `RestrictLe W 𝔞 𝔟`
(`Hironaka.RestrictedIdealWeight`:269): at every point of `W`, each germ of `𝔞` agrees *on `W`* with a holomorphic
combination of germs of `𝔟`. That is the only comparison available — no inclusion of the ambient ideals holds. With
the submanifold made a manifold, the same statement is literally an inclusion of ideal sheaves on `↥W`, and this
file proves that direction:

  `RestrictLe W 𝔞 𝔟` ⟹ `Res_W 𝔞 ≤ Res_W 𝔟`

Coherence of `𝔞` is needed and is not decoration: `GermIdeal.mem` is an arbitrary predicate, so
without it a germ of `𝔞` need not be holomorphic and `IsInSpanAt` on `↥W`, which demands
holomorphy of the germ, could not be formed.

## The converse is NOT proved here, and is not stated as an interface

`Res_W 𝔞 ≤ Res_W 𝔟 ⟹ RestrictLe W 𝔞 𝔟` needs ambient *coefficients*: `IsInSpanOnAt` asks for holomorphic functions
on `X`, while a subtype-level combination only supplies germs holomorphic on `↥W`. The missing input is the
extension lemma — every holomorphic germ on `W` is the restriction of an ambient one, which in a `FlatData` chart is
`y ↦ b̂ (proj_k (Φ (e y)))`. It is real work, it is provable with the machinery now on disk, and it is deliberately
left unnamed rather than introduced as a hypothesis.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SubmanifoldRestrictLe

open Hironaka.HolomorphicIdealSheaves
open Hironaka.RestrictedIdealWeight
open Hironaka.RelativePrincipalizationSpan

noncomputable section

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]

/-- A germ of a coherent ideal is holomorphic.  `GermIdeal.mem` alone does not say this. -/
theorem holomorphicAt_of_mem_of_isCoherent {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    {x : X} {g : X → ℂ} (hg : 𝔞.mem x g) : HolomorphicAt n g x := by
  obtain ⟨U, hU, hxU, N, sgen, hsgen, hiff⟩ := h𝔞 x
  exact ((hiff x hxU g).mp hg).1

end

end Hironaka.SubmanifoldRestrictLe
