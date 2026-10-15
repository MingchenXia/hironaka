/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.RestrictedIdealExtension

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.RestrictedIdealExtension

noncomputable section

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightComparison
open Hironaka.IdealWeightPowers
open Hironaka.RelativePrincipalizationSpan
open Hironaka.RestrictedIdealWeight

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable {W : Set M} {𝔞 : GermIdeal n M}

/-- **`𝔣̃` is coherent for a closed submanifold `W`** — the form Step 1 uses, with
`𝓘_W` coherent by `VanishingIdealCoherent.isCoherent_vanishingIdeal` (Hadamard in
flattening coordinates). -/
theorem isCoherent_restrictOn_of_isClosedSubmanifold [IsComplexManifold n M]
    (h𝔞 : 𝔞.IsCoherent) (hW : Hironaka.BlowupSequences.IsClosedSubmanifold n W) :
    (restrictOn n W 𝔞).IsCoherent :=
  isCoherent_restrictOn h𝔞 (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)

/-! ### `Res_W 𝔣̃ = Res_W 𝔞`, and `𝔣̃ ⊄ 𝓘_W` -/

/-- Every germ of `𝔣̃` restricts on `W` into `𝔞`: this is `Res_W 𝔣̃ ⊆ Res_W 𝔞`, and it
is the definition. -/
theorem restrictLe_restrictOn : RestrictLe W (restrictOn n W 𝔞) 𝔞 :=
  fun _ _ _ hg => hg.2

/-- The converse inclusion `Res_W 𝔞 ⊆ Res_W 𝔣̃`. -/
theorem restrictLe_self_restrictOn (h𝔞 : 𝔞.IsCoherent) :
    RestrictLe W 𝔞 (restrictOn n W 𝔞) :=
  fun x _ g hg => IsInSpanAt.restrict (isInSpanAt_of_eq_mul (S := (restrictOn n W 𝔞).mem x)
    (le_restrictOn h𝔞 x g hg) (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))

end
end Hironaka.RestrictedIdealExtension
