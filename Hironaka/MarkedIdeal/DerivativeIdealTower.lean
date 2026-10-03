/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals along multiple test blow-ups

Source: Włodarczyk 2005, §2.6, Lemma `le:inclusions2`, for marked ideals `(M, M, E, 𝔞, d)` (`N = M`) and transform
with centre-relative strict transforms (`MarkedIdeal.geoTransform`, `geoTransformAlong`, `IsGeoTestTower`).

* `cosupport_subset_of_le`: cosupports are antitone and controlled transforms monotone in the ideal.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.DerivativeIdealTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupControlledTransform BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal

noncomputable section

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Cosupports are antitone in the ideal**: `𝔟 ⊆ 𝔠` implies `cosupp(𝔠, d) ⊆ cosupp(𝔟, d)`. -/
theorem cosupport_subset_of_le {N : Set M} {𝔟 𝔠 : GermIdeal n M} (h : 𝔟.Le 𝔠) (d : ℕ) :
    cosupport n N 𝔠 d ⊆ cosupport n N 𝔟 d :=
  fun _ hx => ⟨hx.1, fun g hg => hx.2 g (h _ g hg)⟩

end OneSpace

end

end Hironaka.DerivativeIdealTower
