/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedEquivalence
import Hironaka.MarkedIdeal.DerivativeIdealInvariance
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The homogenized and coefficient ideals commute with restriction to open sets and with biholomorphisms

Source: Włodarczyk 2005, Lemmas `le:etale2`, `le:etale3` (étale functoriality of `𝓓`, `𝓗` and `𝓒`), for the two
kinds of étale maps used in the analytic setting: the inclusion of an open set and a biholomorphism.

* `pullback_finSumIdeal`, `pullback_homSum`: pullbacks commute with finite sums `∑ᵢ 𝔍ᵢ` and with `∑ᵢ Aᵢ Bⁱ`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedEtale

open Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal HomogenizedIdeal HomogenizedGlueing HomogenizedEquivalence MarkedIdealBiholomorphism GermIdealPullbackCalculus

noncomputable section

section Pullback

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] {f : M' → M}

/-- **Pullbacks commute with finite sums** (`m ≥ 1`, coherent summands). -/
theorem pullback_finSumIdeal (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {J : ℕ → GermIdeal n M} (hJ : ∀ i, (J i).IsCoherent) :
    ∀ {m : ℕ}, 1 ≤ m →
      GermIdeal.pullback (m := n) f (finSumIdeal J m) = finSumIdeal (fun i => GermIdeal.pullback (m := n) f (J i)) m
  | 0, h => absurd h (by omega)
  | 1, _ => by
    rw [finSumIdeal_one (hJ 0), finSumIdeal_one (isCoherent_pullback hf (hJ 0))]
  | m + 2, _ => by
    have hJ' : ∀ i, (GermIdeal.pullback (m := n) f (J i)).IsCoherent := fun i => isCoherent_pullback hf (hJ i)
    rw [finSumIdeal_succ (fun i _ => hJ i), finSumIdeal_succ (fun i _ => hJ' i),
      MarkedIdealOperationsTransform.pullback_sumIdeal hf
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (isCoherent_finSumIdeal_of_lt fun i _ => hJ i))
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hJ (m + 1))),
      pullback_finSumIdeal hf hJ (m := m + 1) (by omega)]

/-- **Pullbacks commute with `∑ᵢ Aᵢ Bⁱ`** (`μ ≥ 1`, coherent `Aᵢ`, `B`). -/
theorem pullback_homSum (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {A : ℕ → GermIdeal n M} {B : GermIdeal n M} (hA : ∀ i, (A i).IsCoherent) (hB : B.IsCoherent) {μ : ℕ}
    (hμ : 1 ≤ μ) :
    GermIdeal.pullback (m := n) f (homSum A B μ) =
      homSum (fun i => GermIdeal.pullback (m := n) f (A i)) (GermIdeal.pullback (m := n) f B) μ := by
  unfold homSum
  rw [pullback_finSumIdeal hf (fun i => isCoherent_mul (hA i) (isCoherent_idealPow hB i)) hμ]
  refine finSumIdeal_congr fun i _ => ?_
  rw [GermIdealTotalTransform.pullback_mul hf (hA i) (isCoherent_idealPow hB i),
    BlowupExceptionalDivisor.pullback_idealPow hf hB]

end Pullback

end

end Hironaka.HomogenizedEtale
