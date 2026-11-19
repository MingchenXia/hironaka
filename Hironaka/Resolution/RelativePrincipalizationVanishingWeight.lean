import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Analytic.DivisorIdealWeightComparison
import Hironaka.Resolution.RelativePrincipalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `eq:IV-H` for the factorization relative principalization actually delivers

Source: Copy-4, Step 4 of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`), equation `eq:IV-H`.

`RelativePrincipalization.exists_relativePrincipalization` hands back, among other
things, the *ideal* identity

  `𝓘_W · 𝒪_{Y'} = 𝒪_{Y'}(-H) · 𝓘_{W'}`,

one factor a divisor, the other the vanishing ideal of the strict transform.  Step 4
uses it as an identity of weights,

  `ψ_{𝓘_W} ∘ f = ψ_H + ψ_{𝓘_{W'}} + O(1)`   (`eq:IV-H`).

`Pending/DivisorIdealWeightComparison` already covers the *two-divisor* shape
`𝔞 𝒪_Z = 𝒪(-H)·𝒪(-H')` (I-0409).  The mixed shape above was not instantiable,
because nothing produced a weight for a vanishing ideal.  Both halves now exist:

* `Pending/VanishingIdealCoherent.isCoherent_vanishingIdeal` — the vanishing ideal
  of a closed complex submanifold is coherent — feeding
  `CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent`, which
  produces `ψ_{𝓘_W}` and `ψ_{𝓘_{W'}}` with coefficient `1`;
* `Pending/DivisorMetric.exists_divisorMetric` together with
  `hasAnalyticSingularitiesOfType_of_isDivisorMetric` — which produces `ψ_H`, also
  with coefficient `1`.

So no weight is hypothesised here: all three are constructed, and the conclusion is
`eq:IV-H` with a single constant on the compact source.  Nothing is assumed about
`f` beyond smoothness — not properness, not surjectivity, not that it is a
modification — and nothing about the supports; the content is the factorization of
the ideal alone.

Degenerate cases.  `p = 0` is allowed: `Y'` is then a finite set of points, `H` has
empty support and `𝓘_{W'}` is the unit ideal or the zero ideal according to whether
`W'` is empty, and the statement is a comparison of two finite functions.  `W = ∅`
gives `𝓘_W = 𝒪`, whose weight is bounded, and `W = Y` gives the zero ideal, whose
weight is `⊥` identically; both are legitimate closed submanifolds and the
conclusion holds in both.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.RelativePrincipalizationVanishingWeight

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  Hironaka.BlowupSequences
open Hironaka.DivisorMetric

variable {n p : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Y' : Type*} [TopologicalSpace Y'] [ChartedSpace (ComplexModel p) Y']
  [IsComplexManifold p Y']

/-- A closed connected submanifold of a fixed dimension is a closed submanifold. -/
theorem isClosedSubmanifold_of_isClosedConnectedSubmanifold {W : Set Y} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) : IsClosedSubmanifold n W :=
  ⟨hW.1, fun x hx => ⟨k, hW.2.2 x hx⟩⟩

/-- **`eq:IV-H`.**  If the pullback of the vanishing ideal of a closed submanifold
`W ⊆ Y` factors as `𝒪(-H) · 𝓘_{W'}` for a closed submanifold `W' ⊆ Y'`, then

  `ψ_{𝓘_W} ∘ f = ψ_H + ψ_{𝓘_{W'}} + O(1)`   on all of `Y'`,

with all three weights constructed, and `ψ_H` the weight of a metered `ℚ`-divisor
with the same support as `H`. -/
theorem exists_weights_sameSingularityTypeOn_comp_of_pullback_eq_divisor_mul_vanishing
    [CompactSpace Y] [CompactSpace Y']
    {f : Y' → Y} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {W : Set Y} (hW : IsClosedSubmanifold n W)
    {W' : Set Y'} (hW' : IsClosedSubmanifold p W')
    (H : EffectiveDivisor p Y')
    (hfact : GermIdeal.pullback (m := p) f (vanishingIdeal (n := n) W) =
      H.ideal.mul (vanishingIdeal (n := p) W')) :
    ∃ (φW : Y → EReal) (E : MeteredEffectiveQDivisor p Y') (φW' : Y' → EReal),
      HasAnalyticSingularitiesOfType (n := n) φW 1 (vanishingIdeal (n := n) W) ∧
      E.support = H.support ∧
      HasAnalyticSingularitiesOfType (n := p) φW' 1 (vanishingIdeal (n := p) W') ∧
      SameSingularityTypeOn (φW ∘ f) (fun y => E.weight y + φW' y) univ := by
  obtain ⟨φW, hφW⟩ :=
    VanishingIdealCoherent.exists_hasAnalyticSingularitiesOfType_vanishingIdeal hW
  obtain ⟨φW', hφW'⟩ :=
    VanishingIdealCoherent.exists_hasAnalyticSingularitiesOfType_vanishingIdeal hW'
  obtain ⟨E, hEsupp, hE⟩ := exists_divisorMetric H
  refine ⟨φW, E, φW', hφW, hEsupp, hφW', ?_⟩
  exact ExceptionalWeightFactorization.sameSingularityTypeOn_univ_comp_add_of_pullback_eq_mul
    hf hφW (hasAnalyticSingularitiesOfType_of_isDivisorMetric hE) hφW' hfact

/-- `eq:IV-H` read as the two inequalities Step 5 consumes.  The first is the one
used to bound `ψ_H` from above by the pulled-back ambient weight; the second is the
converse half, which is what makes `ψ_{𝓘_{W'}}` absorb the difference. -/
theorem exists_weights_moreSingularOn_comp_of_pullback_eq_divisor_mul_vanishing
    [CompactSpace Y] [CompactSpace Y']
    {f : Y' → Y} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {W : Set Y} (hW : IsClosedSubmanifold n W)
    {W' : Set Y'} (hW' : IsClosedSubmanifold p W')
    (H : EffectiveDivisor p Y')
    (hfact : GermIdeal.pullback (m := p) f (vanishingIdeal (n := n) W) =
      H.ideal.mul (vanishingIdeal (n := p) W')) :
    ∃ (φW : Y → EReal) (E : MeteredEffectiveQDivisor p Y') (φW' : Y' → EReal),
      HasAnalyticSingularitiesOfType (n := n) φW 1 (vanishingIdeal (n := n) W) ∧
      E.support = H.support ∧
      HasAnalyticSingularitiesOfType (n := p) φW' 1 (vanishingIdeal (n := p) W') ∧
      MoreSingularOn (φW ∘ f) (fun y => E.weight y + φW' y) univ ∧
      MoreSingularOn (fun y => E.weight y + φW' y) (φW ∘ f) univ := by
  obtain ⟨φW, E, φW', hφW, hEsupp, hφW', hsame⟩ :=
    exists_weights_sameSingularityTypeOn_comp_of_pullback_eq_divisor_mul_vanishing
      hf hW hW' H hfact
  exact ⟨φW, E, φW', hφW, hEsupp, hφW', hsame.1, hsame.2⟩

section SameDimension

variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **`eq:IV-H` along an adapted blowup sequence.**  The shape in which Step 4 meets
it: `W'` is the strict transform of `W`, and its submanifold hypothesis is the
`IsClosedConnectedSubmanifold` that `lem:relative-principalization` returns.  Source
and target carry the same model, as they do for a modification. -/
theorem exists_weights_sameSingularityTypeOn_strictTransform
    [CompactSpace Y] [CompactSpace Z] {j k : ℕ}
    {f : Z → Y} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {W : Set Y} (hW : IsClosedConnectedSubmanifold n W j)
    (hW' : IsClosedConnectedSubmanifold n (strictTransform n f W) k)
    (H : EffectiveDivisor n Z)
    (hfact : GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
      H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W))) :
    ∃ (φW : Y → EReal) (E : MeteredEffectiveQDivisor n Z) (φW' : Z → EReal),
      HasAnalyticSingularitiesOfType (n := n) φW 1 (vanishingIdeal (n := n) W) ∧
      E.support = H.support ∧
      HasAnalyticSingularitiesOfType (n := n) φW' 1
        (vanishingIdeal (n := n) (strictTransform n f W)) ∧
      SameSingularityTypeOn (φW ∘ f) (fun y => E.weight y + φW' y) univ :=
  exists_weights_sameSingularityTypeOn_comp_of_pullback_eq_divisor_mul_vanishing hf
    (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW)
    (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW') H hfact

end SameDimension

end

end Hironaka.RelativePrincipalizationVanishingWeight
