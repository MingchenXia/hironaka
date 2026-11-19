import Hironaka.Analytic.InvertibleIdealCoherent
import Hironaka.Analytic.IdealPresentation
import Hironaka.Blowup.ExceptionalWeightFactorization

set_option autoImplicit false

/-!
# `ψ_𝔞 ∘ f = ψ_G + O(1)` for a principalized ideal

Source: Copy-4, Step 5 of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`), the sentence

  "By `sec:qpsh`, locally on `Y` we have `ψ_{𝔅_M} ∘ π = ψ_{G̃_M} + O(1)`,
   `ψ_{𝔅_m} ∘ π = ψ_{G̃_m} + O(1)`",

which is the hypothesis `hGM` of `Pending/CollarWeightComparison`.

The two halves are now both proved.  `IdealWeightComparison` compares a weight
with a weight *presenting the pulled-back ideal*; what was missing on the divisor
side is a weight presenting `𝒪(-G)` at all, since
`RelativePrincipalization.exists_relativePrincipalization` hands back a bare
`EffectiveDivisor`.  `Pending/DivisorMetric` supplies it: `𝒪(G)` carries a smooth
metric and its weight has analytic singularities of type `(1, 𝒪(-G))`.  Composing
the two gives the statement above with a single constant on a compact source.

The coefficient is `1` on both sides, which is the manuscript's normalisation
`ψ_𝔞 = log ∑ |g_i|²`.

**Which form is usable.**  Every producer in the project delivers the pulled-back
ideal in the *two-factor* shape `𝔞 𝒪_Z = 𝒪(-H) · 𝒪(-H')`
(`RelativePrincipalization.exists_relativePrincipalization` and its callers), not
as the ideal of a single divisor.  The single-divisor statements below are
therefore the clean form but are not instantiable from what exists today; the
two-factor corollaries `..._mul` are, and they are `eq:IV-H` with the divisors
metered.  Recorded as I-0409.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DivisorIdealWeightComparison

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison
open Hironaka.DivisorMetric

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel p) Z]
  [IsComplexManifold p Z]

/-- **`ψ_𝔞 ∘ f = ψ_G + O(1)`** for a metered divisor `E` metrizing `G`, whenever the
pulled-back ideal is `𝒪(-G)`. -/
theorem sameSingularityTypeOn_univ_comp_of_pullback_eq_divisor [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ 1 𝔞)
    {G : EffectiveDivisor p Z} {E : MeteredEffectiveQDivisor p Z}
    (hE : IsDivisorMetric G E)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = G.ideal) :
    SameSingularityTypeOn (φ ∘ f) E.weight univ := by
  refine sameSingularityTypeOn_univ_comp_pullback hf hφ ?_
  rw [hfact]
  exact hasAnalyticSingularitiesOfType_of_isDivisorMetric hE

/-- **`hGM`** (Copy-4, Step 5).  A principalized ideal weight, pulled back, is the
weight of the resulting divisor for a suitable smooth metric, up to one constant on
the compact source.  The metric is not an extra hypothesis: it is constructed. -/
theorem exists_divisorMetric_sameSingularityTypeOn_comp [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ 1 𝔞)
    (G : EffectiveDivisor p Z)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = G.ideal) :
    ∃ E : MeteredEffectiveQDivisor p Z, E.support = G.support ∧
      SameSingularityTypeOn (φ ∘ f) E.weight univ := by
  obtain ⟨E, hsupp, hE⟩ := exists_divisorMetric G
  exact ⟨E, hsupp,
    sameSingularityTypeOn_univ_comp_of_pullback_eq_divisor hf hφ hE hfact⟩

/-- The exact half Step 5 consumes as the hypothesis `hGM` of
`Pending/CollarWeightComparison.moreSingularOn_ambientLowerBound`:
`ψ_{G̃_M} ≤ ψ_{𝔅_M} ∘ π + O(1)`. -/
theorem exists_divisorMetric_moreSingularOn_comp [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ 1 𝔞)
    (G : EffectiveDivisor p Z)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = G.ideal) :
    ∃ E : MeteredEffectiveQDivisor p Z, E.support = G.support ∧
      MoreSingularOn E.weight (fun w => φ (f w)) univ := by
  obtain ⟨E, hsupp, hE⟩ :=
    exists_divisorMetric_sameSingularityTypeOn_comp hf hφ G hfact
  exact ⟨E, hsupp, hE.2⟩

/-- **`eq:IV-H` with metered divisors.**  For the two-factor factorization
`𝔞 𝒪_Z = 𝒪(-H) · 𝒪(-H')` that `lem:relative-principalization` actually delivers,
`ψ_𝔞 ∘ f = ψ_H + ψ_{H'} + O(1)` on a compact source, with metrics constructed on
both divisors. -/
theorem exists_divisorMetric_sameSingularityTypeOn_comp_mul [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ 1 𝔞)
    (H H' : EffectiveDivisor p Z)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = H.ideal.mul H'.ideal) :
    ∃ E E' : MeteredEffectiveQDivisor p Z,
      E.support = H.support ∧ E'.support = H'.support ∧
      SameSingularityTypeOn (φ ∘ f) (fun w => E.weight w + E'.weight w) univ := by
  obtain ⟨E, hEsupp, hE⟩ := exists_divisorMetric H
  obtain ⟨E', hE'supp, hE'⟩ := exists_divisorMetric H'
  refine ⟨E, E', hEsupp, hE'supp, ?_⟩
  exact ExceptionalWeightFactorization.sameSingularityTypeOn_univ_comp_add_of_pullback_eq_mul
    hf hφ (hasAnalyticSingularitiesOfType_of_isDivisorMetric hE)
    (hasAnalyticSingularitiesOfType_of_isDivisorMetric hE') hfact

/-- The half Step 5 consumes, in the two-factor form: `ψ_H + ψ_{H'} ≤ ψ_𝔞 ∘ f + O(1)`. -/
theorem exists_divisorMetric_moreSingularOn_comp_mul [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ 1 𝔞)
    (H H' : EffectiveDivisor p Z)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = H.ideal.mul H'.ideal) :
    ∃ E E' : MeteredEffectiveQDivisor p Z,
      E.support = H.support ∧ E'.support = H'.support ∧
      MoreSingularOn (fun w => E.weight w + E'.weight w) (fun w => φ (f w)) univ := by
  obtain ⟨E, E', hEsupp, hE'supp, hsame⟩ :=
    exists_divisorMetric_sameSingularityTypeOn_comp_mul hf hφ H H' hfact
  exact ⟨E, E', hEsupp, hE'supp, hsame.2⟩

end

end Hironaka.DivisorIdealWeightComparison
