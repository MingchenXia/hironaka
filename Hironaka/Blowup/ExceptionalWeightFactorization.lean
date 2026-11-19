import Hironaka.Analytic.IdealPowers

set_option autoImplicit false

/-!
# `eq:IV-H`: the pulled-back ideal weight splits off the exceptional divisor

Source: Copy-4, Step 4 of `prop:principalization`, equation `eq:IV-H`
(`transcendental-nakamaye-copy4-20260911`).

`RelativePrincipalization.exists_relativePrincipalization` produces, along with
the modification `f : Y' → Y` and the strict transform `W' = strictTransform f W`,
an effective divisor `H` supported in the exceptional locus with the **ideal**
identity

  `𝓘_W · 𝒪_{Y'} = 𝓘(H) · 𝓘_{W'}`.

Copy-4 uses it as an identity between *weights*,

  `ψ_{𝓘_W} ∘ f = ψ_H + ψ_{𝓘_{W'}} + O(1)`   (`eq:IV-H`),

with one constant on the compact `Y'`.  That is exactly what this module records.
It is the composition of two results that already exist and are the two genuine
halves:

* `IdealWeightComparison.sameSingularityTypeOn_univ_comp_pullback` — the weight of
  a pulled-back ideal is the pullback of the weight, up to `O(1)`;
* `IdealWeightPowers.hasAnalyticSingularitiesOfType_mul` — the sum of two weights
  *presents* the product ideal (it produces a presentation rather than comparing a
  given one, which is what makes the substitution along the ideal identity legal).

Nothing here assumes `f` is proper, surjective, or a modification, and nothing
assumes anything about the supports: the statement is about the factorisation of
the ideal only.  The complementary statement Step 4 also uses — that
`ψ_{𝓘_{W'}}` is bounded on compact subsets of `Y' \ W'` — is separate and lives in
`Pending/MeteredDivisorWeightBounds`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.ExceptionalWeightFactorization

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison
open Hironaka.IdealWeightPowers

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel p) Z]
  [IsComplexManifold p Z]

/-- **`eq:IV-H`.**  If the pullback of `𝔞` factors as `𝔥 · 𝔟` and `φ`, `φ_𝔥`, `φ_𝔟`
present `𝔞`, `𝔥`, `𝔟` with one and the same positive rational coefficient, then

  `φ ∘ f = φ_𝔥 + φ_𝔟 + O(1)`

on a compact source, with a single constant.  The substitution along the ideal
identity is legal because `hasAnalyticSingularitiesOfType_mul` *produces* a
presentation of `𝔥 · 𝔟`, so no potential for the product has to be named. -/
theorem sameSingularityTypeOn_univ_comp_add_of_pullback_eq_mul [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {φ𝔥 φ𝔟 : Z → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} {𝔥 𝔟 : GermIdeal p Z}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ𝔥 : HasAnalyticSingularitiesOfType (n := p) φ𝔥 c 𝔥)
    (hφ𝔟 : HasAnalyticSingularitiesOfType (n := p) φ𝔟 c 𝔟)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = 𝔥.mul 𝔟) :
    SameSingularityTypeOn (φ ∘ f) (fun y => φ𝔥 y + φ𝔟 y) univ := by
  refine sameSingularityTypeOn_univ_comp_pullback hf hφ ?_
  rw [hfact]
  exact hasAnalyticSingularitiesOfType_mul hφ𝔥 hφ𝔟

/-- The same statement read as the two inequalities Step 5 consumes: `ψ_H` is the
difference `ψ_{𝓘_W} ∘ f - ψ_{𝓘_{W'}}` up to a constant, in the additive form that
avoids subtracting possibly infinite values. -/
theorem moreSingularOn_univ_comp_of_pullback_eq_mul [CompactSpace Z]
    {f : Z → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {φ𝔥 φ𝔟 : Z → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} {𝔥 𝔟 : GermIdeal p Z}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ𝔥 : HasAnalyticSingularitiesOfType (n := p) φ𝔥 c 𝔥)
    (hφ𝔟 : HasAnalyticSingularitiesOfType (n := p) φ𝔟 c 𝔟)
    (hfact : GermIdeal.pullback (m := p) f 𝔞 = 𝔥.mul 𝔟) :
    MoreSingularOn (φ ∘ f) (fun y => φ𝔥 y + φ𝔟 y) univ ∧
      MoreSingularOn (fun y => φ𝔥 y + φ𝔟 y) (φ ∘ f) univ :=
  sameSingularityTypeOn_univ_comp_add_of_pullback_eq_mul hf hφ hφ𝔥 hφ𝔟 hfact

end

end Hironaka.ExceptionalWeightFactorization
