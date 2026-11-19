import Hironaka.Analytic.BergmanGeneratorSpan

/-!
# Global descent from finite holomorphic frame changes

This module packages the exact hypotheses needed to turn a locally finite
holomorphic presentation into one coherent germ ideal.  On every designated
open overlap, the two chosen finite generator families must be related by
explicit holomorphic coefficient matrices in both directions.  No such
transition data are constructed here; a Bergman application must supply them,
together with its local logarithmic formula and bounded remainders.
-/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Manifold Topology

namespace Hironaka.FiniteHolomorphicFrameDescent


open Hironaka.GlobalAnalyticSingularities
open Hironaka.HolomorphicIdealSheaves
open BergmanGeneratorSpan
open FiniteGeneratorIdealDescent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Explicit mutually inverse-at-the-span-level holomorphic finite generator
expansions on the prescribed local open cover construct a global coherent germ
ideal with the displayed analytic-singularity type.  The hypotheses retain the
local logarithmic presentation and bounded remainder because frame-change data
alone do not provide either one. -/
theorem exists_hasAnalyticSingularitiesOfType_of_localMutualHolomorphicGeneratorExpansions
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (U : M → Set M) (hUopen : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (N : M → ℕ) (G : ∀ x, Fin (N x) → M → ℂ)
    (hGdiff : ∀ x i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (U x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ U x, |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ U x →
      phi y = ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal))
    (A : ∀ x y, Fin (N y) → Fin (N x) → M → ℂ)
    (B : ∀ x y, Fin (N x) → Fin (N y) → M → ℂ)
    (hAhol : ∀ x y, y ∈ U x → ∀ j i, HolomorphicAt n (A x y j i) y)
    (hBhol : ∀ x y, y ∈ U x → ∀ i j, HolomorphicAt n (B x y i j) y)
    (hforward : ∀ x y, y ∈ U x → ∀ j,
      G y j =ᶠ[𝓝 y] fun z => ∑ i, A x y j i z * G x i z)
    (hbackward : ∀ x y, y ∈ U x → ∀ i,
      G x i =ᶠ[𝓝 y] fun z => ∑ j, B x y i j z * G y j z) :
    ∃ a : GermIdeal n M, HasAnalyticSingularitiesOfType phi c a := by
  apply exists_hasAnalyticSingularitiesOfType_of_localGeneratorDescent
    (n := n) (M := M) (phi := phi) c hc U hUopen hxU N G hGdiff R hRbound hformula
  intro x y hy h
  have hGhol : ∀ i, HolomorphicAt n (G x i) y := by
    intro i
    filter_upwards [hUopen x |>.mem_nhds hy] with z hz
    exact (hGdiff x i z hz).mdifferentiableAt (hUopen x |>.mem_nhds hz)
  obtain ⟨hxy, hyx⟩ := generatorInclusions_of_mutualHolomorphicGeneratorExpansions
    (G x) (G y) (A x y) (B x y) hGhol (hAhol x y hy) (hBhol x y hy)
      (hforward x y hy) (hbackward x y hy)
  exact isInSpanAt_iff_of_generators_mutually_in_span (G x) (G y) hxy hyx h

omit [IsComplexManifold n M] in
/-- The preceding coherent-ideal descent gives analytic singularities for the
same locally finite presentation.  This theorem still assumes, rather than
asserts, the actual two-way holomorphic overlap equations. -/
theorem hasAnalyticSingularities_of_localMutualHolomorphicGeneratorExpansions
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (U : M → Set M) (hUopen : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (N : M → ℕ) (G : ∀ x, Fin (N x) → M → ℂ)
    (hGdiff : ∀ x i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (U x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ U x, |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ U x →
      phi y = ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal))
    (A : ∀ x y, Fin (N y) → Fin (N x) → M → ℂ)
    (B : ∀ x y, Fin (N x) → Fin (N y) → M → ℂ)
    (hAhol : ∀ x y, y ∈ U x → ∀ j i, HolomorphicAt n (A x y j i) y)
    (hBhol : ∀ x y, y ∈ U x → ∀ i j, HolomorphicAt n (B x y i j) y)
    (hforward : ∀ x y, y ∈ U x → ∀ j,
      G y j =ᶠ[𝓝 y] fun z => ∑ i, A x y j i z * G x i z)
    (hbackward : ∀ x y, y ∈ U x → ∀ i,
      G x i =ᶠ[𝓝 y] fun z => ∑ j, B x y i j z * G y j z) :
    HasAnalyticSingularities (n := n) phi := by
  obtain ⟨a, ha⟩ :=
    exists_hasAnalyticSingularitiesOfType_of_localMutualHolomorphicGeneratorExpansions
      (n := n) (M := M) (phi := phi) c hc U hUopen hxU N G hGdiff R hRbound hformula
        A B hAhol hBhol hforward hbackward
  exact ⟨c, a, ha⟩

end

end Hironaka.FiniteHolomorphicFrameDescent
