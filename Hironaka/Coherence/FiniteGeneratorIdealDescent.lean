import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus

/-!
# Descent of finite local generators to a coherent germ ideal

A finite family of local holomorphic generators determines a global germ ideal
when the spans of the generators agree on overlaps.  This is the coherence
bridge needed by finite Bergman presentations: the analytic estimate supplies
the bounded remainder, while the overlap statement below supplies the actual
ideal descent.
-/

set_option autoImplicit false

open scoped Manifold

namespace Hironaka.FiniteGeneratorIdealDescent


open Hironaka.HolomorphicIdealSheaves
open Hironaka.GlobalAnalyticSingularities

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Equality of two finitely generated germ spans follows by checking that each
generator of either family lies in the span of the other.  This is the form
directly supplied by holomorphic transition matrices on a chart overlap. -/
theorem isInSpanAt_iff_of_generators_mutually_in_span
    {x : M} {p q : ℕ} (f : Fin p → M → ℂ) (g : Fin q → M → ℂ)
    (hfg : ∀ i, IsInSpanAt (n := n) (· ∈ Set.range f) x (g i))
    (hgf : ∀ i, IsInSpanAt (n := n) (· ∈ Set.range g) x (f i))
    (h : M → ℂ) :
    IsInSpanAt (n := n) (· ∈ Set.range g) x h ↔
      IsInSpanAt (n := n) (· ∈ Set.range f) x h := by
  constructor
  · intro hh
    refine Hironaka.RelativePrincipalizationSpan.IsInSpanAt.trans
      (n := n) ?_ hh
    intro s hs
    obtain ⟨i, rfl⟩ := hs
    exact hfg i
  · intro hh
    refine Hironaka.RelativePrincipalizationSpan.IsInSpanAt.trans
      (n := n) ?_ hh
    intro s hs
    obtain ⟨i, rfl⟩ := hs
    exact hgf i

omit [IsComplexManifold n M] in
/-- Finite local holomorphic generators with span-compatible overlaps define a
coherent germ ideal, and a potential given by their local logarithmic norms up
to bounded remainders has analytic singularities of the prescribed type. -/
theorem exists_hasAnalyticSingularitiesOfType_of_localGeneratorDescent
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (U : M → Set M) (hUopen : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (N : M → ℕ) (G : ∀ x, Fin (N x) → M → ℂ)
    (hGdiff : ∀ x i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (U x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ U x, |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ U x →
      phi y = ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal))
    (hspan : ∀ x y, y ∈ U x → ∀ h : M → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range (G y)) y h ↔
        IsInSpanAt (n := n) (· ∈ Set.range (G x)) y h) :
    ∃ a : GermIdeal n M, HasAnalyticSingularitiesOfType phi c a := by
  let a : GermIdeal n M := ⟨fun y h =>
    IsInSpanAt (n := n) (· ∈ Set.range (G y)) y h⟩
  refine ⟨a, hc, ?_, ?_⟩
  · intro x
    refine ⟨U x, hUopen x, hxU x, N x, G x, hGdiff x, ?_⟩
    intro y hy h
    exact hspan x y hy h
  · intro x
    obtain ⟨C, hC⟩ := hRbound x
    refine ⟨U x, hUopen x, hxU x, N x, G x, hGdiff x, ?_, R x, C, hC, ?_⟩
    · intro y hy h
      exact hspan x y hy h
    · intro y hy
      exact hformula x y hy

omit [IsComplexManifold n M] in
/-- The preceding descent package immediately yields analytic singularities. -/
theorem hasAnalyticSingularities_of_localGeneratorDescent
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (U : M → Set M) (hUopen : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (N : M → ℕ) (G : ∀ x, Fin (N x) → M → ℂ)
    (hGdiff : ∀ x i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (U x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ U x, |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ U x →
      phi y = ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal))
    (hspan : ∀ x y, y ∈ U x → ∀ h : M → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range (G y)) y h ↔
        IsInSpanAt (n := n) (· ∈ Set.range (G x)) y h) :
    HasAnalyticSingularities (n := n) phi := by
  obtain ⟨a, ha⟩ :=
    exists_hasAnalyticSingularitiesOfType_of_localGeneratorDescent (n := n) (M := M)
      (phi := phi) c hc U hUopen hxU N G hGdiff R hRbound hformula hspan
  exact ⟨c, a, ha⟩

omit [IsComplexManifold n M] in
/-- A version of local-generator descent whose overlap hypothesis is given
generator by generator.  In applications, the two inclusions are the exact
holomorphic transition-matrix statements, rather than a preassembled equality
of ideal germs. -/
theorem hasAnalyticSingularities_of_localGeneratorInclusions
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (U : M → Set M) (hUopen : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (N : M → ℕ) (G : ∀ x, Fin (N x) → M → ℂ)
    (hGdiff : ∀ x i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (U x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ U x, |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ U x →
      phi y = ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal))
    (hforward : ∀ x y, y ∈ U x → ∀ i,
      IsInSpanAt (n := n) (· ∈ Set.range (G x)) y (G y i))
    (hbackward : ∀ x y, y ∈ U x → ∀ i,
      IsInSpanAt (n := n) (· ∈ Set.range (G y)) y (G x i)) :
    HasAnalyticSingularities (n := n) phi := by
  apply hasAnalyticSingularities_of_localGeneratorDescent c hc U hUopen hxU N G hGdiff
    R hRbound hformula
  intro x y hy h
  exact isInSpanAt_iff_of_generators_mutually_in_span (G x) (G y)
    (hforward x y hy) (hbackward x y hy) h

end

end Hironaka.FiniteGeneratorIdealDescent
