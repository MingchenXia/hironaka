import Hironaka.Analytic.ChartGeneratorLift
import Hironaka.Analytic.FiniteHolomorphicFrameDescent

/-!
# Coherent-ideal descent from chart-coordinate finite presentations

This is the direct bridge from coordinate presentations to the ambient
finite-holomorphic-frame descent theorem.  The coordinate families are lifted
through one selected chart at every point.  The cover, bounded remainders, and
the two actual ambient overlap equations remain hypotheses: a collection of
Bergman coordinate presentations does not by itself produce any of them.
-/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Manifold Topology

namespace Hironaka.ChartCoordinateHolomorphicFrameDescent


open Hironaka.GlobalAnalyticSingularities
open Hironaka.HolomorphicIdealSheaves
open ChartGeneratorLift
open FiniteHolomorphicFrameDescent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Point-indexed coordinate generator presentations descend to one coherent
germ ideal once their chart lifts satisfy the explicitly supplied holomorphic
frame-change germs.  The hypotheses do not claim that an atlas supplies the
cover, the bounded remainder, or either overlap equation. -/
theorem exists_hasAnalyticSingularitiesOfType_of_chartCoordinateMutualHolomorphicGeneratorExpansions
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (e : M → ComplexChart n M) (W : M → Set (ComplexModel n))
    (hWopen : ∀ x, IsOpen (W x))
    (_hWtarget : ∀ x, W x ⊆ (e x).val.target)
    (hcover : ∀ x, x ∈ domain (e x) (W x))
    (N : M → ℕ) (F : ∀ x, Fin (N x) → ComplexModel n → ℂ)
    (hFanalytic : ∀ x i, AnalyticOnNhd ℂ (F x i) (W x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ domain (e x) (W x), |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ domain (e x) (W x) →
      phi y = ((c : ℝ) : EReal) * generatorLog (F x) ((e x).val y) + (R x y : EReal))
    (A : ∀ x y, Fin (N y) → Fin (N x) → M → ℂ)
    (B : ∀ x y, Fin (N x) → Fin (N y) → M → ℂ)
    (hAhol : ∀ x y, y ∈ domain (e x) (W x) → ∀ j i, HolomorphicAt n (A x y j i) y)
    (hBhol : ∀ x y, y ∈ domain (e x) (W x) → ∀ i j, HolomorphicAt n (B x y i j) y)
    (hforward : ∀ x y, y ∈ domain (e x) (W x) → ∀ j,
      generator (e y) (F y) j =ᶠ[𝓝 y] fun z =>
        ∑ i, A x y j i z * generator (e x) (F x) i z)
    (hbackward : ∀ x y, y ∈ domain (e x) (W x) → ∀ i,
      generator (e x) (F x) i =ᶠ[𝓝 y] fun z =>
        ∑ j, B x y i j z * generator (e y) (F y) j z) :
    ∃ a : GermIdeal n M, HasAnalyticSingularitiesOfType phi c a := by
  let G : ∀ x, Fin (N x) → M → ℂ := fun x => generator (e x) (F x)
  have hUopen : ∀ x, IsOpen (domain (e x) (W x)) := fun x =>
    isOpen_domain (e x) (hWopen x)
  have hGdiff : ∀ x i,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (domain (e x) (W x)) := by
    intro x i
    exact generator_mdifferentiableOn_of_analyticOnNhd (e x) (W x) (F x) (hFanalytic x) i
  have hformulaG : ∀ x y, y ∈ domain (e x) (W x) →
      phi y = ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal) := by
    intro x y hy
    simpa only [G, generatorLog_apply] using hformula x y hy
  exact
    exists_hasAnalyticSingularitiesOfType_of_localMutualHolomorphicGeneratorExpansions
      (n := n) (M := M) (phi := phi) c hc
      (fun x => domain (e x) (W x)) hUopen hcover N G hGdiff R hRbound hformulaG
      A B hAhol hBhol hforward hbackward

/-- The chart-coordinate descent theorem also yields ordinary analytic
singularities, with the same explicit cover, remainder, and overlap data. -/
theorem hasAnalyticSingularities_of_chartCoordinateMutualHolomorphicGeneratorExpansions
    {phi : M → EReal} (c : ℚ) (hc : 0 < c)
    (e : M → ComplexChart n M) (W : M → Set (ComplexModel n))
    (hWopen : ∀ x, IsOpen (W x))
    (hWtarget : ∀ x, W x ⊆ (e x).val.target)
    (hcover : ∀ x, x ∈ domain (e x) (W x))
    (N : M → ℕ) (F : ∀ x, Fin (N x) → ComplexModel n → ℂ)
    (hFanalytic : ∀ x i, AnalyticOnNhd ℂ (F x i) (W x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ domain (e x) (W x), |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ domain (e x) (W x) →
      phi y = ((c : ℝ) : EReal) * generatorLog (F x) ((e x).val y) + (R x y : EReal))
    (A : ∀ x y, Fin (N y) → Fin (N x) → M → ℂ)
    (B : ∀ x y, Fin (N x) → Fin (N y) → M → ℂ)
    (hAhol : ∀ x y, y ∈ domain (e x) (W x) → ∀ j i, HolomorphicAt n (A x y j i) y)
    (hBhol : ∀ x y, y ∈ domain (e x) (W x) → ∀ i j, HolomorphicAt n (B x y i j) y)
    (hforward : ∀ x y, y ∈ domain (e x) (W x) → ∀ j,
      generator (e y) (F y) j =ᶠ[𝓝 y] fun z =>
        ∑ i, A x y j i z * generator (e x) (F x) i z)
    (hbackward : ∀ x y, y ∈ domain (e x) (W x) → ∀ i,
      generator (e x) (F x) i =ᶠ[𝓝 y] fun z =>
        ∑ j, B x y i j z * generator (e y) (F y) j z) :
    HasAnalyticSingularities (n := n) phi := by
  obtain ⟨a, ha⟩ :=
    exists_hasAnalyticSingularitiesOfType_of_chartCoordinateMutualHolomorphicGeneratorExpansions
      (n := n) (M := M) (phi := phi) c hc e W hWopen hWtarget hcover N F hFanalytic R
        hRbound hformula A B hAhol hBhol hforward hbackward
  exact ⟨c, a, ha⟩

end

end Hironaka.ChartCoordinateHolomorphicFrameDescent
