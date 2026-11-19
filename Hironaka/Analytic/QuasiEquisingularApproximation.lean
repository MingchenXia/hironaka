import Hironaka.Analytic.PotentialTheory.AnalyticSingularitiesBasic
import Hironaka.Analytic.PositiveClasses
import Hironaka.Analytic.PotentialTheory.MultiplierIdealsBasic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option autoImplicit false

/-!
# Quasi-equisingular approximation data

This file encodes the actual conditions in DX24, Definition `def:equising`,
and Hironaka, Definition 1.6.4. An approximation varies the background by a
nonnegative decreasing error, decreases pointwise to the original potential,
has analytic singularity type term by term, and eventually satisfies every
strictly separated multiplier-ideal inclusion.

Multiplier ideals are represented chartwise by their defining weighted
holomorphic germs. This is an actual membership predicate, not an assumed
coherent sheaf. Existence of quasi-equisingular approximations and coherence
remain analytic theorems outside the verified core.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.QuasiEquisingularApproximation

noncomputable section

open Hironaka.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A global potential has analytic singularity type when each actual chart
germ has the manuscript's positive rational logarithmic presentation with
bounded remainder. -/
def HasManifoldAnalyticSingularityType (u : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    HasAnalyticSingularityTypeAt (chartFunction u e) z

/-- Inclusion of local multiplier-ideal germs, tested on genuine holomorphic
germs against the canonical Borel--Haar measure on the complex chart model. -/
def MultiplierIdealIncluded
    (φ : M → EReal) (c : ℝ) (ψ : M → EReal) (d : ℝ) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∀ f : ComplexModel n → ℂ, AnalyticAt ℂ f z →
      MultiplierIntegrableAt (chartFunction φ e) c f z volume →
        MultiplierIntegrableAt (chartFunction ψ e) d f z volume

/-- A nonnegative real sequence decreases to zero. -/
def NonnegativeDecreasesToZero (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ ε k) ∧ Antitone ε ∧ Tendsto ε atTop (𝓝 0)

/-- Pointwise decreasing convergence of extended-real potentials, including
at their negative-infinite poles. -/
def DecreasesPointwiseTo (uSeq : ℕ → M → EReal) (u : M → EReal) : Prop :=
  (∀ x, Antitone fun k => uSeq k x) ∧
    ∀ x, Tendsto (fun k => uSeq k x) atTop (𝓝 (u x))

/-- The complete first-pass quasi-equisingular approximation predicate.

The last clause is `I(λ' uₖ) ⊆ I(λ u)` for every `0 < λ < λ'`, eventually in
`k`. No singularity-metric convergence or trace conclusion is included. -/
def IsQuasiEquisingularApproximation
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (u : M → EReal) (ε : ℕ → ℝ) (uSeq : ℕ → M → EReal) : Prop :=
  IsThetaPshPotential θ.val u ∧
    NonnegativeDecreasesToZero ε ∧
    (∀ k, IsThetaPshPotential (θ + ε k • omega.form).val (uSeq k)) ∧
    (∀ k, HasManifoldAnalyticSingularityType (n := n) (uSeq k)) ∧
    DecreasesPointwiseTo uSeq u ∧
    ∀ c d : ℝ, 0 < c → c < d →
      ∀ᶠ k in atTop, MultiplierIdealIncluded (n := n) (uSeq k) d u c

variable {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
  {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}

theorem IsQuasiEquisingularApproximation.target
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) :
    IsThetaPshPotential θ.val u := h.1

theorem IsQuasiEquisingularApproximation.error
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) :
    NonnegativeDecreasesToZero ε := h.2.1

theorem IsQuasiEquisingularApproximation.error_nonneg
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) (k : ℕ) :
    0 ≤ ε k := h.2.1.1 k

theorem IsQuasiEquisingularApproximation.error_antitone
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) :
    Antitone ε := h.2.1.2.1

theorem IsQuasiEquisingularApproximation.error_tendsto
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) :
    Tendsto ε atTop (𝓝 0) := h.2.1.2.2

theorem IsQuasiEquisingularApproximation.term
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) (k : ℕ) :
    IsThetaPshPotential (θ + ε k • omega.form).val (uSeq k) := h.2.2.1 k

theorem IsQuasiEquisingularApproximation.term_hasAnalyticSingularityType
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) (k : ℕ) :
    HasManifoldAnalyticSingularityType (n := n) (uSeq k) := h.2.2.2.1 k

theorem IsQuasiEquisingularApproximation.decreasesPointwise
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) :
    DecreasesPointwiseTo uSeq u := h.2.2.2.2.1

theorem IsQuasiEquisingularApproximation.term_antitone
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) (x : M) :
    Antitone fun k => uSeq k x := h.2.2.2.2.1.1 x

theorem IsQuasiEquisingularApproximation.term_tendsto
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) (x : M) :
    Tendsto (fun k => uSeq k x) atTop (𝓝 (u x)) := h.2.2.2.2.1.2 x

theorem IsQuasiEquisingularApproximation.eventually_multiplierIdealIncluded
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∀ᶠ k in atTop, MultiplierIdealIncluded (n := n) (uSeq k) d u c :=
  h.2.2.2.2.2 c d hc hcd

end

end Hironaka.QuasiEquisingularApproximation
