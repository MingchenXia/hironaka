import Hironaka.Analytic.NumericalRestrictedVolumeScaffold
import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.DemaillyApproximationSmoothOffPole

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Demailly 1992, in Boucksom's form `bou02-volume:2.6`: the ONE named input

Source: Demailly, *Regularization of closed positive currents and intersection
theory*, J. Algebraic Geom. **1** (1992), Theorem 1.1, as Boucksom quotes it
(`bou02-volume:2.6`, blueprint node `ana:demailly-algebraic-approximation`):

> Let `T` be a closed almost positive `(1,1)`-current on a compact complex `X`
> with a Hermitian form `ω`.  Write `T = α + ddᶜφ` with `α` smooth and `φ` almost
> psh, and suppose given a continuous real form `γ` with `T ≥ γ`.  Then there is
> a sequence `φ_k` of almost psh functions such that
> (i) `φ_k` has algebraic singularities;
> (ii) `φ_k` decreases to `φ` everywhere;
> (iii) the Lelong numbers `ν(φ_k,x)` converge to `ν(φ,x)` uniformly in `x`;
> (iv) setting `T_k = α + ddᶜφ_k`, one has `T_k ≥ γ - ε_kω` with `ε_k ↓ 0`.

## Why this module exists

The human's decision `I-0598` (item 1, 30 Sep) is that Demailly 1992 enters the
project as **one** named input.  Until this module, the project carried it
twice:

* `Hironaka.DemaillyAlgebraicApproximation.exists_algebraicApproximation`
  (`DemaillyAlgebraicApproximationInterface.lean`, run 0089, TN3-LOCUSPROPS),
  with clause (i) in the chartwise `I-0489` convention only, consumed by the
  collar construction of CT22 4.3;
* `Hironaka.KahlerCurrentRegularizationAlgebraicApproximation
  .demailly1992_exists_algebraicApproximation_analyticSingularities` (run 0091,
  TN-CLASSICAL), with clause (i) in both conventions, consumed by target 5a.

The second imported the first, so the first could not be derived from the
second without an import cycle (`I-0601`, finding 3).  This module imports
neither of them (it imported `FirstPass` only until the proof landed; the proof's
module `DemaillyApproximationSmoothOffPole` imports neither either), states the
strong form **once**, and proves the weak form as a projection
(`exists_algebraicApproximation_smoothOffPole`, whose statement is
character-for-character that of `exists_algebraicApproximation`).  Both older
declarations keep their statements and become projections of
`demailly1992_exists_algebraicApproximation`; the second one is rewired in its
own module, the first by its owner.

## What is specialized, and why every specialization WEAKENS the statement

* `γ = 0`: the current `α + ddᶜψ` is positive.
* Clause (i) is asked in two forms, both implied by "algebraic singularities":
  globally (`HasAnalyticSingularities`: a positive **rational** coefficient
  along a coherent ideal with a bounded remainder — Demailly's `φ_k` has
  coefficient `1/k` along the multiplier ideal `𝓘(kφ)`, coherent by Nadel), and
  chartwise in the `I-0489` convention (`HasManifoldAnalyticSingularitiesSmoothOffPole`:
  bounded remainder, `C^∞` off the poles; Demailly's `φ_k` is smooth off its
  pole set, which is the zero set of the Bergman sections).
* Clause (ii) is `Antitone` together with `⨅ k, ψ_k x = ψ x`.
* Clause (iii) is OMITTED.
* Clause (iv) is `0 ≤ δ_k` with `δ_k → 0`, not "decreasing".

Degenerate cases (hard rule 4): `ψ` is never identically `-∞`
(`IsThetaPshPotential` contains `LocallyNondegenerate`); on an empty `M` every
clause is vacuous; in dimension `0` every function is smooth and the constant
sequence works.

## Not a restatement of a consumer (`I-0166`, `I-0194`)

The statement quantifies over an arbitrary closed real `(1,1)`-form, an arbitrary
`θ`-psh potential and an arbitrary Kähler background; it mentions no Kähler
current, class, Lelong number, pole set, subvariety or gluing datum.  Its
consumers (Boucksom 3.17 for target 5a; the CT22 4.3 collar construction; the
smoothing of bounded potentials) each add their own construction on top.
-/

open Set Filter
open scoped Topology

namespace Hironaka.Demailly1992AlgebraicApproximation

open Hironaka.PositiveClasses Hironaka.NumericalRestrictedVolumeScaffold
  Hironaka.GlobalAnalyticSingularities

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly 1992 Theorem 1.1, in Boucksom's form `bou02-volume:2.6`, with `γ = 0` and
clause (i) in both conventions — PROVED** (programme `TN.3.3.DEMPROVE`:
`DemaillyApproximationSmoothOffPole.exists_algebraicApproximation`, Demailly's explicit Bergman
kernel sequence on a fixed chart cover).
A positive current `α + ddᶜψ` on a compact Kähler manifold is approximated from
above by currents with algebraic singularities, at an asymptotically vanishing
loss of positivity.  This is the project's single named form of the theorem
(`I-0598`). -/
theorem demailly1992_exists_algebraicApproximation [CompactSpace M]
    (omega : KahlerBackground n M) (alpha : ClosedRealOneOneForm n M) (psi : M → EReal)
    (hpsi : IsThetaPshPotential alpha.val psi) :
    ∃ (psiSeq : ℕ → M → EReal) (delta : ℕ → ℝ),
      -- (i) analytic singularities, globally and in the `I-0489` convention
      (∀ k, HasAnalyticSingularities (n := n) (psiSeq k)) ∧
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (psiSeq k)) ∧
      -- (ii) decreasing to `psi` everywhere
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = psi x) ∧
      -- (iv) the curvature loss, with a vanishing constant
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (alpha + delta k • omega.form).val (psiSeq k) :=
  DemaillyApproximationSmoothOffPole.exists_algebraicApproximation omega alpha psi hpsi

/-- **The `I-0489`-convention form is a projection.**  Its statement is that of
`DemaillyAlgebraicApproximation.exists_algebraicApproximation`, character for
character, so that declaration can be proved as
`Demailly1992AlgebraicApproximation.exists_algebraicApproximation_smoothOffPole
omega alpha psi hpsi`. -/
theorem exists_algebraicApproximation_smoothOffPole [CompactSpace M]
    (omega : KahlerBackground n M) (alpha : ClosedRealOneOneForm n M) (psi : M → EReal)
    (hpsi : IsThetaPshPotential alpha.val psi) :
    ∃ (psiSeq : ℕ → M → EReal) (delta : ℕ → ℝ),
      -- (i) analytic singularities, in the `I-0489` convention
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (psiSeq k)) ∧
      -- (ii) decreasing to `psi` everywhere
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = psi x) ∧
      -- (iv) the curvature loss, with a vanishing constant
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (alpha + delta k • omega.form).val (psiSeq k) := by
  obtain ⟨psiSeq, delta, -, hsmooth, hanti, hinf, hdnn, hdlim, hpsh⟩ :=
    demailly1992_exists_algebraicApproximation omega alpha psi hpsi
  exact ⟨psiSeq, delta, hsmooth, hanti, hinf, hdnn, hdlim, hpsh⟩

end

end Hironaka.Demailly1992AlgebraicApproximation
