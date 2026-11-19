import Hironaka.Analytic.CollarExhaustionDini
import Hironaka.Analytic.Demailly1992AlgebraicApproximation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Demailly's approximation with algebraic singularities: the collar construction's form

This module states the form of the one classical theorem the collar construction
of CT22, Lemma 4.3, Step 3 rests on, and nothing else.  Since run 0096 it is **no
longer a separate assumption**: the theorem is a projection of the project's single
named form of Demailly 1992,
`Hironaka.Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation`
(`I-0598` item 1), through
`Demailly1992AlgebraicApproximation.exists_algebraicApproximation_smoothOffPole`, whose
statement is this one character for character.  The statement below is unchanged.

It is Demailly's regularization
theorem (*Regularization of closed positive currents and intersection theory*,
J. Algebraic Geom. **1** (1992)), in the form Boucksom quotes it
(`bou02-volume:2.6`, blueprint node `ana:demailly-algebraic-approximation`):

> Let `T` be a closed almost positive `(1,1)`-current on a compact complex `X`
> with a Hermitian form `ω`.  Write `T = α + ddᶜφ` with `α` smooth and `φ` almost
> psh, and suppose given a continuous real form `γ` with `T ≥ γ`.  Then there is
> a sequence `φ_k` of almost psh functions such that
> (i) `φ_k` has algebraic singularities;
> (ii) `φ_k` decreases to `φ` everywhere;
> (iii) the Lelong numbers `ν(φ_k,x)` converge to `ν(φ,x)` uniformly in `x`;
> (iv) setting `T_k = α + ddᶜφ_k`, one has `T_k ≥ γ - ε_kω` with `ε_k ↓ 0`.

## What is specialized, and why every specialization WEAKENS the statement

* `γ = 0`, i.e. the current is genuinely positive.  That is the only case the
  collar construction uses (`ψ` is `(θ+ε₀ω)`-plurisubharmonic).
* Clause (i) is asked in the convention the human fixed in `I-0489`
  (`HasManifoldAnalyticSingularitiesSmoothOffPole`: bounded remainder, `C^∞` off
  the poles, positive REAL coefficient) rather than "algebraic singularities"
  (rational coefficient, remainder smooth across the poles).  The source's
  conclusion implies this one.
* Clause (ii) is `Antitone` together with `⨅ k, ψ_k x = ψ x`, which is exactly
  "decreases to `ψ` everywhere".
* Clause (iii) is OMITTED: the construction never uses Lelong numbers, and
  omitting a clause of an assumed input makes the assumption weaker.
* Clause (iv) is asked as `0 ≤ ε_k` with `ε_k → 0`, not as a decreasing
  sequence: only `∃ k, ε_k ≤ Λ/2` is ever used.

So the Lean statement below is implied by the source theorem clause by clause;
it is not a reformulation of its consumer.  The consumer is the collar
construction, which adds the exhaustion, the cut-off, the downward shift and the
regularized-max gluing — none of which is in this statement.
-/

open Set Filter
open scoped Topology

namespace Hironaka.DemaillyAlgebraicApproximation

open Hironaka.PositiveClasses Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly 1992, in Boucksom's form `bou02-volume:2.6`, with `γ = 0` and
clause (i) in the `I-0489` convention.**  A positive current `α + ddᶜψ` on a
compact Kähler manifold is approximated from above by currents with analytic
singularities, at an asymptotically vanishing loss of positivity.

Not an assumption of its own: it projects the single named form
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation`
(drop the global clause (i)). -/
theorem exists_algebraicApproximation [CompactSpace M] (omega : KahlerBackground n M)
    (alpha : ClosedRealOneOneForm n M) (psi : M → EReal)
    (hpsi : IsThetaPshPotential alpha.val psi) :
    ∃ (psiSeq : ℕ → M → EReal) (delta : ℕ → ℝ),
      -- (i) analytic singularities, in the `I-0489` convention
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (psiSeq k)) ∧
      -- (ii) decreasing to `psi` everywhere
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = psi x) ∧
      -- (iv) the curvature loss, with a vanishing constant
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (alpha + delta k • omega.form).val (psiSeq k) := by
  exact Demailly1992AlgebraicApproximation.exists_algebraicApproximation_smoothOffPole
    omega alpha psi hpsi

/-! ## The two free consequences of clause (ii) -/

variable {psiSeq : ℕ → M → EReal} {psi : M → EReal}

/-- A decreasing sequence with infimum `psi` dominates `psi` at every index. -/
theorem le_of_iInf_eq (hinf : ∀ x, ⨅ k, psiSeq k x = psi x) (k : ℕ) (x : M) :
    psi x ≤ psiSeq k x := by
  rw [← hinf x]
  exact iInf_le _ k

/-- **No new poles.**  Since the approximants dominate `psi`, their pole sets are
contained in that of `psi`.  This is clause (i) of the CT22 statement. -/
theorem poleSet_subset_of_iInf_eq (hinf : ∀ x, ⨅ k, psiSeq k x = psi x) (k : ℕ) :
    poleSet (psiSeq k) ⊆ poleSet psi := by
  intro x hx
  have h := le_of_iInf_eq hinf k x
  rw [mem_poleSet] at hx ⊢
  exact le_bot_iff.mp (hx ▸ h)

/-- The pointwise limit, for Dini's theorem. -/
theorem tendsto_of_antitone_of_iInf_eq (hanti : ∀ x, Antitone fun k => psiSeq k x)
    (hinf : ∀ x, ⨅ k, psiSeq k x = psi x) (x : M) :
    Tendsto (fun k => psiSeq k x) atTop (𝓝 (psi x)) := by
  rw [← hinf x]
  exact tendsto_atTop_iInf (hanti x)

end

end Hironaka.DemaillyAlgebraicApproximation
