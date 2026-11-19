import Hironaka.Analytic.Demailly1992AlgebraicApproximation
import Hironaka.Analytic.DemaillyAlgebraicApproximationInterface
import Hironaka.Analytic.AnalyticSingularityPoleLelong
import Hironaka.Analytic.KahlerCurrentMax
import Hironaka.Analytic.KahlerCurrentPerturbation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Target 5a from Demailly's approximation theorem (route (iii))

Source: Demailly, *Regularization of closed positive currents and intersection
theory*, J. Algebraic Geom. **1** (1992), Theorem 1.1, in the form Boucksom
quotes it (`bou02-volume:2.6`, blueprint node
`ana:demailly-algebraic-approximation`); the deduction is the one in the proof of
Boucksom, *Divisorial Zariski decompositions*, Theorem 3.17.

## Why this module exists

The human's decision of 30 Sep (`I-0598`, answering `I-0565`) fixes **route
(iii)** as the primary route to target 5a: derive

  `KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`

from Demailly's approximation theorem, *exactly as Boucksom does*, so that
Demailly 1992 is ONE named input in the project rather than two (the previous
route went through `DemaillyRegularizedMaxBergmanDataInterface`, the ordered
regularized-max Bergman record, whose stage-zero obstruction is recorded in
`I-0565`; per `I-0459` those files stay in the tree, superseded).

## Boucksom's deduction, and what it costs

Let `T = θ + ddᶜφ ≥ ω'` be a Kähler current in `α`.  Apply the approximation
theorem to the **positive** current `T - ω' = (θ - ω') + ddᶜφ`, i.e. with
`γ = 0` and the smooth form `θ - ω'`.  It returns `φ_k ↓ φ` with analytic
singularities and

  `(θ - ω') + δ_k ω' + ddᶜφ_k ≥ 0`,   `δ_k ↓ 0`.

For `δ_k < 1` this reads `θ + ddᶜφ_k ≥ (1 - δ_k) ω'`, so `θ + ddᶜφ_k` is again a
Kähler current in the **same** class `α` — the representative is untouched, only
the Kähler lower bound shrinks.  A pole of `φ_k` has positive Lelong number
because `φ_k` has analytic singularities
(`AnalyticSingularityPoleLelong`), and `ν(φ_k, x) ≤ ν(φ, x)` because
`φ_k ≥ φ` (`KahlerCurrentMax.lelongNumber_le_of_eventually_le`).  Hence the
pole set of `φ_k` lies in the positive-Lelong locus of `φ`, which is the
conclusion.

Note that only `δ_k → 0` is used, and only through "some index has `δ_k < 1`";
clause (iii) of the published theorem (uniform convergence of Lelong numbers) is
**not** needed — the comparison `ν(φ_k) ≤ ν(φ)` comes from `φ_k ≥ φ` alone, and
that is clause (ii).

## The one clause that had to be restored

`Hironaka.DemaillyAlgebraicApproximation.exists_algebraicApproximation` states
clause (i) only in the chartwise `I-0489` convention
(`HasManifoldAnalyticSingularitiesSmoothOffPole`), because its consumer — the
collar construction of CT22 4.3 — needs no more.  Target 5a needs more: both
its `HasAnalyticSingularities` conclusion and the positive-Lelong step go
through the **global** form of analytic singularities (a positive rational
coefficient and a coherent ideal).  That is what Demailly's clause (i) actually
says — "algebraic singularities" — so it is restored here, exactly as `I-0598`
authorises for a clause of the published statement, and nothing else is added:
`γ = 0`, clause (iii) omitted, clause (iv) as `0 ≤ δ_k → 0`.

The interface below is therefore the published theorem with clause (i) in both
forms.  Consequently `exists_algebraicApproximation`'s own statement is a
**corollary** of it, proved here as `exists_algebraicApproximation_of_stronger`:
the two are not two independent assumptions.

**Run 0094: the `sorry` moved to a base module.**  This module imports
`DemaillyAlgebraicApproximationInterface`, so that module could not import this
one to make its own `sorry` a projection.  The strong statement now lives,
verbatim and once, in `Hironaka.Demailly1992AlgebraicApproximation`
(`demailly1992_exists_algebraicApproximation`), which imports `FirstPass` only;
`demailly1992_exists_algebraicApproximation_analyticSingularities` below keeps its
statement byte-identical and is proved as that projection, so this module has no
`sorry` of its own.  The older interface's owner can make
`exists_algebraicApproximation` a projection of the same base declaration
(`Demailly1992AlgebraicApproximation.exists_algebraicApproximation_smoothOffPole`).

## Not a restatement of its consumer (`I-0166`, `I-0194`)

The interface quantifies over an arbitrary closed real `(1,1)`-form, an
arbitrary `θ`-psh potential and an arbitrary Kähler background; it mentions no
Kähler current, no class, no Lelong number and no pole set.  Its consumer below
adds the shift by `ω'`, the choice of index, the reconstruction of a Kähler
current in the same class, and the two Lelong steps.  Both proved halves are
sorry-free given the interface.
-/

open Set Filter
open scoped Topology

namespace Hironaka.KahlerCurrentRegularizationAlgebraicApproximation

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold Hironaka.GlobalAnalyticSingularities
open Hironaka.AnalyticSingularityPoleLelong
open Hironaka.DemaillyAlgebraicApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly 1992 Theorem 1.1, in Boucksom's form `bou02-volume:2.6`, with
`γ = 0` and clause (i) in both conventions** — since run 0094 a projection of the
project's single named form,
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation`.

Identical to `DemaillyAlgebraicApproximation.exists_algebraicApproximation`
except that clause (i) is also asked in the *global* form of analytic
singularities — a positive rational coefficient along a coherent ideal with a
bounded remainder — which is what "algebraic singularities" means in the
published statement.  Clause (iii) is still omitted and `γ` is still `0`, so
every deviation from the source still weakens it. -/
theorem demailly1992_exists_algebraicApproximation_analyticSingularities
    [CompactSpace M] (omega : KahlerBackground n M)
    (alpha : ClosedRealOneOneForm n M) (psi : M → EReal)
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
  Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation
    omega alpha psi hpsi

/-- **Proved half 1: the `I-0489`-convention interface is a corollary.**  Drop
the global clause (i).  This is the statement of
`DemaillyAlgebraicApproximation.exists_algebraicApproximation` verbatim, so the
project does not carry two independent Demailly assumptions. -/
theorem exists_algebraicApproximation_of_stronger [CompactSpace M]
    (omega : KahlerBackground n M) (alpha : ClosedRealOneOneForm n M)
    (psi : M → EReal) (hpsi : IsThetaPshPotential alpha.val psi) :
    ∃ (psiSeq : ℕ → M → EReal) (delta : ℕ → ℝ),
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (psiSeq k)) ∧
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = psi x) ∧
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (alpha + delta k • omega.form).val (psiSeq k) := by
  obtain ⟨psiSeq, delta, -, hsmooth, hanti, hinf, hdnn, hdlim, hpsh⟩ :=
    demailly1992_exists_algebraicApproximation_analyticSingularities omega alpha psi hpsi
  exact ⟨psiSeq, delta, hsmooth, hanti, hinf, hdnn, hdlim, hpsh⟩

/-- **Proved half 2: target 5a, by Boucksom's argument.**  Every Kähler current
in a class on a compact complex manifold is dominated by a Kähler current in the
*same* class with analytic singularities whose pole set lies in the
positive-Lelong locus of the original potential.

The class is unchanged because the representative is unchanged: only the Kähler
lower bound shrinks from `ω'` to `(1 - δ_k) ω'`. -/
theorem exists_kahlerCurrent_poleSet_subset_lelongNumber_pos [CompactSpace M]
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  obtain ⟨psiSeq, delta, hana, hsmooth, -, hinf, -, hdlim, hpsh⟩ :=
    demailly1992_exists_algebraicApproximation_analyticSingularities
      T.lowerBound (T.representative - T.lowerBound.form) T.potential T.strictlyPsh
  -- some index has `δ_k < 1`
  have hev : ∀ᶠ k in atTop, delta k < 1 :=
    hdlim (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨k, hk⟩ := hev.exists
  have hpos : (0 : ℝ) < 1 - delta k := by linarith
  have hform : T.representative - (KahlerBackground.smul hpos T.lowerBound).form
      = (T.representative - T.lowerBound.form) + delta k • T.lowerBound.form := by
    rw [KahlerBackground.smul_form, sub_smul, one_smul]
    abel
  refine ⟨{ representative := T.representative
            represents := T.represents
            potential := psiSeq k
            lowerBound := KahlerBackground.smul hpos T.lowerBound
            strictlyPsh := by rw [hform]; exact hpsh k },
    hana k, hsmooth k, ?_⟩
  intro x hx
  have hposLelong : 0 < lelongNumber (n := n) (psiSeq k) x :=
    poleSet_subset_lelongNumber_pos_of_hasAnalyticSingularities (hana k) hx
  have hle : lelongNumber (n := n) (psiSeq k) x
      ≤ lelongNumber (n := n) T.potential x :=
    KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (Eventually.of_forall fun y => le_of_iInf_eq hinf k y)
  exact lt_of_lt_of_le hposLelong hle

end

end Hironaka.KahlerCurrentRegularizationAlgebraicApproximation
