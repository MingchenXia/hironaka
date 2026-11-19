import Hironaka.Analytic.PrincipalizationCopy4StepFiveCoreReduction
import Hironaka.Analytic.CoherentIdealWeight
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.IdealComparisonResidual
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Analytic.InvertibleIdealCoherent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Producers for the two ideal-side ambient fields of Copy-4 Step 5

Source: Copy-4, `prop:principalization` Step 5 and `sec:fixed-data`
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1503-1523`,
`:1845-1984`); blueprint `ana:principalization-data`.

## What this closes

`Copy4StepFiveExceptionalWeightData`
(`PrincipalizationCopy4StepFiveCoreReduction.lean:232`) carries four ambient
fields.  One of them, `ambientPhiR_source`, was given a producer in
`Hironaka.AmbientPhiRSourceOfAnalyticSingularities`.  The two *ideal-side* ones,

* `ambientGM_source : AmbientGMLowerSource n base M pi psiBM psiGM`, and
* `ambientIV_source : AmbientIVLowerSource n base M pi psiIV psiH psiIW`,

had **no producer at all**: `PrincipalizationCopy4StepFiveCoreReduction` states
them, derives `MoreSingularOn` from them, and every route to Step 5 assumed
them outright.  This module builds both, sorry-free, from data that is
available on the modification side:

* a *coherent ideal* on the base together with a smooth `π`, for
  `AmbientGMLowerSource`;
* the `eq:IV-H` ideal identity `π^*𝔞 = 𝔥 · 𝔟` with `𝔥`, `𝔟` coherent, for
  `AmbientIVLowerSource`.

Nothing analytic is assumed.  The only inputs are
`CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent` (every
coherent ideal on a compact manifold carries a weight, at coefficient `1`),
`GermIdealPullbackCalculus.isCoherent_pullback`, and
`IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul`.

## Why the coefficient is the content

Both structures insist that *all* their weights carry one and the same positive
rational coefficient `c`: that is what the whole `O(1)` calculus of
`Pending/IdealWeightComparison` needs before it can compare them.  The weight
constructor delivers coefficient `1` and nothing else, so a producer has to
manufacture the common coefficient.  It is obtained by rescaling
(`hasAnalyticSingularitiesOfType_smul`), which moves the coefficient and leaves
the *ideal* — hence the comparison — untouched.  In `AmbientGMLowerSource` the
coefficient is dictated from outside, by the presentation of `ψ_{𝔅_M}` that the
ambient half of Step 5 already fixed; in `AmbientIVLowerSource` all three
weights are produced here, so `c` may be chosen freely and is quantified.

## What is *not* claimed

These are producers for two fields, not for `Copy4StepFiveExceptionalWeightData`
itself.  That structure couples its fields: `ψ_{G̃_M}` also has to satisfy
`bound_GM` and `divisor_weight`, and `ψ_{𝓘_W}` has to satisfy
`psiIW_zeroLocus`.  A weight produced existentially here is a witness for the
ambient field alone.  The `_of_presentation`/`_of_presentations` constructors
are the form in which a *coupled* construction will use them: they take the
weights as given and check only the ideal-theoretic content.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.AmbientIdealSourcesOfCoherentIdeals

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.BlowupSequences
open Hironaka.CoherentIdealWeight
open Hironaka.GermIdealPullbackCalculus
open Hironaka.IdealComparisonResidual
open Hironaka.PrincipalizationCopy4StepFiveCoreReduction

universe u

noncomputable section

variable {n : ℕ} {base : Type u} [TopologicalSpace base]
  [ChartedSpace (ComplexModel n) base] [IsComplexManifold n base]
  {target : Type u} [TopologicalSpace target]
  [ChartedSpace (ComplexModel n) target] [IsComplexManifold n target]

/-! ### A weight at a prescribed coefficient -/

/-- **A coherent ideal carries a weight at any prescribed positive
coefficient.**  `CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent`
produces one at coefficient `1`; rescaling by `c` moves the coefficient and
keeps the ideal, which is what every structure below needs. -/
theorem exists_hasAnalyticSingularitiesOfType_coefficient [CompactSpace target]
    {𝔞 : GermIdeal n target} (h𝔞 : 𝔞.IsCoherent) {c : ℚ} (hc : 0 < c) :
    ∃ psi : target → EReal, HasAnalyticSingularitiesOfType (n := n) psi c 𝔞 := by
  obtain ⟨psi, hpsi⟩ := exists_hasAnalyticSingularitiesOfType_of_isCoherent h𝔞
  refine ⟨fun y => ((c : ℝ) : EReal) * psi y, ?_⟩
  have h := hasAnalyticSingularitiesOfType_smul (n := n) hc hpsi
  rwa [mul_one] at h

/-! ### `AmbientGMLowerSource` -/

/-- The divisor/ideal comparison datum from a presentation of the pullback
ideal.  Only the ideal-theoretic content is checked here: `ψ_{G̃_M}` presents
`𝔅_M 𝒪_Y` at the coefficient `ψ_{𝔅_M}` already uses. -/
def ambientGMLowerSource_of_presentation
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiBM : base → EReal} {psiGM : target → EReal} {c : ℚ}
    {idealBM : GermIdeal n base}
    (hBM : HasAnalyticSingularitiesOfType (n := n) psiBM c idealBM)
    (hGM : HasAnalyticSingularitiesOfType (n := n) psiGM c
      (GermIdeal.pullback (m := n) pi idealBM)) :
    AmbientGMLowerSource n base target pi psiBM psiGM where
  c := c
  pi_smooth := hpi
  idealBM := idealBM
  idealGM := GermIdeal.pullback (m := n) pi idealBM
  BM_presentation := hBM
  GM_presentation := hGM
  factorization := rfl

/-- **The `ψ_{G̃_M}` ambient field of Copy-4 Step 5 has a producer.**  A weight
`ψ_{𝔅_M}` with analytic singularities on the base and a smooth `π` already
determine a divisor weight on `Y` presenting `𝔅_M 𝒪_Y`, hence the whole
structure.  No property of `π` beyond smoothness is used. -/
theorem exists_ambientGMLowerSource [CompactSpace target]
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiBM : base → EReal} {c : ℚ} {idealBM : GermIdeal n base}
    (hBM : HasAnalyticSingularitiesOfType (n := n) psiBM c idealBM) :
    ∃ psiGM : target → EReal,
      Nonempty (AmbientGMLowerSource n base target pi psiBM psiGM) := by
  obtain ⟨psiGM, hGM⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient
      (isCoherent_pullback (m := n) hpi hBM.2.1) hBM.1
  exact ⟨psiGM, ⟨ambientGMLowerSource_of_presentation hpi hBM hGM⟩⟩

/-- The Step-5 comparison `ψ_{G̃_M} ≤ ψ_{𝔅_M} ∘ π + O(1)` for the weight the
previous theorem produces. -/
theorem exists_moreSingularOn_comp_of_isCoherent [CompactSpace target]
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiBM : base → EReal} {c : ℚ} {idealBM : GermIdeal n base}
    (hBM : HasAnalyticSingularitiesOfType (n := n) psiBM c idealBM) :
    ∃ psiGM : target → EReal,
      HasAnalyticSingularitiesOfType (n := n) psiGM c
        (GermIdeal.pullback (m := n) pi idealBM) ∧
      MoreSingularOn psiGM (fun y => psiBM (pi y)) univ := by
  obtain ⟨psiGM, hGM⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient
      (isCoherent_pullback (m := n) hpi hBM.2.1) hBM.1
  exact ⟨psiGM, hGM,
    (ambientGMLowerSource_of_presentation hpi hBM hGM).moreSingularOn⟩

/-! ### `AmbientIVLowerSource` -/

/-- The `eq:IV-H` datum from three presentations at one coefficient and the
ideal identity `π^*𝔞_{IV} = 𝔥 · 𝔟`. -/
def ambientIVLowerSource_of_presentations
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiIV : base → EReal} {psiH psiIW : target → EReal} {c : ℚ}
    {idealIV : GermIdeal n base} {idealH idealIW : GermIdeal n target}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (hH : HasAnalyticSingularitiesOfType (n := n) psiH c idealH)
    (hIW : HasAnalyticSingularitiesOfType (n := n) psiIW c idealIW)
    (hfact : GermIdeal.pullback (m := n) pi idealIV = idealH.mul idealIW) :
    AmbientIVLowerSource n base target pi psiIV psiH psiIW where
  c := c
  pi_smooth := hpi
  idealIV := idealIV
  idealH := idealH
  idealIW := idealIW
  IV_presentation := hIV
  H_presentation := hH
  IW_presentation := hIW
  factorization := hfact

/-- **The `eq:IV-H` ambient field of Copy-4 Step 5 has a producer.**  The
ideal identity `π^*𝔞_{IV} = 𝔥 · 𝔟` with both factors coherent is enough: the
three weights are then produced at the coefficient of `ψ_{IV}`.

`𝔥` is Copy-4's `𝒪(-H)` and `𝔟` its `𝓘_{W}`; on the modification side both are
coherent — the first by `DivisorMetric.isCoherent_of_isInvertible`, the second
by `VanishingIdealCoherent.isCoherent_vanishingIdeal`. -/
theorem exists_ambientIVLowerSource [CompactSpace target]
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiIV : base → EReal} {c : ℚ} {idealIV : GermIdeal n base}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    {idealH idealIW : GermIdeal n target}
    (hHcoh : idealH.IsCoherent) (hIWcoh : idealIW.IsCoherent)
    (hfact : GermIdeal.pullback (m := n) pi idealIV = idealH.mul idealIW) :
    ∃ psiH psiIW : target → EReal,
      Nonempty (AmbientIVLowerSource n base target pi psiIV psiH psiIW) := by
  obtain ⟨psiH, hH⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient hHcoh hIV.1
  obtain ⟨psiIW, hIW⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient hIWcoh hIV.1
  exact ⟨psiH, psiIW,
    ⟨ambientIVLowerSource_of_presentations hpi hIV hH hIW hfact⟩⟩

/-- **The same, in the shape the modification side delivers it.**  `π` is the
modification, `H` the exceptional divisor of clause (i) of
`lem:relative-principalization`, and `W'` the strict transform; the hypothesis
is exactly that clause.  Both weights on `Y` are produced, together with the
presentations that the Step-5 structure's own `psiIW_presentation` field
records for `ψ_{𝓘_{W'}}`. -/
theorem exists_ambientIVLowerSource_of_vanishingIdeal_factorization
    [CompactSpace target]
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiIV : base → EReal} {c : ℚ} {idealIV : GermIdeal n base}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (H : EffectiveDivisor n target) {W' : Set target}
    (hW' : IsClosedSubmanifold n W')
    (hfact : GermIdeal.pullback (m := n) pi idealIV
      = H.ideal.mul (vanishingIdeal (n := n) W')) :
    ∃ psiH psiIW : target → EReal,
      HasAnalyticSingularitiesOfType (n := n) psiIW c
        (vanishingIdeal (n := n) W') ∧
      Nonempty (AmbientIVLowerSource n base target pi psiIV psiH psiIW) := by
  obtain ⟨psiH, hH⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient
      (DivisorMetric.isCoherent_of_isInvertible H.isInvertible) hIV.1
  obtain ⟨psiIW, hIW⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hW') hIV.1
  exact ⟨psiH, psiIW, hIW,
    ⟨ambientIVLowerSource_of_presentations hpi hIV hH hIW hfact⟩⟩

/-- `eq:IV-H` itself, for the weights just produced: `ψ_H + ψ_{𝓘_{W'}}` is more
singular than `ψ_{IV} ∘ π`, which is the direction Step 5 uses to remove the
residual ideal weight on a collar. -/
theorem exists_moreSingularOn_add_comp [CompactSpace target]
    {pi : target → base}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiIV : base → EReal} {c : ℚ} {idealIV : GermIdeal n base}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    {idealH idealIW : GermIdeal n target}
    (hHcoh : idealH.IsCoherent) (hIWcoh : idealIW.IsCoherent)
    (hfact : GermIdeal.pullback (m := n) pi idealIV = idealH.mul idealIW) :
    ∃ psiH psiIW : target → EReal,
      MoreSingularOn (fun y => psiH y + psiIW y) (fun y => psiIV (pi y)) univ := by
  obtain ⟨psiH, psiIW, ⟨d⟩⟩ :=
    exists_ambientIVLowerSource hpi hIV hHcoh hIWcoh hfact
  exact ⟨psiH, psiIW, d.moreSingularOn⟩

end

end Hironaka.AmbientIdealSourcesOfCoherentIdeals
