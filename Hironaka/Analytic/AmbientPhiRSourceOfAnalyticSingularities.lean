import Hironaka.Analytic.PrincipalizationCopy4StepFiveCoreReduction
import Hironaka.Analytic.UniformNullstellensatzPowerInterface
import Hironaka.Analytic.IdealComparisonResidual

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Building Copy-4's `Φ_R` ambient source from a current with analytic singularities

Source: Copy-4, `sec:fixed-data` (`eq:def-R`, `eq:PhiR-lower`)
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1503-1507`);
blueprint `ana:principalization-data`.

## What this closes

`AmbientPhiRLowerSource` (`PrincipalizationCopy4StepFiveCoreReduction.lean:54`)
is one of the four ambient fields of `Copy4StepFiveExceptionalWeightData`, and
until now it had **no producer at all**: every route to it assumed it.  Run 0082
concluded from that that the Step-5 interface "is not one Lean hole away"
because the fields force `φ_G` to have *analytic* singularities, and read that
as a dependency on target 5 (`KahlerCurrentRegularization`).

The reading of the mathematics is right and the operational conclusion is wrong.
Copy-4's `eq:def-R` does not manufacture `Φ_R` from the restricted volume; it
quotes Boucksom's Theorem 3.17 for a Kähler current with analytic singularities
in a big class.  That statement **already exists on the main route** as
`NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`, and is
already consumed by `PrincipalizationData.exists_kahlerCurrentPotential_eq_bot_on_subset_nonKahlerLocus`.
Its output is literally `HasAnalyticSingularities`, which is the shape
`PhiR_presentation` needs.  Consuming it adds no sorry root that the main
theorem's cone does not already carry.

So this module builds the structure, sorry-free apart from the one classical
input Copy-4 itself cites at this step:

* `exists_ambientPhiRLowerSource_of_type` takes `ψ_{IV}`, `ψ_j` and `Φ_R` as
  weights with analytic singularities and the zero-locus containment
  `Z(𝔞_R) ⊆ Z(𝔞_{IV} 𝔞_j)`, and produces the structure together with its
  constant `A`.  The exponent comes from
  `UniformNullstellensatzPower.demaillyII422_exists_idealPow_le_of_zeroLocus_subset`
  (Demailly CADG II.4.22), which is a **pre-existing** named interface; no new
  one is introduced here.
* `exists_ambientPhiRLowerSource` is the same statement with `Φ_R` given in the
  exact form the Boucksom producer returns, `HasAnalyticSingularities Φ_R`.

## The coefficient bookkeeping, which is the only real content

`AmbientPhiRLowerSource` insists that `ψ_{IV}`, `ψ_j` and the auxiliary `ψ_R`
all carry **one common** coefficient `c`, while `Φ_R` carries `c_R · c`.  The
Boucksom current arrives with whatever coefficient its own presentation has, say
`c_Φ`, and there is no reason for `c_Φ` to be `c` or a multiple of it.  The two
are reconciled by rescaling, not by assuming:

* `c_R := c_Φ / c`, so `c_R · c = c_Φ` and `PhiR_presentation` is exactly the
  hypothesis, with no scaling of `Φ_R` itself;
* `ψ_R := (c / c_Φ) · Φ_R`, which `hasAnalyticSingularitiesOfType_smul` gives at
  coefficient `(c / c_Φ) · c_Φ = c` **on the same ideal** `𝔞_R`.

Both cancellations need the coefficients to be nonzero, which is part of
`HasAnalyticSingularitiesOfType`.  Note that `ψ_R` is an auxiliary of the
structure only: `AmbientPhiRLowerSource.moreSingularOn` uses it to route the
power containment to `eq:PhiR-lower` and it appears in no conclusion.

`A` is an output here, not an input.  Copy-4 fixes `A` in `sec:fixed-data` after
the exponent is chosen, and `A_def : A = c_R · N` is what records that; a
statement quantifying `A` universally would be stronger than the source.
-/

open Set

namespace Hironaka.AmbientPhiRSourceOfAnalyticSingularities

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightPowers
open Hironaka.UniformNullstellensatzPower
open Hironaka.PrincipalizationCopy4StepFiveCoreReduction
open Hironaka.IdealComparisonResidual

universe u

noncomputable section

variable {n : ℕ} {base : Type u} [TopologicalSpace base]
  [ChartedSpace (ComplexModel n) base] [IsComplexManifold n base] [CompactSpace base]

/-- **Copy-4 `sec:fixed-data`, the `Φ_R` half.**  Weights `ψ_{IV}`, `ψ_j` at a
common coefficient `c`, a weight `Φ_R` with analytic singularities of type
`(c_Φ, 𝔞_R)`, and the containment `Z(𝔞_R) ⊆ Z(𝔞_{IV} 𝔞_j)` produce the ambient
`Φ_R` source, with its constant `A`.

The containment is Copy-4's own setup condition: `Φ_R` is the Kähler current of
`eq:def-R`, whose polar set is `E_nK(α)`, and the fixed data of `sec:fixed-data`
is chosen so that `ψ_{IV} + ψ_j` is singular along at least that set. -/
theorem exists_ambientPhiRLowerSource_of_type
    {c cPhi : ℚ} {psiIV psij PhiR : base → EReal}
    {idealIV idealj idealR : GermIdeal n base}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij c idealj)
    (hPhi : HasAnalyticSingularitiesOfType (n := n) PhiR cPhi idealR)
    (hz : idealR.zeroLocus ⊆ (idealIV.mul idealj).zeroLocus) :
    ∃ A : ℝ, 0 < A ∧ Nonempty (AmbientPhiRLowerSource n base A PhiR psiIV psij) := by
  have hc : 0 < c := hIV.1
  have hcPhi : 0 < cPhi := hPhi.1
  have hIVcoh : idealIV.IsCoherent := hIV.2.1
  have hjcoh : idealj.IsCoherent := hj.2.1
  have hRcoh : idealR.IsCoherent := hPhi.2.1
  -- The uniform exponent, from the classical input Copy-4 cites at this step.
  obtain ⟨N, hNpos, hNle⟩ :=
    demaillyII422_exists_idealPow_le_of_zeroLocus_subset
      (isCoherent_mul hIVcoh hjcoh) hRcoh hz
  have hcne : (c : ℚ) ≠ 0 := ne_of_gt hc
  have hcPhine : (cPhi : ℚ) ≠ 0 := ne_of_gt hcPhi
  -- `c_R := c_Φ / c`, so that `c_R * c = c_Φ` with `Φ_R` itself unscaled.
  have hcR_pos : 0 < cPhi / c := div_pos hcPhi hc
  have hcancel : cPhi / c * c = cPhi := div_mul_cancel₀ _ hcne
  -- `ψ_R := (c / c_Φ) • Φ_R` has coefficient `c` on the SAME ideal `𝔞_R`.
  have hscale : (0 : ℚ) < c / cPhi := div_pos hc hcPhi
  have hR_presentation :
      HasAnalyticSingularitiesOfType (n := n)
        (fun y => ((((c / cPhi : ℚ)) : ℝ) : EReal) * PhiR y) c idealR := by
    have h := hasAnalyticSingularitiesOfType_smul (n := n) hscale hPhi
    rwa [div_mul_cancel₀ _ hcPhine] at h
  refine ⟨(cPhi / c : ℚ) * (N : ℝ), ?_, ⟨?_⟩⟩
  · have : (0 : ℝ) < ((cPhi / c : ℚ) : ℝ) := by exact_mod_cast hcR_pos
    exact mul_pos this (by exact_mod_cast hNpos)
  · exact
      { c := c
        cR := cPhi / c
        cR_pos := hcR_pos
        idealIV := idealIV
        idealj := idealj
        idealR := idealR
        psiR := fun y => ((((c / cPhi : ℚ)) : ℝ) : EReal) * PhiR y
        IV_presentation := hIV
        j_presentation := hj
        R_presentation := hR_presentation
        PhiR_presentation := by rwa [hcancel]
        power := N
        power_pos := hNpos
        power_containment := hNle
        A_def := by push_cast; ring }

/-- **The same, packaged for the on-route Boucksom producer.**
`NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus` delivers
`HasAnalyticSingularities T.potential`, i.e. *some* presentation `(c_Φ, 𝔞_R)`;
what Copy-4 then needs of that presentation is the containment of zero loci.  So
the hypothesis is stated as "there is a presentation whose zero locus is
contained", not as `HasAnalyticSingularities` plus a separate condition on
*every* presentation: the latter is strictly stronger and a consumer holding one
presentation could not discharge it.

This is the form in which the ambient `Φ_R` data of Copy-4 Step 5 is reachable
from the main route.  It appeals to `KahlerCurrentRegularization` only through
that producer, which the route already consumes at
`PrincipalizationData.exists_kahlerCurrentPotential_eq_bot_on_subset_nonKahlerLocus`;
it therefore adds no sorry root the main theorem's cone does not already carry.
It does **not** make the eventual sorry-freeness of Step 5 independent of that
target. -/
theorem exists_ambientPhiRLowerSource
    {c : ℚ} {psiIV psij PhiR : base → EReal} {idealIV idealj : GermIdeal n base}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij c idealj)
    (hPhi : ∃ (cPhi : ℚ) (idealR : GermIdeal n base),
      HasAnalyticSingularitiesOfType (n := n) PhiR cPhi idealR ∧
        idealR.zeroLocus ⊆ (idealIV.mul idealj).zeroLocus) :
    ∃ A : ℝ, 0 < A ∧ Nonempty (AmbientPhiRLowerSource n base A PhiR psiIV psij) := by
  obtain ⟨cPhi, idealR, hPhiType, hz⟩ := hPhi
  exact exists_ambientPhiRLowerSource_of_type hIV hj hPhiType hz

/-- **`eq:PhiR-lower` itself**, as the consumer sees it: the containment of zero
loci is exactly what makes `Φ_R` more singular than `A (ψ_{IV} + ψ_j)`. -/
theorem moreSingularOn_of_zeroLocus_subset
    {c cPhi : ℚ} {psiIV psij PhiR : base → EReal}
    {idealIV idealj idealR : GermIdeal n base}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij c idealj)
    (hPhi : HasAnalyticSingularitiesOfType (n := n) PhiR cPhi idealR)
    (hz : idealR.zeroLocus ⊆ (idealIV.mul idealj).zeroLocus) :
    ∃ A : ℝ, 0 < A ∧
      MoreSingularOn (fun y => (A : EReal) * (psiIV y + psij y)) PhiR univ := by
  obtain ⟨A, hApos, ⟨d⟩⟩ := exists_ambientPhiRLowerSource_of_type hIV hj hPhi hz
  exact ⟨A, hApos, d.moreSingularOn⟩

end

end Hironaka.AmbientPhiRSourceOfAnalyticSingularities
