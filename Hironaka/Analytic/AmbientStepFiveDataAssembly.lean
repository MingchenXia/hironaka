import Hironaka.Analytic.AmbientIdealSourcesOfCoherentIdeals
import Hironaka.Analytic.AmbientUMWeightLowerBound
import Hironaka.Analytic.AmbientPhiRSourceOfAnalyticSingularities

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Four of the eight ambient obligations of Copy-4 Step 5, assembled

Source: Copy-4, `sec:fixed-data` and `sec:ambient`
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1490-1527`,
`:1719-1750`), used in Step 5 of `prop:principalization` (`:1845-1984`);
blueprint `ana:principalization-data`.

## What this module does, and what it does not

`Copy4StepFiveExceptionalWeightData`
(`PrincipalizationCopy4StepFiveCoreReduction.lean:232`) carries **eight**
obligations in its ambient block (`:289-314`), not four:

| field | line | producer |
|---|---|---|
| `ambientUM_lower` | 300 | `Hironaka.AmbientUMWeightLowerBound` |
| `ambientPhiR_source` | 302 | `Hironaka.AmbientPhiRSourceOfAnalyticSingularities` |
| `phiQpi_def` | 304 | **none** |
| `psiJ_def` | 306 | **none** |
| `ambientGM_source` | 307 | `Hironaka.AmbientIdealSourcesOfCoherentIdeals` |
| `psiIW_presentation` | 311 | **none** |
| `psiIW_zeroLocus` | 313 | **none** |
| `ambientIV_source` | 314 | `Hironaka.AmbientIdealSourcesOfCoherentIdeals` |

This module assembles the **four with producers** onto one choice of data.  It
does not close the ambient block and it constructs no inhabitant of
`Copy4StepFiveExceptionalWeightData`.  The other four are open, and two of them
are substantive rather than definitional: `phiQpi` is pinned from the other
side by `polar_split` (`:269`), so `phiQpi_def` asserts that `φ_G` decomposes
through `convexComb (1 - L/lev) U_M Φ_R ∘ π`, and `ψ_𝔧` is pinned by `bound_J`
(`:278`) and `correction_weight` (`:283`).  They are tracked on roadmap
`TN.3.4.DIVISORSIDE`.

## Why the assembly is stated with the weights explicit

The four producers share their data: `ψ_{𝔅_M}` occurs in `ambientUM_lower` and
in `ambientGM_source`, `ψ_{𝓘_V}` in `ambientPhiR_source` and in
`ambientIV_source`, `ψ_𝔧` in `ambientPhiR_source` and in `psiJ_def`.  So the
primary statement, `ambientStepFiveData_of_presentations`, takes `ψ_{𝔅_M}`,
`ψ_{G̃_M}`, `ψ_H` and `ψ_{𝓘_W}` as **arguments**: a coupled construction of the
full structure has to choose those weights itself, because they are constrained
elsewhere in it (`bound_GM`, `divisor_weight`, `H_weight`,
`psiIW_presentation`, `psiIW_zeroLocus`), and a theorem that produces them
afresh cannot serve it.  `exists_ambientStepFiveData` is the corollary in which
they are produced from coherence alone.

`U_M` stays existential in both: it is not free, it is the output of
`lem:regularization` at the level `M`.

The two coefficient constraints turned out to be satisfiable **by
construction**, and this is recorded rather than dressed up as a reconciliation:
`exists_hasAnalyticSingularitiesOfType_coefficient` manufactures a weight at any
positive coefficient, so `AmbientGMLowerSource` places no constraint on the
coefficient of `ψ_{𝔅_M}`, which is free to be the `1` that
`Hironaka.AmbientUMWeightLowerBound` needs; and the shared coefficient of
`ψ_{𝓘_V}` is shared syntactically, the same presentation being passed to both
producers.  What the assembly does establish is that no *ideal* or *weight*
clash blocks the four from coexisting.

## Residue

Both theorems carried `sorryAx` through exactly two **pre-existing** named
classical interfaces, both cited by Copy-4 at these very steps and neither
introduced here; the first is proved since 2980657b
(`QuantitativeRegularizationFixedCover`), so only the second remains:

* `QuantitativeRegularizationInterface.demailly1992_exists_regularization_multiplierIdeal_lowerBound`
  (`lem:regularization`, for `eq:def-TM`), and
* `UniformNullstellensatzPower.demaillyII422_exists_idealPow_le_of_zeroLocus_subset`
  (Demailly CADG II.4.22, for `eq:PhiR-lower`).

Beyond those, **three substantive inputs are carried as hypotheses** and must be
disclosed with the residue rather than counted as discharged:

* `hBcoh` — coherence of `𝓘(M φ)` (Nadel), a hypothesis here exactly as in
  `Hironaka.IdealComparisonResidual`;
* `hPhi` — `Φ_R` with analytic singularities and the zero-locus containment
  (`eq:def-R`, quoting Boucksom 3.17); on the main route this comes from
  `NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus` (sorry-free:
  no tracked Lean file of the project contains `sorry` any more);
* `hfact` — the `eq:IV-H` ideal identity `π^* 𝓘_V = 𝔥 · 𝔟`, i.e. clause (i) of
  `lem:relative-principalization`.  Its only producer in the tree is
  `RelativePrincipalization.exists_factorizationData` (`I-0458`, `I-0484`), the Hironaka
  statement, proved in place from the canonical resolution invariant.  It enters as a hypothesis, so it does not
  appear in `#print axioms` of this module.

The divisor-side fields of `Copy4StepFiveExceptionalWeightData` — `ψ_{D,res}`,
`ψ_E`, `χ`, the five bounded divisor weights with their bounds,
`divisor_weight`, `correction_weight`, `H_weight`, the coefficient
inequalities, and the local geometry `y, U, β, σ, ρ` — are untouched.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.AmbientStepFiveDataAssembly

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities
open Hironaka.AmbientIdealSourcesOfCoherentIdeals
open Hironaka.AmbientPhiRSourceOfAnalyticSingularities
open Hironaka.AmbientUMWeightLowerBound
open Hironaka.CoherentIdealWeight
open Hironaka.PrincipalizationCopy4StepFiveCoreReduction

universe u

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **The four ambient obligations with producers, on one explicit choice of
weights.**

This is the primary form (`I-0166`): `ψ_{𝔅_M}`, `ψ_{G̃_M}`, `ψ_H` and
`ψ_{𝓘_W}` are **arguments**, because a coupled construction of
`Copy4StepFiveExceptionalWeightData` must choose them itself — they are
constrained by `bound_GM`, `divisor_weight`, `H_weight`, `psiIW_presentation`
and `psiIW_zeroLocus` elsewhere in the structure.  Only `U_M` and the
Nullstellensatz constant `A` are produced, because neither is free: `U_M` is
the output of `lem:regularization` at the level `M`, and `A` is fixed by the
exponent of `eq:PhiR-lower`.

The hypotheses on the four weights are exactly the ideal-theoretic content the
four fields need, and nothing else: coefficient `1` on `𝓘(M φ)` for
`ψ_{𝔅_M}` (Copy-4's normalization, and the only coefficient at which Demailly's
germ bound matches `eq:def-TM`), the pullback ideal for `ψ_{G̃_M}`, and the two
factors of `eq:IV-H` at the coefficient of `ψ_{𝓘_V}` for `ψ_H` and `ψ_{𝓘_W}`.

Does **not** close the ambient block: `phiQpi_def`, `psiJ_def`,
`psiIW_presentation` and `psiIW_zeroLocus` have no producer.  See the module
docstring for the three hypotheses that are part of the residue. -/
theorem ambientStepFiveData_of_presentations [CompactSpace X] [ConnectedSpace X]
    [CompactSpace Y] (omega : KahlerBackground n X)
    (theta : ClosedRealOneOneForm n X) {phi : X → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    {Mlev : ℕ} (hM : 1 ≤ Mlev)
    {psiBM : X → EReal}
    (hpsiBM : HasAnalyticSingularitiesOfType (n := n) psiBM 1
      (multiplierIdeal (n := n) (Mlev : ℝ) phi))
    {c : ℚ} {psiIV psij PhiR : X → EReal} {idealIV idealj : GermIdeal n X}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij c idealj)
    (hPhi : ∃ (cPhi : ℚ) (idealR : GermIdeal n X),
      HasAnalyticSingularitiesOfType (n := n) PhiR cPhi idealR ∧
        idealR.zeroLocus ⊆ (idealIV.mul idealj).zeroLocus)
    {pi : Y → X}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {psiGM : Y → EReal}
    (hGM : HasAnalyticSingularitiesOfType (n := n) psiGM 1
      (GermIdeal.pullback (m := n) pi (multiplierIdeal (n := n) (Mlev : ℝ) phi)))
    {idealH idealIW : GermIdeal n Y} {psiH psiIW : Y → EReal}
    (hH : HasAnalyticSingularitiesOfType (n := n) psiH c idealH)
    (hIW : HasAnalyticSingularitiesOfType (n := n) psiIW c idealIW)
    (hfact : GermIdeal.pullback (m := n) pi idealIV = idealH.mul idealIW) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∃ (UM : X → EReal) (A : ℝ),
        0 < A ∧
        IsThetaPshPotential (theta + (c₀ / (Mlev : ℝ)) • omega.form).val UM ∧
        MoreSingularOn (fun x => (((Mlev : ℝ)⁻¹ : ℝ) : EReal) * psiBM x) UM univ ∧
        Nonempty (AmbientGMLowerSource n X Y pi psiBM psiGM) ∧
        Nonempty (AmbientPhiRLowerSource n X A PhiR psiIV psij) ∧
        Nonempty (AmbientIVLowerSource n X Y pi psiIV psiH psiIW) := by
  -- `eq:def-TM`, both clauses, at the given `ψ_{𝔅_M}`.
  obtain ⟨c₀, hc₀, hreg⟩ :=
    exists_regularization_moreSingularOn_multiplierIdealWeight (d := n) (Z := X) omega
  obtain ⟨UM, hUM, hUMlower⟩ := hreg theta phi hphi Mlev hM psiBM hpsiBM
  -- `eq:PhiR-lower`, at the coefficient of `ψ_{𝓘_V}` and `ψ_𝔧`.
  obtain ⟨A, hA, hPhiR⟩ := exists_ambientPhiRLowerSource hIV hj hPhi
  exact ⟨c₀, hc₀, UM, A, hA, hUM, hUMlower,
    ⟨ambientGMLowerSource_of_presentation hpi hpsiBM hGM⟩, hPhiR,
    ⟨ambientIVLowerSource_of_presentations hpi hIV hH hIW hfact⟩⟩

/-- **The same with the four weights produced from coherence.**  A corollary of
`ambientStepFiveData_of_presentations`: `ψ_{𝔅_M}` comes from Nadel coherence of
`𝓘(M φ)`, `ψ_{G̃_M}` from coherence of the pullback, and `ψ_H`, `ψ_{𝓘_W}` from
coherence of the two `eq:IV-H` factors.

Useful as an existence statement; **not** usable by a coupled construction of
`Copy4StepFiveExceptionalWeightData`, which needs the weights of
`ambientStepFiveData_of_presentations` to be its own. -/
theorem exists_ambientStepFiveData [CompactSpace X] [ConnectedSpace X]
    [CompactSpace Y] (omega : KahlerBackground n X)
    (theta : ClosedRealOneOneForm n X) {phi : X → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    {Mlev : ℕ} (hM : 1 ≤ Mlev)
    (hBcoh : (multiplierIdeal (n := n) (Mlev : ℝ) phi).IsCoherent)
    {c : ℚ} {psiIV psij PhiR : X → EReal} {idealIV idealj : GermIdeal n X}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij c idealj)
    (hPhi : ∃ (cPhi : ℚ) (idealR : GermIdeal n X),
      HasAnalyticSingularitiesOfType (n := n) PhiR cPhi idealR ∧
        idealR.zeroLocus ⊆ (idealIV.mul idealj).zeroLocus)
    {pi : Y → X}
    (hpi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi)
    {idealH idealIW : GermIdeal n Y}
    (hHcoh : idealH.IsCoherent) (hIWcoh : idealIW.IsCoherent)
    (hfact : GermIdeal.pullback (m := n) pi idealIV = idealH.mul idealIW) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∃ (psiBM UM : X → EReal) (psiGM psiH psiIW' : Y → EReal) (A : ℝ),
        0 < A ∧
        HasAnalyticSingularitiesOfType (n := n) psiBM 1
          (multiplierIdeal (n := n) (Mlev : ℝ) phi) ∧
        IsThetaPshPotential (theta + (c₀ / (Mlev : ℝ)) • omega.form).val UM ∧
        MoreSingularOn (fun x => (((Mlev : ℝ)⁻¹ : ℝ) : EReal) * psiBM x) UM univ ∧
        Nonempty (AmbientGMLowerSource n X Y pi psiBM psiGM) ∧
        Nonempty (AmbientPhiRLowerSource n X A PhiR psiIV psij) ∧
        Nonempty (AmbientIVLowerSource n X Y pi psiIV psiH psiIW') := by
  obtain ⟨psiBM, hpsiBM⟩ := exists_hasAnalyticSingularitiesOfType_of_isCoherent hBcoh
  obtain ⟨psiGM, hGM⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient
      (GermIdealPullbackCalculus.isCoherent_pullback (m := n) hpi hBcoh) one_pos
  obtain ⟨psiH, hH⟩ := exists_hasAnalyticSingularitiesOfType_coefficient hHcoh hIV.1
  obtain ⟨psiIW, hIW⟩ := exists_hasAnalyticSingularitiesOfType_coefficient hIWcoh hIV.1
  obtain ⟨c₀, hc₀, UM, A, hA, hUM, hUMlower, hGMsrc, hPhiR, hIVsrc⟩ :=
    ambientStepFiveData_of_presentations omega theta hphi hM hpsiBM hIV hj hPhi hpi
      hGM hH hIW hfact
  exact ⟨c₀, hc₀, psiBM, UM, psiGM, psiH, psiIW, A, hA, hpsiBM, hUM, hUMlower,
    hGMsrc, hPhiR, hIVsrc⟩

end

end Hironaka.AmbientStepFiveDataAssembly
