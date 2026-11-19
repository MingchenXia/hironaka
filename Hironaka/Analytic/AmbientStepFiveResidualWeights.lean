import Hironaka.Analytic.AmbientStepFiveDataAssembly
import Hironaka.Analytic.VanishingIdealZeroLocus
import Hironaka.Analytic.ThetaPshConvexCombination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The last four ambient obligations of Copy-4 Step 5

Source: Copy-4, `prop:principalization` Step 5 and `sec:fixed-data`
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1490-1527`,
`:1719-1750`, `:1845-1984`); blueprint `ana:principalization-data`.

## What this module adds

`Hironaka.AmbientStepFiveDataAssembly` assembled **four** of the eight ambient
obligations of `Copy4StepFiveExceptionalWeightData`
(`Pending/PrincipalizationCopy4StepFiveCoreReduction.lean:232`).  The other
four — `phiQpi_def` (`:304`), `psiJ_def` (`:306`), `psiIW_presentation`
(`:311`) and `psiIW_zeroLocus` (`:313`) — had no producer.  They get one here,
and `ambientStepFiveBlock_of_presentations` runs all **eight** on one choice of
data.

## Where the substance of the last four actually sits

Run 0088 r0 recorded `phiQpi_def` and `psiJ_def` as *substantive*.  That was a
mislocation, and it is corrected here: `phiQpi` and `psiJ` are **free fields**
of the structure, so an equation that only *defines* them is discharged by
`rfl` once the right value is chosen.  What their presence does is transfer the
obligation onto the fields that pin the same functions from the other side:

* `polar_split` (`:269`) becomes `φ_G = convexComb (1 - L/ℓ) U_M Φ_R ∘ π + τ ψ_E`,
  i.e. Copy-4's *construction* of the global polar branch.  That is the real
  content, it is divisor-side (it mentions `ψ_E` and `τ`), and it is untouched
  here.
* `bound_J` (`:278`) and `correction_weight` (`:283`) become statements about
  `ψ_𝔧 ∘ π`.  `bound_J` is discharged here — a weight with analytic
  singularities on a compact manifold is bounded above
  (`IdealWeightComparison.exists_le_of_hasAnalyticSingularitiesOfType`), and
  boundedness is stable under composition with any map.  `correction_weight`
  mentions `χ` and stays divisor-side.

So the ambient block of Step 5 is closed, in the sense that every one of its
eight fields now has a producer; the statement below is the record of that, not
an inhabitant of `Copy4StepFiveExceptionalWeightData`, which needs the divisor
side as well.

`psiIW_presentation` and `psiIW_zeroLocus` are genuinely two obligations and
are discharged together, at the ideal `𝓘_{W'}` that the modification side
delivers: coherence from `VanishingIdealCoherent.isCoherent_vanishingIdeal`
gives the weight, and `VanishingIdealZeroLocus.zeroLocus_vanishingIdeal` gives
the zero locus.  Both need `W'` to be a *closed* submanifold and nothing more.

## Residue

As in `Hironaka.AmbientStepFiveDataAssembly`, `sorryAx` no longer reaches the assembly: the
named classical inputs `demaillyII422_exists_idealPow_le_of_zeroLocus_subset` (for `eq:PhiR-lower`) and
`demailly1992_exists_regularization_multiplierIdeal_lowerBound` (for `eq:def-TM`, since 2980657b)
are proved (no tracked Lean file of the project contains `sorry`).  Three substantive inputs ride
along as **hypotheses**, hence invisibly to `#print axioms`: Nadel coherence of `𝓘(Mφ)` (only via
the corollary form there), `hPhi` (`eq:def-R`, Boucksom 3.17), and `hfact`, which is clause (i) of
`lem:relative-principalization` combined with clause (ii) — its only producer is the Hironaka
statement `RelativePrincipalization.exists_factorizationData`, proved in place from the canonical resolution invariant.  The four
new declarations are sorry-free.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.AmbientStepFiveResidualWeights

open Hironaka.PositiveClasses Hironaka.BlowupSequences
  Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.AmbientIdealSourcesOfCoherentIdeals
open Hironaka.AmbientStepFiveDataAssembly
open Hironaka.IdealWeightComparison
open Hironaka.PrincipalizationCopy4StepFiveCoreReduction
open Hironaka.ThetaPshConvexCombination
open Hironaka.VanishingIdealZeroLocus

universe u

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-! ### `psiIW_presentation` and `psiIW_zeroLocus` -/

/-- **The residual ideal weight of Copy-4 Step 5, with its zero locus.**  Both
obligations at once, at the ideal `𝓘_{W'}` of the strict transform: a closed
complex submanifold has a coherent vanishing ideal, hence a weight at any
prescribed positive coefficient, and the zero locus of a vanishing ideal of a
closed set is that set.

The coefficient is prescribed because Step 5 shares it with `ψ_{𝓘_V}` and
`ψ_H`: the whole `O(1)` calculus of `Pending/IdealWeightComparison` compares
weights only at a common coefficient. -/
theorem exists_residualIdealWeight [CompactSpace Y] {W' : Set Y}
    (hW' : IsClosedSubmanifold n W') {c : ℚ} (hc : 0 < c) :
    ∃ psiIW : Y → EReal,
      HasAnalyticSingularitiesOfType (n := n) psiIW c
        (vanishingIdeal (n := n) W') ∧
      (vanishingIdeal (n := n) W').zeroLocus = W' := by
  obtain ⟨psiIW, hIW⟩ :=
    exists_hasAnalyticSingularitiesOfType_coefficient
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hW') hc
  exact ⟨psiIW, hIW, zeroLocus_vanishingIdeal hW'.1⟩

/-! ### `psiJ_def` and `bound_J` -/

/-- **`bound_J` for the pulled-back weight.**  `ψ_𝔧` is bounded above on the
compact base because it has analytic singularities, and boundedness above is
preserved by composition with an arbitrary map — no property of `π` is used.
This is the field `bound_J` for the value of `ψ_𝔧` forced by `psiJ_def`. -/
theorem exists_bound_comp [CompactSpace X] {psij : X → EReal} {c : ℚ}
    {idealj : GermIdeal n X}
    (hj : HasAnalyticSingularitiesOfType (n := n) psij c idealj)
    (pi : Y → X) :
    ∃ K : ℝ, ∀ y : Y, psij (pi y) ≤ (K : EReal) := by
  obtain ⟨K, hK⟩ := exists_le_of_hasAnalyticSingularitiesOfType hj
  exact ⟨K, fun y => hK (pi y)⟩

/-! ### All eight ambient obligations on one choice of data -/

/-- **The ambient block of Copy-4 Step 5, complete.**  Every one of the eight
ambient fields of `Copy4StepFiveExceptionalWeightData` holds for one choice of
data: the four of `AmbientStepFiveDataAssembly.ambientStepFiveData_of_presentations`
together with the residual ideal weight, its zero locus, the pulled-back `ψ_𝔧`
with its bound, and `φ_{Q,π}`.

`ψ_{𝔅_M}`, `ψ_{G̃_M}` and `ψ_H` stay **arguments** for the reason recorded in
`AmbientStepFiveDataAssembly`: a coupled construction of the full structure has
to choose them itself, because `bound_GM`, `divisor_weight` and `H_weight`
constrain them on the divisor side.  `ψ_{𝓘_W}`, `ψ_𝔧` and `φ_{Q,π}` are
produced, since the divisor side constrains them only through `polar_split` and
`correction_weight`, which are about `φ_G` and `χ`.

`L` and `ℓ` are free parameters here: the coefficient inequalities `hL`,
`hLlev`, `hCA` are divisor-side fields, and the ambient block does not
constrain them.  The bound `0 < A` is stronger than the field `hA : 0 ≤ A`.

This does **not** produce a `Copy4StepFiveExceptionalWeightData`: the divisor
side (`ψ_{D,res}`, `ψ_E`, `χ`, `ψ_D`, the four remaining bounded divisor
weights, the coefficient inequalities, `divisor_weight`, `correction_weight`,
`H_weight`, the local geometry, `correction_eq`, `divisor_split` and
`polar_split`) is untouched.  See the module docstring for the residue. -/
theorem ambientStepFiveBlock_of_presentations [CompactSpace X] [ConnectedSpace X]
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
    {psiH : Y → EReal} {idealH : GermIdeal n Y}
    (hH : HasAnalyticSingularitiesOfType (n := n) psiH c idealH)
    {W' : Set Y} (hW' : IsClosedSubmanifold n W')
    (hfact : GermIdeal.pullback (m := n) pi idealIV
      = idealH.mul (vanishingIdeal (n := n) W'))
    (L lev : ℝ) :
    ∃ (c₀ A KJ : ℝ) (UM : X → EReal) (psiIW psiJ phiQpi : Y → EReal),
      0 < c₀ ∧ 0 < A ∧
      IsThetaPshPotential (theta + (c₀ / (Mlev : ℝ)) • omega.form).val UM ∧
      MoreSingularOn (fun x => (((Mlev : ℝ)⁻¹ : ℝ) : EReal) * psiBM x) UM univ ∧
      Nonempty (AmbientGMLowerSource n X Y pi psiBM psiGM) ∧
      Nonempty (AmbientPhiRLowerSource n X A PhiR psiIV psij) ∧
      Nonempty (AmbientIVLowerSource n X Y pi psiIV psiH psiIW) ∧
      HasAnalyticSingularitiesOfType (n := n) psiIW c
        (vanishingIdeal (n := n) W') ∧
      (vanishingIdeal (n := n) W').zeroLocus = W' ∧
      (∀ y, psiJ y = psij (pi y)) ∧
      (∀ y, psiJ y ≤ (KJ : EReal)) ∧
      (∀ y, phiQpi y = convexComb (1 - L / lev) UM PhiR (pi y)) := by
  obtain ⟨psiIW, hIW, hIWzero⟩ := exists_residualIdealWeight hW' hIV.1
  obtain ⟨c₀, hc₀, UM, A, hA, hUM, hUMlower, hGMsrc, hPhiRsrc, hIVsrc⟩ :=
    ambientStepFiveData_of_presentations omega theta hphi hM hpsiBM hIV hj hPhi
      hpi hGM hH hIW hfact
  obtain ⟨KJ, hKJ⟩ := exists_bound_comp (Y := Y) hj pi
  exact ⟨c₀, A, KJ, UM, psiIW, fun y => psij (pi y),
    fun y => convexComb (1 - L / lev) UM PhiR (pi y),
    hc₀, hA, hUM, hUMlower, hGMsrc, hPhiRsrc, hIVsrc, hIW, hIWzero,
    fun _ => rfl, hKJ, fun _ => rfl⟩

end

end Hironaka.AmbientStepFiveResidualWeights
