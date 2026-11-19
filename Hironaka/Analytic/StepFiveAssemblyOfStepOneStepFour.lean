import Hironaka.Analytic.PrincipalizationCopy4StepFiveCoreReduction
import Hironaka.Analytic.StepFiveCorrectionTerm
import Hironaka.Analytic.StepSixLocalGeometry
import Hironaka.Analytic.StepFiveDivisorWeights
import Hironaka.Analytic.AmbientStepFiveResidualWeights

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 5 assembled: the proved half, with Step 1 and Step 4 as hypotheses

Source: Copy-4, `prop:principalization`, Steps 3--6, with `sec:fixed-data`,
`eq:constants` and `sec:ambient`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1497-1545,
1600-1760, 1845-1984`).

## What this module does

`PrincipalizationPolarBranchStepFive.ct22Copy4_exists_polarBranch_copy4StepFiveExceptionalWeightData`
(the main-cone root) asks for a polar branch `φ_G` and an inhabitant of
`Copy4StepFiveExceptionalWeightData`.  Every field of that structure now has a
producer (`I-0619`, `I-0621`), except the ones Copy-4 obtains from Step 1
(`sec:positive-current`, which waits on QEA) and Step 4.  This module puts the
producers together **once, on one coherent choice of data**:

`exists_polarBranch_stepFiveData_of_stepOne_stepFour` constructs `φ_G` and the
structure from

* the fixed data of `sec:fixed-data` — `Φ_R` with `R ≥ δ_R ω`, `ψ_{𝓘_V}`, `ψ_𝔧`
  and the source datum of `eq:PhiR-lower` with its constant `A_R`;
* the output of `lem:regularization` at the level `M`: `U_M` with
  `T_M ≥ -(c₀/M) ω` and `U_M ≥ (1/M) ψ_{𝔅_M} + O(1)` (`eq:def-TM`);
* the ideal function `Ψ_m` of `eq:def-Psi` for `𝔧 𝔅_m`, with `ddᶜΨ_m ≥ -c_Ψ ω`;
* the constants of `eq:constants` and of the choice of `M` and `τ`:
  `L δ_R > c₀`, `C - 1 ≥ L A_R`, `L < M`, `((C-1)/M) c_Ψ ≤ δ`,
  `0 < τ ≤ (L δ_R - c₀)/M`;
* the exceptional metric `E_rel` of Step 3 (`lem:exceptional-metric`);
* **Step 1, as hypotheses**: metered divisors `G̃_M, H^fix_m, P^mov, P^F` on `Y`
  with `ψ_{G̃_M}` presenting `𝔅_M 𝒪_Y`, `ψ_{H^fix} + ψ_{P^mov} + ψ_{P^F}` presenting
  an ideal `𝔥` with `𝓘_V 𝒪_Y = 𝔥 · 𝓘_W` (`eq:IV-H`), and
  `ψ_{𝔅_m} ∘ π ≤ ψ_{H^fix} + O(1)` (`eq:def-Gm-tilde`);
* the point `y ∈ W` off the supports and the exceptional locus, over which `Ψ_m` is
  smooth (Copy-4's choice of `y` at the end of Step 6);
* **Step 4, as a hypothesis**: `PositiveOnOneFlattening W k (β + ddᶜf̃)` for
  `β = θ_Y - Θ_D - δ π^*ω`, `D` the divisor of `eq:def-DLY` built from the data
  above (`copy4Divisor`).  `StepFourKahlerClassOnW` produces it from
  `lem:residual-nef` on `W`.

The statement of the interface is **not** changed and the interface is **not**
discharged: Step 1 and Step 4 remain hypotheses here, and the interface
quantifies `π` universally (`I-0608`).

## Evidence

`exists_polarBranch_stepFiveData_of_stepOne_stepFour` is sorry-free
(`#print axioms`: `propext, Classical.choice, Quot.sound`).
`exists_regularizationConstant_forall` was sorry-backed through exactly one
declaration, `lem:regularization`
(`QuantitativeRegularization.demailly1992_exists_regularization_multiplierIdeal_lowerBound`);
that lemma is proved since 2980657b
(`QuantitativeRegularizationFixedCover.exists_regularization_multiplierIdeal_lowerBound`), so
it is sorry-free as well (`#print axioms`: `propext, Classical.choice, Quot.sound`).

## The order of the constants

`lem:regularization`'s constant `c₀` and the Nullstellensatz constant `A_R` come
*before* `L` and `C` (`eq:constants`), and `c_Ψ` before `M`.  The producers return
them existentially, so a theorem that called them after fixing `L` could not
satisfy the inequalities (`I-0619`, coupling note).  Here `c₀`, `U_M`, `A_R`, `Ψ`
and `c_Ψ` are inputs, and the inequalities are hypotheses about them.
`exists_regularizationConstant_forall` shows that the order can be met: it
obtains `c₀` from `AmbientUMWeightLowerBound.exists_regularization_moreSingularOn_multiplierIdealWeight`
FIRST and then quantifies over everything chosen afterwards.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFiveAssemblyOfStepOneStepFour

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction StepFiveCorrectionTerm StepSixLocalGeometry
  PolarBranchStepThree MeteredDivisorOperations MeteredDivisorScaling
  AmbientIdealSourcesOfCoherentIdeals AmbientStepFiveResidualWeights
  ManifoldTubePositivity TubePositivityOneFlattening IdealWeightComparison
  ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-! ### The divisor of `eq:def-DLY` -/

theorem one_div_nonneg_of_pos {levQ : ℚ} (hlev : 0 < levQ) : (0 : ℚ) ≤ 1 / levQ :=
  div_nonneg zero_le_one hlev.le

theorem sub_one_div_nonneg {levQ CQ : ℚ} (hlev : 0 < levQ) (hC : 1 ≤ CQ) :
    (0 : ℚ) ≤ (CQ - 1) / levQ :=
  div_nonneg (sub_nonneg.mpr hC) hlev.le

theorem div_nonneg_of_one_le {levQ CQ : ℚ} (hlev : 0 < levQ) (hC : 1 ≤ CQ) :
    (0 : ℚ) ≤ CQ / levQ :=
  div_nonneg (zero_le_one.trans hC) hlev.le

/-- **Copy-4 `eq:def-DLY`**: `D = (1/M) G̃_M + ((C-1)/M) P^mov + (C/M) P^F + τ E_rel`,
as a metered effective `ℚ`-divisor. -/
def copy4Divisor {levQ CQ τQ : ℚ} (hlev : 0 < levQ) (hC : 1 ≤ CQ) (hτ : 0 ≤ τQ)
    (EGM EPmov EPF E : MeteredEffectiveQDivisor n Y) : MeteredEffectiveQDivisor n Y :=
  qcomb4 n Y (one_div_nonneg_of_pos hlev) (sub_one_div_nonneg hlev hC)
    (div_nonneg_of_one_le hlev hC) hτ EGM EPmov EPF E

/-- A nonnegative multiple has no more support than the divisor. -/
theorem smul_support_subset {c : ℚ} (hc : 0 ≤ c) (E : MeteredEffectiveQDivisor n Y) :
    (smul hc E).support ⊆ E.support := by
  intro y hy
  have hy' : ((c : ℝ) : EReal) * E.weight y = ⊥ := hy
  have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  rcases (EReal.mul_eq_bot _ _).mp hy' with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact absurd h (EReal.coe_ne_bot _)
  · exact h
  · exact absurd h (EReal.coe_ne_top _)
  · exact absurd h (not_lt.mpr (EReal.coe_nonneg.mpr hcR))

/-- The support of `D` lies in the union of the four supports. -/
theorem copy4Divisor_support_subset {levQ CQ τQ : ℚ} (hlev : 0 < levQ) (hC : 1 ≤ CQ)
    (hτ : 0 ≤ τQ) (EGM EPmov EPF E : MeteredEffectiveQDivisor n Y) :
    (copy4Divisor hlev hC hτ EGM EPmov EPF E).support ⊆
      EGM.support ∪ EPmov.support ∪ EPF.support ∪ E.support := by
  intro y hy
  rcases add_support_subset _ _ hy with h | h
  · rcases add_support_subset _ _ h with h | h
    · rcases add_support_subset _ _ h with h | h
      · exact Or.inl (Or.inl (Or.inl (smul_support_subset _ _ h)))
      · exact Or.inl (Or.inl (Or.inr (smul_support_subset _ _ h)))
    · exact Or.inl (Or.inr (smul_support_subset _ _ h))
  · exact Or.inr (smul_support_subset _ _ h)

/-- A function smooth near a point is finite there. -/
theorem ne_bot_of_isSmoothNear {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {u : M → EReal} {p : M}
    (hu : IsSmoothNear (n := n) u p) : u p ≠ ⊥ := by
  obtain ⟨U, -, hpU, h, -, heq⟩ := hu
  rw [heq p hpU]
  exact EReal.coe_ne_bot _

/-! ### The assembly -/

/-- **Copy-4 Steps 3--6 assembled on one coherent choice of data, with Step 1 and
Step 4 as explicit hypotheses.**  See the module docstring for the list of
inputs; every field of `Copy4StepFiveExceptionalWeightData` is produced by an
existing theorem:

* `φ_G` and its Kähler-current property: `PolarBranchStepThree.isKahlerCurrentPotential_polarBranch`;
* `U, σ, dominates_beta`: `StepSixLocalGeometry.exists_localGeometry_of_positiveOnOneFlattening`;
* `ρ, χ, positive_correction, smooth_rho_at_y, correction_weight`: `StepFiveCorrectionTerm`;
* `divisor_split, divisor_weight, H_weight`: exact weight identities of `qcomb4`;
* the bounds: `MeteredDivisorScaling.exists_forall_weight_le`, `AmbientStepFiveResidualWeights.exists_bound_comp`;
* the ambient block: `AmbientIdealSourcesOfCoherentIdeals` and
  `AmbientStepFiveResidualWeights.exists_residualIdealWeight`. -/
theorem exists_polarBranch_stepFiveData_of_stepOne_stepFour
    [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    {W : Set Y} {k : ℕ} (hW : IsClosedConnectedSubmanifold n W k)
    -- Step 3: the exceptional metric
    (E : MeteredEffectiveQDivisor n Y) (hEexc : E.support ⊆ exceptionalLocus n π)
    (hEkahler :
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler)
    -- `sec:fixed-data`: `R = θ + ddᶜΦ_R ≥ δ_R ω` and `eq:PhiR-lower`
    {PhiR : X → EReal} {δR : ℝ}
    (hPhiR : IsThetaPshPotential (θ - δR • omega.form).val PhiR)
    {psiIV psij : X → EReal} {idealIV 𝔧 : GermIdeal n X}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV 1 idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij 1 𝔧)
    {A : ℝ} (hA : 0 ≤ A) (hPhiRsrc : AmbientPhiRLowerSource n X A PhiR psiIV psij)
    -- `eq:def-TM`: `lem:regularization` at the level `M`
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {levQ : ℚ} {UM psiBM : X → EReal} {𝔅M : GermIdeal n X}
    (hpsiBM : HasAnalyticSingularitiesOfType (n := n) psiBM 1 𝔅M)
    (hUM : IsThetaPshPotential (θ + (c₀ / (levQ : ℝ)) • omega.form).val UM)
    (hUMlower : MoreSingularOn (fun x => ((1 / (levQ : ℝ) : ℝ) : EReal) * psiBM x) UM univ)
    -- `eq:def-Psi`: the ideal function of `𝔧 𝔅_m`
    {Ψ psib : X → EReal} {𝔟 : GermIdeal n X} {cΨ δ : ℝ}
    (hΨpsh : ThetaPlurisubharmonic (cΨ • omega.form).val Ψ)
    (hΨtype : HasAnalyticSingularitiesOfType (n := n) Ψ 1 (𝔧.mul 𝔟))
    (hb : HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟)
    -- the constants
    (hlev : 0 < levQ) {L : ℝ} {CQ τQ : ℚ} (hL : 0 < L) (hLlev : L < (levQ : ℝ))
    (hconst : c₀ < L * δR)
    (hC : 1 < CQ) (hCA : L * A ≤ (CQ : ℝ) - 1)
    (hκδ : ((CQ : ℝ) - 1) / (levQ : ℝ) * cΨ ≤ δ)
    (hτ : 0 < τQ) (hτε : (τQ : ℝ) ≤ (L * δR - c₀) / (levQ : ℝ))
    -- Step 1, as weights
    (EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y)
    (hGM : HasAnalyticSingularitiesOfType (n := n) EGM.weight 1
      (GermIdeal.pullback (m := n) π 𝔅M))
    {idealH : GermIdeal n Y}
    (hH : HasAnalyticSingularitiesOfType (n := n)
      (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1 idealH)
    (hfact : GermIdeal.pullback (m := n) π idealIV = idealH.mul (vanishingIdeal (n := n) W))
    (hHfix : MoreSingularOn (fun y => psib (π y)) EHfix.weight univ)
    -- the point `y`
    {y : Y} (hyW : y ∈ W) (hyGM : y ∉ EGM.support) (hyPmov : y ∉ EPmov.support)
    (hyPF : y ∉ EPF.support) (hyexc : y ∉ exceptionalLocus n π)
    (hΨy : IsSmoothNear (n := n) Ψ (π y))
    -- Step 4
    {f : Y → ℝ} (hf : ChartSmooth (n := n) f)
    (hstep4 : PositiveOnOneFlattening W k
      ((ClosedRealOneOneForm.pullback hπ.contMDiff θ
        - (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).curvature
        - δ • ClosedRealOneOneForm.pullback hπ.contMDiff omega.form) + ddcClosedForm f hf)) :
    ∃ φG : Y → EReal,
      IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
      Nonempty (Copy4StepFiveExceptionalWeightData
        (ClosedRealOneOneForm.pullback hπ.contMDiff θ) W φG) := by
  have hlevR : (0 : ℝ) < (levQ : ℝ) := by exact_mod_cast hlev
  have hCR : (1 : ℝ) < (CQ : ℝ) := by exact_mod_cast hC
  have hκ : (0 : ℝ) < ((CQ : ℝ) - 1) / (levQ : ℝ) := div_pos (by linarith) hlevR
  have hτR : (0 : ℝ) < (τQ : ℝ) := by exact_mod_cast hτ
  -- Step 3: the polar branch
  have hφG := isKahlerCurrentPotential_polarBranch omega hc₀ hL hLlev hconst hUM hPhiR hπ E
    hEexc hEkahler hτR hτε
  -- Step 6, from Step 4's positivity
  obtain ⟨U, σ, hU, hWU, hσ, hdom⟩ :=
    exists_localGeometry_of_positiveOnOneFlattening
      ⟨ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature, hEkahler⟩
      hW.1 hW.2.2 _ hf hstep4
  -- the point `y` is off `Supp D`
  have hyE : y ∉ E.support := fun h => hyexc (hEexc h)
  have hyD : y ∉ (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).support := by
    intro h
    rcases copy4Divisor_support_subset hlev hC.le hτ.le EGM EPmov EPF E h with
      ((h | h) | h) | h
    exacts [hyGM h, hyPmov h, hyPF h, hyE h]
  -- Step 5: the correction term
  have hρsmooth := isSmoothNear_correction hπ.contMDiff
    (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E) (((CQ : ℝ) - 1) / (levQ : ℝ)) hyD hΨy
  have hne : (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).weight y
      + ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) * Ψ (π y) ≠ ⊥ :=
    ne_bot_of_isSmoothNear (M := Y) hρsmooth
  have hρpot := isThetaPshPotentialOn_correction omega hπ.contMDiff
    (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
    (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E) hΨpsh hκ hκδ hne U
  -- bounds
  obtain ⟨KGM, hKGM⟩ := exists_forall_weight_le EGM
  obtain ⟨KHfix, hKHfix⟩ := exists_forall_weight_le EHfix
  obtain ⟨KPmov, hKPmov⟩ := exists_forall_weight_le EPmov
  obtain ⟨KPF, hKPF⟩ := exists_forall_weight_le EPF
  obtain ⟨KJ, hKJ⟩ := exists_bound_comp (Y := Y) hj π
  -- the residual ideal weight of the strict transform
  obtain ⟨psiIW, hIW, hIWzero⟩ := exists_residualIdealWeight (Y := Y)
    ⟨hW.1, fun x hx => ⟨k, hW.2.2 x hx⟩⟩ (one_pos : (0 : ℚ) < 1)
  have e₁ : (((1 / levQ : ℚ) : ℝ) : EReal) = ((1 / (levQ : ℝ) : ℝ) : EReal) := by
    push_cast; rfl
  have e₂ : ((((CQ - 1) / levQ : ℚ) : ℝ) : EReal)
      = ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) := by
    push_cast; rfl
  have e₃ : (((CQ / levQ : ℚ) : ℝ) : EReal) = (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) := by
    push_cast; rfl
  refine ⟨fun y => convexComb (1 - L / (levQ : ℝ)) UM PhiR (π y)
      + ((τQ : ℝ) : EReal) * E.weight y, hφG, ⟨?_⟩⟩
  exact
    { y := y
      U := U
      beta := ClosedRealOneOneForm.pullback hπ.contMDiff θ
        - (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).curvature
        - δ • ClosedRealOneOneForm.pullback hπ.contMDiff omega.form
      sigma := σ
      rho := fun x => (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).weight x
        + ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) * Ψ (π x)
      smooth_sigma := hσ
      dominates_beta := hdom
      positive_correction := hρpot
      smooth_rho_at_y := hρsmooth
      point_mem := hyW
      open_neighbourhood := hU
      transform_subset := hWU
      psiDres := fun x => (((1 / levQ : ℚ) : ℝ) : EReal) * EGM.weight x
        + ((((CQ - 1) / levQ : ℚ) : ℝ) : EReal) * EPmov.weight x
        + (((CQ / levQ : ℚ) : ℝ) : EReal) * EPF.weight x
      psiE := E.weight
      chi := fun x => ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) * Ψ (π x)
      phiQpi := fun y => convexComb (1 - L / (levQ : ℝ)) UM PhiR (π y)
      psiD := (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).weight
      psiGM := EGM.weight
      psiHfix := EHfix.weight
      psiPmov := EPmov.weight
      psiPF := EPF.weight
      psiJ := fun y => psij (π y)
      psiH := fun y => EHfix.weight y + EPmov.weight y + EPF.weight y
      tau := (τQ : ℝ)
      lev := (levQ : ℝ)
      L := L
      C := (CQ : ℝ)
      A := A
      KGM := KGM
      KHfix := KHfix
      KPmov := KPmov
      KPF := KPF
      KJ := KJ
      correction_eq := rfl
      divisor_split := fun _ => rfl
      polar_split := fun _ => rfl
      hL := hL
      hLlev := hLlev
      hA := hA
      hCA := hCA
      bound_GM := hKGM
      bound_Hfix := hKHfix
      bound_Pmov := hKPmov
      bound_PF := hKPF
      bound_J := hKJ
      divisor_weight := MoreSingularOn.of_le fun x _ => le_of_eq (by rw [e₁, e₂, e₃])
      correction_weight := moreSingularOn_correction_weight hκ.le hΨtype hj hb hHfix
      H_weight := MoreSingularOn.of_le fun _ _ => le_rfl
      base := X
      pi := π
      psiBM := psiBM
      psiIV := psiIV
      psij := psij
      UM := UM
      PhiR := PhiR
      ambientUM_lower := hUMlower
      ambientPhiR_source := hPhiRsrc
      phiQpi_def := fun _ => rfl
      psiJ_def := fun _ => rfl
      ambientGM_source := ambientGMLowerSource_of_presentation hπ.contMDiff hpsiBM hGM
      psiIW := psiIW
      psiIW_coefficient := 1
      psiIW_ideal := vanishingIdeal (n := n) W
      psiIW_presentation := hIW
      psiIW_zeroLocus := hIWzero
      ambientIV_source := ambientIVLowerSource_of_presentations hπ.contMDiff hIV hH hIW hfact }

/-! ### The order of the constants can be met -/

/-- **`c₀` first.**  `lem:regularization`'s constant depends only on `(X, ω)`, so
it can be fixed before everything else; for every later choice of the data and
of the constants satisfying `eq:constants` with respect to it, `U_M` is produced
by `lem:regularization` at the chosen level `M` (with `𝔅_M = 𝓘(M φ)`) and the
assembly above applies.  This is the coupled order of `I-0619`: `c₀` is obtained
from `AmbientUMWeightLowerBound.exists_regularization_moreSingularOn_multiplierIdealWeight`
ONCE, before `L`, `C`, `M`, `π` and the Step-1 divisors are quantified.

The remaining existential inputs (`A_R` with its source datum, `Ψ_m` with `c_Ψ`,
`E_rel`) stay universally quantified data: each has its own producer
(`AmbientPhiRSourceOfAnalyticSingularities.exists_ambientPhiRLowerSource`,
`IdealFunctionMaxGluing.exists_idealFunction`, `ExceptionalMetric.exists_exceptionalMetric`),
and a caller obtains it at the point of Copy-4's order where it is chosen. -/
theorem exists_regularizationConstant_forall [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (θ : ClosedRealOneOneForm n X) (phi : X → EReal),
        IsThetaPshPotential θ.val phi →
      ∀ (Mlev : ℕ) (hM : 1 ≤ Mlev),
      ∀ (psiBM : X → EReal), HasAnalyticSingularitiesOfType (n := n) psiBM 1
        (multiplierIdeal (n := n) (Mlev : ℝ) phi) →
      ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
        [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y]
        (π : Y → X) (hπ : IsBlowupSequence n X Y π) (W : Set Y) (k : ℕ),
        IsClosedConnectedSubmanifold n W k →
      ∀ (E : MeteredEffectiveQDivisor n Y), E.support ⊆ exceptionalLocus n π →
        (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler →
      ∀ (PhiR : X → EReal) (δR : ℝ), IsThetaPshPotential (θ - δR • omega.form).val PhiR →
      ∀ (psiIV psij : X → EReal) (idealIV 𝔧 : GermIdeal n X),
        HasAnalyticSingularitiesOfType (n := n) psiIV 1 idealIV →
        HasAnalyticSingularitiesOfType (n := n) psij 1 𝔧 →
      ∀ (A : ℝ), 0 ≤ A → AmbientPhiRLowerSource n X A PhiR psiIV psij →
      ∀ (Ψ psib : X → EReal) (𝔟 : GermIdeal n X) (cΨ δ : ℝ),
        ThetaPlurisubharmonic (cΨ • omega.form).val Ψ →
        HasAnalyticSingularitiesOfType (n := n) Ψ 1 (𝔧.mul 𝔟) →
        HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟 →
      ∀ (L : ℝ) (CQ τQ : ℚ), 0 < L → L < ((Mlev : ℚ) : ℝ) → c₀ < L * δR →
      ∀ (hC : 1 < CQ), L * A ≤ (CQ : ℝ) - 1 →
        ((CQ : ℝ) - 1) / ((Mlev : ℚ) : ℝ) * cΨ ≤ δ →
      ∀ (hτ : 0 < τQ), (τQ : ℝ) ≤ (L * δR - c₀) / ((Mlev : ℚ) : ℝ) →
      ∀ (EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y),
        HasAnalyticSingularitiesOfType (n := n) EGM.weight 1
          (GermIdeal.pullback (m := n) π (multiplierIdeal (n := n) (Mlev : ℝ) phi)) →
      ∀ (idealH : GermIdeal n Y),
        HasAnalyticSingularitiesOfType (n := n)
          (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1 idealH →
        GermIdeal.pullback (m := n) π idealIV = idealH.mul (vanishingIdeal (n := n) W) →
        MoreSingularOn (fun y => psib (π y)) EHfix.weight univ →
      ∀ (y : Y), y ∈ W → y ∉ EGM.support → y ∉ EPmov.support → y ∉ EPF.support →
        y ∉ exceptionalLocus n π → IsSmoothNear (n := n) Ψ (π y) →
      ∀ (f : Y → ℝ) (hf : ChartSmooth (n := n) f),
        PositiveOnOneFlattening W k
          ((ClosedRealOneOneForm.pullback hπ.contMDiff θ
            - (copy4Divisor (Nat.cast_pos.mpr hM : (0 : ℚ) < Mlev)
                hC.le hτ.le EGM EPmov EPF E).curvature
            - δ • ClosedRealOneOneForm.pullback hπ.contMDiff omega.form)
            + ddcClosedForm f hf) →
      ∃ φG : Y → EReal,
        IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
        Nonempty (Copy4StepFiveExceptionalWeightData
          (ClosedRealOneOneForm.pullback hπ.contMDiff θ) W φG) := by
  obtain ⟨c₀, hc₀, hreg⟩ :=
    AmbientUMWeightLowerBound.exists_regularization_moreSingularOn_multiplierIdealWeight
      (d := n) (Z := X) omega
  refine ⟨c₀, hc₀, ?_⟩
  intro θ phi hphi Mlev hM psiBM hpsiBM Y _ _ _ _ _ π hπ W k hW E hEexc hEkahler PhiR δR
    hPhiR psiIV psij idealIV 𝔧 hIV hj A hA hPhiRsrc Ψ psib 𝔟 cΨ δ hΨpsh hΨtype hb
    L CQ τQ hL hLlev hconst hC hCA hκδ hτ hτε EGM EHfix EPmov EPF hGM idealH hH hfact hHfix
    y hyW hyGM hyPmov hyPF hyexc hΨy f hf hstep4
  obtain ⟨UM, hUM, hUMlower⟩ := hreg θ phi hphi Mlev hM psiBM hpsiBM
  have hcast : ((Mlev : ℚ) : ℝ) = (Mlev : ℝ) := Rat.cast_natCast Mlev
  have hUM' : IsThetaPshPotential (θ + (c₀ / ((Mlev : ℚ) : ℝ)) • omega.form).val UM := by
    rw [hcast]; exact hUM
  have hUMlower' : MoreSingularOn
      (fun x => ((1 / ((Mlev : ℚ) : ℝ) : ℝ) : EReal) * psiBM x) UM univ := by
    rw [hcast, one_div]; exact hUMlower
  exact exists_polarBranch_stepFiveData_of_stepOne_stepFour omega θ hπ hW E hEexc hEkahler
    hPhiR hIV hj hA hPhiRsrc hc₀.le hpsiBM hUM' hUMlower' hΨpsh hΨtype hb _ hL hLlev hconst
    hC hCA hκδ hτ hτε EGM EHfix EPmov EPF hGM hH hfact hHfix hyW hyGM hyPmov hyPF hyexc hΨy
    hf hstep4

end

end Hironaka.StepFiveAssemblyOfStepOneStepFour
