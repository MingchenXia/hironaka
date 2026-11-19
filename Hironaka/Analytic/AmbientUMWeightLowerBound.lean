import Hironaka.Analytic.QuantitativeRegularization
import Hironaka.Analytic.IdealPresentation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `eq:def-TM`: the ambient regularization dominates the multiplier-ideal weight

Source: Copy-4, `sec:ambient`, `eq:def-TM`
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1719-1727`),
and `sec:setup` for `𝔅_q := 𝓘(q V_θ)` (`:1419`); blueprint `ana:regularization`.

## What this module is for

`Copy4StepFiveExceptionalWeightData`
(`PrincipalizationCopy4StepFiveCoreReduction.lean:232`) has a field

  `ambientUM_lower : MoreSingularOn (fun x => ((1 / lev : ℝ) : EReal) * psiBM x) UM univ`

which is the third clause of Copy-4's `eq:def-TM`,
`U_M ≥ M⁻¹ ψ_{𝔅_M} + O(1)`.  It is the one ambient field of Step 5 whose
producer is not ideal-theoretic: Copy-4 obtains it by applying
`lem:regularization` to `V_θ` at level `M`.

`Hironaka.QuantitativeRegularization.exists_regularization_multiplierIdeal_lowerBound`
is exactly that lemma, but it states its lower bound *germwise and against a
generating family*: for every point `x` and every finite family `g` of germs of
`𝓘(mφ)` at `x` there is a constant with `m⁻¹ log ∑|gᵢ|² - C ≤ φ_m` near `x`.
This module converts that shape into the single global comparison
`MoreSingularOn`, which is what the Step-5 structure and the whole `O(1)`
calculus of `Pending/IdealWeightComparison` consume.  Until now the lemma had
no consumer at all.

## The two inputs

* the germ bound above, and
* a weight `ψ_{𝔅_M}` of `𝓘(Mφ)` **at coefficient `1`** — Copy-4's normalization
  `ψ_𝔞 = log ∑|gᵢ|²`.  Once `𝓘(Mφ)` is known to be coherent (Nadel's theorem,
  a hypothesis here exactly as in `Hironaka.IdealComparisonResidual`), such a
  weight exists by
  `CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent`,
  which produces coefficient `1` and nothing else — so the normalization is not
  a restriction.

Compactness turns the germwise comparison into one global constant
(`IdealWeightComparison.moreSingularOn_univ_of_forall_moreSingularAt`).

## Honest labelling

`moreSingularAt_smul_of_generatorLog_lowerBound` and
`moreSingularOn_smul_of_generatorLog_lowerBound` are **sorry-free**: they take
the germ bound as a hypothesis.
`exists_regularization_moreSingularOn_multiplierIdealWeight`, which discharges
that hypothesis from `lem:regularization`, is sorry-free too since
`QuantitativeRegularizationInterface.demailly1992_exists_regularization_multiplierIdeal_lowerBound`
was proved (2980657b).  No new interface is introduced and no existing statement is changed.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.AmbientUMWeightLowerBound

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison
open Hironaka.QuantitativeRegularization

noncomputable section

/-! ### Moving a finite constant across an `EReal` inequality -/

/-- `x - C ≤ y` gives `x ≤ y + C` for a real `C`.  `EReal` is not a group, so
this is a case analysis rather than `sub_add_cancel`. -/
theorem le_add_of_sub_le {x y : EReal} {C : ℝ} (h : x - (C : EReal) ≤ y) :
    x ≤ y + (C : EReal) := by
  induction x with
  | bot => exact bot_le
  | top =>
      rw [EReal.top_sub_coe] at h
      rw [top_le_iff.mp h]
      simp
  | coe r =>
      induction y with
      | bot =>
          rw [← EReal.coe_sub, le_bot_iff] at h
          exact absurd h (EReal.coe_ne_bot _)
      | top => simp
      | coe s =>
          rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          linarith

/-! ### The germ step -/

variable {X : Type*} [TopologicalSpace X]

/-- **The germ form of `eq:def-TM` becomes a singularity comparison.**

If `ψ` is presented near `x` as `log ∑|gᵢ|²` plus a bounded remainder, and the
regularization `φm` satisfies the Demailly lower bound `a · log ∑|gᵢ|² - C ≤ φm`
near `x` for the same family, then `a · ψ` is more singular than `φm` at `x`.

`a ≥ 0` is the only hypothesis on the scale; in the application `a = m⁻¹`. -/
theorem moreSingularAt_smul_of_generatorLog_lowerBound
    {psi phim : X → EReal} {x : X} {a C₀ C₁ : ℝ} (ha : 0 ≤ a)
    {N : ℕ} {g : Fin N → X → ℂ} {R : X → ℝ}
    (hpsi : ∀ᶠ y in 𝓝 x, psi y = generatorLog g y + (R y : EReal))
    (hR : ∀ᶠ y in 𝓝 x, R y ≤ C₀)
    (hlow : ∀ᶠ y in 𝓝 x,
      ((a : ℝ) : EReal) * generatorLog g y - (C₁ : EReal) ≤ phim y) :
    MoreSingularAt (fun y => ((a : ℝ) : EReal) * psi y) phim x := by
  refine ⟨C₁ + a * C₀, ?_⟩
  filter_upwards [hpsi, hR, hlow] with y hy hyR hylow
  have hgen : ((a : ℝ) : EReal) * generatorLog g y ≤ phim y + (C₁ : EReal) :=
    le_add_of_sub_le hylow
  have hRle : ((a : ℝ) : EReal) * (R y : EReal) ≤ ((a * C₀ : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hyR ha)
  have hsplit : ((a : ℝ) : EReal) * psi y
      = ((a : ℝ) : EReal) * generatorLog g y + ((a : ℝ) : EReal) * (R y : EReal) := by
    rw [hy]
    exact EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ha)
      (EReal.coe_ne_top _) _ _
  calc ((a : ℝ) : EReal) * psi y
      = ((a : ℝ) : EReal) * generatorLog g y + ((a : ℝ) : EReal) * (R y : EReal) := hsplit
    _ ≤ (phim y + (C₁ : EReal)) + ((a * C₀ : ℝ) : EReal) := add_le_add hgen hRle
    _ = phim y + ((C₁ + a * C₀ : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]

/-! ### The global comparison -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **`eq:def-TM`, third clause, as a singularity comparison.**  A weight
`ψ_𝔞` of `𝔞` at coefficient `1` and the Demailly germ bound for `φm` against
every finite family of germs of `𝔞` give `a · ψ_𝔞 ≤ φm + O(1)` globally.

Sorry-free: the germ bound is a hypothesis. -/
theorem moreSingularOn_smul_of_generatorLog_lowerBound [CompactSpace M]
    {𝔞 : GermIdeal n M} {psi phim : M → EReal} {a : ℝ} (ha : 0 ≤ a)
    (hpsi : HasAnalyticSingularitiesOfType (n := n) psi 1 𝔞)
    (hlow : ∀ (x : M) (N : ℕ) (g : Fin N → M → ℂ), (∀ i, 𝔞.mem x (g i)) →
      ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
        ((a : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ phim y) :
    MoreSingularOn (fun y => ((a : ℝ) : EReal) * psi y) phim univ := by
  refine moreSingularOn_univ_of_forall_moreSingularAt fun x => ?_
  obtain ⟨-, -, hloc⟩ := hpsi
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, heq⟩ := hloc x
  have hmem : ∀ i, 𝔞.mem x (g i) := fun i =>
    mem_of_isPresentation hU hxU hgdiff hgiff i
  obtain ⟨C₁, hC₁⟩ := hlow x N g hmem
  refine moreSingularAt_smul_of_generatorLog_lowerBound (C₀ := C₀) (C₁ := C₁)
    (R := R) (g := g) ha
    (Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_)
    (Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_) hC₁
  · rw [heq y hy]
    norm_num
  · exact (abs_le.mp (hRb y hy)).2

/-! ### `eq:def-TM` from `lem:regularization` -/

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- **`eq:def-TM`.**  Copy-4's ambient regularization, with its third clause in
the form the Step-5 field `ambientUM_lower` asks for.

Given the level `m`, a `ζ`-PSH potential `φ`, and any weight `ψ` of the
multiplier ideal `𝓘(mφ)` at coefficient `1`, the regularization `φ_m` supplied
by `lem:regularization` satisfies both

* `ζ + ddᶜφ_m ≥ -(c/m) ω_Z`, and
* `m⁻¹ ψ ≤ φ_m + O(1)` on all of `Z`, with one constant.

The constant `c` depends only on `(Z, ω_Z)`, as in the source.

**This declaration carries `sorryAx`**, through the single named classical
interface behind `lem:regularization`; the two theorems above it do not. -/
theorem exists_regularization_moreSingularOn_multiplierIdealWeight
    [CompactSpace Z] [ConnectedSpace Z] (omegaZ : KahlerBackground d Z) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ →
        ∀ m : ℕ, 1 ≤ m →
          ∀ psi : Z → EReal,
            HasAnalyticSingularitiesOfType (n := d) psi 1
              (multiplierIdeal (n := d) (m : ℝ) φ) →
            ∃ φm : Z → EReal,
              IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
              MoreSingularOn (fun y => (((m : ℝ)⁻¹ : ℝ) : EReal) * psi y) φm univ := by
  obtain ⟨c, hc, hreg⟩ := exists_regularization_multiplierIdeal_lowerBound omegaZ
  refine ⟨c, hc, fun ζ φ hφ m hm psi hpsi => ?_⟩
  obtain ⟨φm, hφm, hbound⟩ := hreg ζ φ hφ m hm
  have hapos : (0 : ℝ) ≤ ((m : ℝ)⁻¹ : ℝ) := by positivity
  exact ⟨φm, hφm,
    moreSingularOn_smul_of_generatorLog_lowerBound hapos hpsi hbound⟩

end

end Hironaka.AmbientUMWeightLowerBound
