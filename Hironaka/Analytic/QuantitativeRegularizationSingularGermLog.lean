import Hironaka.Analytic.QuantitativeRegularizationSingularGermDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The finite-family logarithmic form of Step 4 of Copy-4 `lem:regularization`

Source: Copy-4, `lem:regularization`, Step 4 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationSingularGermDomination.normSq_le_bergmanSup_multiplierWeight`
dominates **one** germ of `𝓘(mΨ)` by the Bergman sup-weight of the singular weight
`e^{-mΨ}`.  The statement of `QuantitativeRegularization` asks instead for a **finite
family** `g : Fin N → _` of germs and for the inequality in its logarithmic, `m`-scaled
form

> `m⁻¹ · generatorLog g y - C ≤ m⁻¹ · bergmanLog B_j (e^{-mΨ}) y`,

i.e. `m⁻¹ log ∑ᵢ |gᵢ|² ≤ ψ_{j,m} + O(1)`.  This module is that passage.  It is pure
bookkeeping — no new analysis — and it is worth isolating because each of its three steps
is a place where the extended arithmetic could silently lose the bound:

* `ofReal_generatorNormSq_le_sum_mul`: the individual bounds add up.  `∑ᵢ |gᵢ y|²` is a
  *finite* sum of nonnegative reals, so `ENNReal.ofReal` of it is the sum of the
  `ENNReal.ofReal`s and the common factor `b` factors out of the sum.
* `generatorLog_le_log_add`: taking `ENNReal.log`.  Here `ENNReal.log_mul_add` is
  unconditional — `log (x * y) = log x + log y` holds even at `0` and `⊤`, because
  `⊥ + ⊤ = ⊥` in `EReal` matches `0 * ⊤ = 0` in `ℝ≥0∞` — so the empty family
  (`generatorLog = ⊥`) and a vanishing kernel need no separate treatment.
* `exists_const_generatorLog_le_bergmanLog`: dividing by `m`.  `EReal` multiplication does
  not distribute over addition in general, but it does for a *finite nonnegative* left
  factor (`EReal.left_distrib_of_nonneg_of_ne_top`), and `m⁻¹` is one.

The constant is `∑ᵢ (C · Nᵢ + 1) + 1` with `C = pointExtensionConst d (r/2) Mθ (2S) S` the
weight-free constant of the smooth theory and `Nᵢ` the weighted mass of `gᵢ`; the trailing
`+ 1` is there only so the constant is `≠ 0`, which is what makes its logarithm a *real*
number and lets the empty family be handled by the same formula rather than a case split.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators

namespace Hironaka.QuantitativeRegularizationSingularGermLog

noncomputable section

open Hironaka.MongeAmpere BergmanSupWeight
open Hironaka.QuantitativeRegularizationPointExtension
open Hironaka.QuantitativeRegularizationSingularGermDomination

variable {d : ℕ}

/-! ### A family of bounds with a common right factor adds up -/

/-- If `|gᵢ y|² ≤ Kᵢ · b` for every member of a finite family, then
`∑ᵢ |gᵢ y|² ≤ (∑ᵢ Kᵢ) · b`.  Both steps are exact: `ENNReal.ofReal` is additive on
nonnegative reals and multiplication distributes over a finite sum in `ℝ≥0∞`. -/
theorem ofReal_generatorNormSq_le_sum_mul {X : Type*} {N : ℕ} {g : Fin N → X → ℂ}
    {y : X} {K : Fin N → ℝ≥0∞} {b : ℝ≥0∞}
    (h : ∀ i, ENNReal.ofReal (‖g i y‖ ^ 2) ≤ K i * b) :
    ENNReal.ofReal (generatorNormSq g y) ≤ (∑ i, K i) * b := by
  rw [generatorNormSq, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity,
    Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => h i

/-- The logarithmic form of `ofReal_generatorNormSq_le_sum_mul`.

`ENNReal.log_mul_add` is unconditional, so no positivity or finiteness hypothesis is
needed: the empty family, where `generatorLog g y = ⊥`, and a vanishing `b` are both
covered. -/
theorem generatorLog_le_log_add {X : Type*} {N : ℕ} {g : Fin N → X → ℂ}
    {y : X} {K : Fin N → ℝ≥0∞} {b : ℝ≥0∞}
    (h : ∀ i, ENNReal.ofReal (‖g i y‖ ^ 2) ≤ K i * b) :
    generatorLog g y ≤ ENNReal.log (∑ i, K i) + ENNReal.log b := by
  rw [generatorLog_eq_log_sum, ← ENNReal.log_mul_add]
  refine ENNReal.log_monotone ?_
  simpa only [generatorNormSq] using ofReal_generatorNormSq_le_sum_mul (g := g) (y := y) h

/-! ### Step 4 for a finite family of germs of `𝓘(mΨ)` -/

variable {A Ω : Opens (ComplexModel d)} {u : ComplexModel d → EReal}

/-- **A finite family of germs of `𝓘(mΨ)` is dominated by the Bergman weight**
(Copy-4, `lem:regularization`, Step 4, family form).

This is `normSq_le_bergmanSup_multiplierWeight` summed over the family and put under a
logarithm.  The hypotheses are the same, now asked of every member: each `gᵢ` is
holomorphic on the neighbourhood `U` of the cut-off support and has finite weighted mass
`Nᵢ` there, which is exactly what it means for `gᵢ` to be a germ of the multiplier ideal.
The single cut-off `θ` serves every `y` with `‖y - x‖ < r/2` and every member of the
family, so the constant depends on neither. -/
theorem generatorLog_le_bergmanLog_add (hd : 0 < d)
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    (hu : PlurisubharmonicOn u Ω) {m : ℝ} (hm : 0 < m)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {U : Set (ComplexModel d)} (hUo : IsOpen U) (hts : tsupport θ ⊆ U)
    (htsA : tsupport θ ⊆ (A : Set (ComplexModel d)))
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcA : Bjc ⊆ (A : Set (ComplexModel d)))
    {S : ℝ} (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (hN : ∀ i, (∫⁻ z in tsupport θ,
      ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight m (u z)) ≠ ⊤)
    {y : ComplexModel d} (hyBj : y ∈ Bj) (hyx : ‖y - x‖ < r / 2) :
    generatorLog g y ≤
      ENNReal.log (∑ i, (ENNReal.ofReal (pointExtensionConst d (r / 2) Mθ (2 * S) S) *
          (∫⁻ z in tsupport θ,
            ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight m (u z)) + 1))
        + bergmanLog Bj (fun z => multiplierWeight m (u z)) y :=
  generatorLog_le_log_add fun i =>
    normSq_le_bergmanSup_multiplierWeight hd hAconv hAΩ hu hm x hr hθ hθcs hθ1 hθle hUo
      hts htsA (hg i) hMθ hBjo hBjBjc hBjc hBjcA hnormS (hN i) hyBj hyx

/-! ### The `m`-scaled form the regularization statement consumes -/

/-- **Step 4 in the shape `QuantitativeRegularization` asks for.**

For one fixed finite family of germs of `𝓘(mΨ)` there is a single real constant `C` with

> `m⁻¹ · generatorLog g y - C ≤ m⁻¹ · bergmanLog B_j (e^{-mΨ}) y`

for **every** `y ∈ B_j` within `r/2` of `x`.  The constant is uniform in `y` because the
cut-off, hence `pointExtensionConst`, is; and `m⁻¹ · bergmanLog B_j (e^{-mΨ})` is the
local branch `ψ_{j,m}`, so this is the local half of
`φ_m ≥ m⁻¹ ψ_{𝓘(mφ)} + O(1)`.

The `+ 1` inside the constant is what makes it nonzero, hence its `ENNReal.log` a real
number rather than `⊥`; without it the empty family would need its own argument. -/
theorem exists_const_generatorLog_le_bergmanLog (hd : 0 < d)
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    (hu : PlurisubharmonicOn u Ω) {m : ℝ} (hm : 0 < m)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {U : Set (ComplexModel d)} (hUo : IsOpen U) (hts : tsupport θ ⊆ U)
    (htsA : tsupport θ ⊆ (A : Set (ComplexModel d)))
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcA : Bjc ⊆ (A : Set (ComplexModel d)))
    {S : ℝ} (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (hN : ∀ i, (∫⁻ z in tsupport θ,
      ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight m (u z)) ≠ ⊤) :
    ∃ C : ℝ, ∀ y ∈ Bj, ‖y - x‖ < r / 2 →
      ((m⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal)
        ≤ ((m⁻¹ : ℝ) : EReal) * bergmanLog Bj (fun z => multiplierWeight m (u z)) y := by
  set K : ℝ≥0∞ := (∑ i, (ENNReal.ofReal (pointExtensionConst d (r / 2) Mθ (2 * S) S) *
      (∫⁻ z in tsupport θ,
        ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight m (u z)) + 1)) + 1 with hK
  have hK0 : K ≠ 0 := by simp [hK]
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun i _ => ?_, by simp⟩
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hN i), by simp⟩
  -- the logarithm of the constant is a real number
  have hlogK : ENNReal.log K = ((Real.log K.toReal : ℝ) : EReal) :=
    ENNReal.log_pos_real hK0 hKtop
  refine ⟨m⁻¹ * Real.log K.toReal, fun y hyBj hyx => ?_⟩
  -- the family bound, with `K` in place of the bare sum
  have hbase : generatorLog g y ≤ ENNReal.log K +
      bergmanLog Bj (fun z => multiplierWeight m (u z)) y := by
    have hfirst : generatorLog g y ≤ ENNReal.log (∑ i,
        (ENNReal.ofReal (pointExtensionConst d (r / 2) Mθ (2 * S) S) *
          (∫⁻ z in tsupport θ,
            ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight m (u z)) + 1)) +
        bergmanLog Bj (fun z => multiplierWeight m (u z)) y := by
      simpa only [bergmanLog] using
        (generatorLog_le_log_add (g := g) (y := y)
          (K := fun i =>
            ENNReal.ofReal (pointExtensionConst d (r / 2) Mθ (2 * S) S) *
              (∫⁻ z in tsupport θ,
                ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight m (u z)) + 1)
          (b := bergmanSup Bj (fun z => multiplierWeight m (u z)) y)
          fun i =>
            normSq_le_bergmanSup_multiplierWeight hd hAconv hAΩ hu hm x hr hθ hθcs hθ1 hθle
              hUo hts htsA (hg i) hMθ hBjo hBjBjc hBjc hBjcA hnormS (hN i) hyBj hyx)
    refine hfirst.trans ?_
    gcongr
    rw [hK]
    exact le_add_of_nonneg_right zero_le
  -- scale by `m⁻¹ ≥ 0`, which distributes because it is finite and nonnegative
  have hmnn : (0 : EReal) ≤ ((m⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (inv_nonneg.2 hm.le)
  have hmne : ((m⁻¹ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hscaled : ((m⁻¹ : ℝ) : EReal) * generatorLog g y
      ≤ ((m⁻¹ : ℝ) : EReal) * bergmanLog Bj (fun z => multiplierWeight m (u z)) y
        + ((m⁻¹ * Real.log K.toReal : ℝ) : EReal) := by
    refine (mul_le_mul_of_nonneg_left hbase hmnn).trans ?_
    rw [EReal.left_distrib_of_nonneg_of_ne_top hmnn hmne, hlogK, ← EReal.coe_mul]
    exact le_of_eq (add_comm _ _)
  exact EReal.sub_le_of_le_add hscaled

end

end Hironaka.QuantitativeRegularizationSingularGermLog
