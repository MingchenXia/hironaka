import Hironaka.Analytic.QuantitativeRegularizationSingularGermLog
import Hironaka.Analytic.HormanderWeightedL2

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 4 of Copy-4 `lem:regularization` from the germ hypothesis alone

Source: Copy-4, `lem:regularization`, Step 4 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationSingularGermLog.exists_const_generatorLog_le_bergmanLog`
dominates a finite family `g` by the Bergman weight of `e^{-mΨ}`, but it asks for the
family in *chart data* form: a cut-off `θ`, a radius `r`, a derivative bound `Mθ`, an open
set `U ⊇ tsupport θ` on which every `gᵢ` is holomorphic, and finiteness of each weighted
mass `∫_{tsupport θ} |gᵢ|² e^{-mΨ}`.  The statement of `QuantitativeRegularization`
supplies none of that; it supplies the *germ* hypothesis
`gᵢ ∈ 𝓘(mΨ)_x`, i.e. `MultiplierIntegrableAt u m (gᵢ) x volume`.

This module is the passage between the two, and it is the step that removes the
"generators span the multiplier ideal" obligation from the local half of the lemma: the
bound is proved for an **arbitrary** finite family of germs of `𝓘(mΨ)` at `x`, with no
generating system and hence no appeal to Nadel coherence.

The two steps are:

* `exists_isOpen_of_multiplierIntegrableAt` — the family is finite, so the finitely many
  neighbourhoods on which the individual members are holomorphic with finite weighted mass
  intersect in **one** open neighbourhood of `x` that works for all of them.  The empty
  family is covered without a case split: `⋂ i : Fin 0, Uᵢ = univ`.
* `exists_radius_const_generatorLog_le_bergmanLog_of_multiplierIntegrableAt` — a cut-off
  supported in that neighbourhood, from `Hormander.exists_contDiff_cutoff`; its derivative
  bound exists because a `C^∞` function with compact support has a continuous, compactly
  supported differential.

`exists_const_eventually_generatorLog_le_bergmanLog_of_multiplierIntegrableAt` states the
result in the shape the target consumes, `∀ᶠ y in 𝓝 x`, for a point of the Bergman domain
`B_j`.  Note that `x ∈ A` is then automatic from `x ∈ B_j ⊆ B̄_j ⊆ A`.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators

namespace Hironaka.QuantitativeRegularizationMultiplierGermFamily

noncomputable section

open Hironaka.MongeAmpere BergmanSupWeight
open Hironaka.QuantitativeRegularizationSingularGermLog

variable {d : ℕ}

/-! ### One neighbourhood for the whole family -/

/-- **A finite family of germs of `𝓘(mΨ)` at `x` has a common good neighbourhood.**

Each member carries its own open set on which it is holomorphic with finite weighted
mass; the family is finite, so their intersection is still an open neighbourhood of `x`,
and both properties are inherited by every subset of it. -/
theorem exists_isOpen_of_multiplierIntegrableAt
    {m : ℝ} {u : ComplexModel d → EReal} {x : ComplexModel d}
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    (hg : ∀ i, MultiplierIntegrableAt u m (g i) x volume) :
    ∃ U : Set (ComplexModel d), IsOpen U ∧ x ∈ U ∧
      (∀ i, DifferentiableOn ℂ (g i) U) ∧
      ∀ i, (∫⁻ z in U, multiplierDensity u m (g i) z) ≠ ⊤ := by
  choose _hc U hUo hxU hdiff hL2 using hg
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hUo, mem_iInter.2 hxU,
    fun i => (hdiff i).mono (iInter_subset _ i), fun i => ?_⟩
  exact ((lintegral_mono_set (iInter_subset _ i)).trans_lt (hL2 i).2).ne

/-! ### The germ form of Step 4 -/

/-- **Step 4 of `lem:regularization` for an arbitrary finite family of germs of `𝓘(mΨ)`.**

There is a radius `r > 0` and one real constant `C` with

> `m⁻¹ · log ∑ᵢ |gᵢ(y)|² - C ≤ m⁻¹ · log K_{B_j}(y, e^{-mΨ})`

for every `y ∈ B_j` within `r` of `x`.  Both `r` and `C` depend on the family, which is
all the target asks for: the constant there is existentially quantified after the family.

No generating system of `𝓘(mΨ)` appears anywhere, so the local half of the lemma needs
no coherence input. -/
theorem exists_radius_const_generatorLog_le_bergmanLog_of_multiplierIntegrableAt
    (hd : 0 < d) {A Ω : Opens (ComplexModel d)}
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    {u : ComplexModel d → EReal} (hu : PlurisubharmonicOn u Ω)
    {m : ℝ} (hm : 0 < m)
    {x : ComplexModel d} (hxA : x ∈ (A : Set (ComplexModel d)))
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcA : Bjc ⊆ (A : Set (ComplexModel d)))
    {S : ℝ} (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    (hg : ∀ i, MultiplierIntegrableAt u m (g i) x volume) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ y ∈ Bj, ‖y - x‖ < r →
      ((m⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal)
        ≤ ((m⁻¹ : ℝ) : EReal) * bergmanLog Bj (fun z => multiplierWeight m (u z)) y := by
  obtain ⟨U, hUo, hxU, hdiff, hmass⟩ := exists_isOpen_of_multiplierIntegrableAt hg
  -- shrink to a neighbourhood inside `A`, where the psh comparison lives
  have hVo : IsOpen (U ∩ (A : Set (ComplexModel d))) := hUo.inter A.isOpen
  have hxV : x ∈ U ∩ (A : Set (ComplexModel d)) := ⟨hxU, hxA⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVo x hxV
  have hcb : closedBall x (ε / 2) ⊆ U ∩ (A : Set (ComplexModel d)) :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨θ, hθ, hθcs, hθV, hθ1s, hθ01⟩ :=
    Hormander.exists_contDiff_cutoff (isCompact_closedBall x (ε / 2)) hVo hcb
  -- the cut-off is `1` on the ball and bounded by `1` everywhere
  have hθ1 : ∀ z ∈ ball x (ε / 2), θ z = 1 := fun z hz =>
    hθ1s.self_of_nhdsSet z (ball_subset_closedBall hz)
  have hθle : ∀ z, |θ z| ≤ 1 := fun z =>
    abs_le.2 ⟨by linarith [(hθ01 z).1], (hθ01 z).2⟩
  -- a `C^∞` function with compact support has a bounded differential
  obtain ⟨Mθ, hMθ⟩ :=
    ((hθ.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (hθcs.fderiv ℝ))
  refine ⟨ε / 4, by linarith, ?_⟩
  obtain ⟨C, hC⟩ :=
    exists_const_generatorLog_le_bergmanLog (A := A) (Ω := Ω) (u := u) (g := g)
      hd hAconv hAΩ hu hm x (by linarith : (0 : ℝ) < ε / 2) hθ hθcs hθ1 hθle
      hVo hθV (hθV.trans inter_subset_right) hMθ hBjo hBjBjc hBjc hBjcA hnormS
      (fun i => (hdiff i).mono inter_subset_left)
      (fun i => ((lintegral_mono_set (hθV.trans inter_subset_left)).trans_lt
        (lt_of_le_of_ne le_top (hmass i))).ne)
  exact ⟨C, fun y hy hyx => hC y hy (by linarith)⟩

/-- **The germ shape the target consumes.**  For a point of the Bergman domain `B_j`, the
conclusion of the previous theorem is a statement about a neighbourhood of `x`. -/
theorem exists_const_eventually_generatorLog_le_bergmanLog_of_multiplierIntegrableAt
    (hd : 0 < d) {A Ω : Opens (ComplexModel d)}
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    {u : ComplexModel d → EReal} (hu : PlurisubharmonicOn u Ω)
    {m : ℝ} (hm : 0 < m)
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcA : Bjc ⊆ (A : Set (ComplexModel d)))
    {S : ℝ} (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    {x : ComplexModel d} (hxBj : x ∈ Bj)
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    (hg : ∀ i, MultiplierIntegrableAt u m (g i) x volume) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      ((m⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal)
        ≤ ((m⁻¹ : ℝ) : EReal) * bergmanLog Bj (fun z => multiplierWeight m (u z)) y := by
  obtain ⟨r, hr, C, hC⟩ :=
    exists_radius_const_generatorLog_le_bergmanLog_of_multiplierIntegrableAt hd hAconv hAΩ
      hu hm (hBjcA (hBjBjc hxBj)) hBjo hBjBjc hBjc hBjcA hnormS hg
  refine ⟨C, ?_⟩
  filter_upwards [hBjo.mem_nhds hxBj, ball_mem_nhds x hr] with y hy hyr
  exact hC y hy (mem_ball_iff_norm.1 hyr)

end

end Hironaka.QuantitativeRegularizationMultiplierGermFamily
