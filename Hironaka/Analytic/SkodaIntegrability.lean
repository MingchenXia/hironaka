import Hironaka.Analytic.DemaillyApproximationAnalyticType
import Hironaka.Analytic.LelongNumberChartTransport
import Hironaka.Analytic.MultiplierIdealProductComparison
import Hironaka.Analytic.PshConvexCone

set_option autoImplicit false

/-!
# Skoda's integrability theorem

Source: H. Skoda, *Sous-ensembles analytiques d'ordre fini ou infini dans `ℂⁿ`*, Bull. Soc.
Math. France **100** (1972); in the form of Demailly, *Analytic methods in algebraic geometry*,
Lemma 5.6 (a): if `ν(φ, x) < 1` then `e^{-2φ}` is integrable near `x`.  Copy-4 uses it in
`sec:setup` (`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1422`):
"By Skoda's theorem and `ν(V_θ, x_*) = 0`, `𝔅_q` and `𝔅̄_q` are unit ideals near `x_*`".

The project's normalisations are `𝓘(cφ) = {g : |g|² e^{-cφ} integrable near x}`
(`Hironaka.HolomorphicIdealSheaves.multiplierIdeal`, no factor `2`) and
`ν(φ, x) = sup {γ : φ ≤ γ log ‖· - x‖ + O(1)}` (`Hironaka.lelongNumber`, so
`ν(log |z₁|²) = 2`).  In these normalisations Skoda's theorem reads

  `c ν(φ, x) < 2  ⟹  1 ∈ 𝓘(cφ)_x`,  i.e. `e^{-cφ}` is integrable near `x`,

which is sharp (`φ = log |z₁|²`, `c = 1`).

## The proof: Demailly's Bergman-kernel argument

Skoda's original proof goes through the Riesz representation of `φ` and Jensen's inequality.
This module instead uses the local Bergman kernel machinery that the Demailly 1992 programme
(`TN.3.3.DEMPROVE`) already proved, which gives the theorem in a few lines and with the sharp
constant.  In the chart at `x`, with `Ψ = c (φ ∘ e⁻¹ + ρ)` plurisubharmonic on a ball `B`:

* **Ohsawa--Takegoshi at a point** (`BergmanWeightConvergence.le_bergmanWeight`): wherever
  `Ψ(z) > -∞`, `Ψ(z) - log C ≤ log K_{B, e^{-Ψ}}(z)`.
* If `x ∈ Z(𝓘(cφ))`, every element `f` of the Bergman unit ball of `B` vanishes at `z₀ = e(x)`,
  since `f ∘ e ∈ 𝓘(cφ)_x` (`DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart`).
  The unit ball is uniformly bounded near `z₀` (`BergmanSupWeight.norm_le_bergmanBoundConst`),
  so by the Cauchy estimates (`Hironaka.norm_sub_le_of_forall_norm_le`) `|f(z)| ≤ A ‖z - z₀‖`
  uniformly in `f`; hence `K(z) ≤ A² ‖z - z₀‖²`.
* Together: `Ψ(z) ≤ 2 log ‖z - z₀‖ + O(1)`, i.e. `φ ≤ (2/c) log ‖e(·) - e(x)‖ + O(1)` near `x`,
  so `2/c` is an admissible exponent and `ν(φ, x) ≥ 2/c`.

## Main results

* `exists_log_bound_of_forall_bergmanBall_vanish` — the local core on `ℂᵈ`.
* `ofReal_two_div_le_lelongNumber_of_mem_zeroLocus` — **`x ∈ Z(𝓘(cφ)) ⟹ ν(φ, x) ≥ 2/c`**, for
  every `θ`-psh `φ` on every complex manifold (no compactness, no Kähler form, any dimension).
* `notMem_zeroLocus_multiplierIdeal_of_lelongNumber_lt`,
  `one_mem_multiplierIdeal_of_lelongNumber_lt` — **Skoda**: `ν(φ, x) < 2/c ⟹ 1 ∈ 𝓘(cφ)_x`.
* `not_subset_zeroLocus_multiplierIdeal_of_lelongNumber_eq_zero` — Copy-4's use: if
  `ν(φ, x_*) = 0` at a point `x_*` of `S`, then `S ⊄ Z(𝓘(qφ))` for every `q ≥ 1`; with
  `S = V` and `φ = V_θ` this is the Skoda clause of input (I2) in
  `Copy4FixedDataFromInputs.TraceInput`.

Sorry-free.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.SkodaIntegrability

open Hironaka.HolomorphicIdealSheaves Hironaka.NonKahlerLocus
  BergmanSupWeight BergmanWeightConvergence LelongNumberChartTransport

noncomputable section

/-! ### The local core on `ℂᵈ` -/

section Local

variable {d : ℕ}

/-- The Bergman kernel does not depend on which Borel structure of `ℂᵈ` is used. -/
theorem bergmanSup_congr_instance (i₁ : MeasurableSpace (ComplexModel d))
    (b₁ : @BorelSpace _ _ i₁) (i₂ : MeasurableSpace (ComplexModel d)) (b₂ : @BorelSpace _ _ i₂)
    (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    @bergmanSup d i₁ b₁ D w y = @bergmanSup d i₂ b₂ D w y := by
  have h₁ : i₁ = borel (ComplexModel d) := b₁.measurable_eq
  have h₂ : i₂ = borel (ComplexModel d) := b₂.measurable_eq
  subst h₁
  subst h₂
  rfl

/-- **Ohsawa--Takegoshi at a point, at level one, in the ambient Borel structure**:
`Ψ(y) - log C ≤ log K_{B, e^{-Ψ}}(y)` wherever `Ψ(y)` is finite, for one constant `C` depending
only on the dimension and on a bound `R` for `B`. -/
theorem exists_le_log_bergmanSup (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B → ∀ y ∈ B, ∀ p : ℝ, P y = p →
        (((p - Real.log C : ℝ)) : EReal) ≤
          ENNReal.log (bergmanSup B (fun z => multiplierWeight 1 (P z)) y) := by
  obtain ⟨C, hC, hOT⟩ := le_bergmanWeight d R hR
  refine ⟨C, hC, fun B hB hconv hbd P hP y hy p hp => ?_⟩
  have h := hOT B hB hconv hbd P hP 1 le_rfl y hy p hp
  simp only [bergmanWeight, bergmanLog, Nat.cast_one, inv_one, one_mul, EReal.coe_one] at h
  rw [bergmanSup_congr_instance _ _ (borel (ComplexModel d)) (@BorelSpace.mk _ _ (borel _) rfl)]
  exact h

/-- **The local core of Skoda's theorem.**  Let `Ψ` be plurisubharmonic near the closed ball
`closedBall z₀ R`.  If every element of the Bergman unit ball of `ball z₀ R` for the weight
`e^{-Ψ}` vanishes at `z₀`, then `Ψ ≤ 2 log ‖· - z₀‖ + C` on a punctured ball about `z₀`. -/
theorem exists_log_bound_of_forall_bergmanBall_vanish {W : Set (ComplexModel d)}
    {Ψ : ComplexModel d → EReal} (hΨ : PlurisubharmonicOn Ψ W) {z₀ : ComplexModel d} {R : ℝ}
    (hR : 0 < R) (hRW : closedBall z₀ R ⊆ W)
    (hvan : ∀ f ∈ bergmanBall (ball z₀ R) (fun z => multiplierWeight 1 (Ψ z)), f z₀ = 0) :
    ∃ r C : ℝ, 0 < r ∧ ∀ z ∈ ball z₀ r, z ≠ z₀ →
      Ψ z ≤ ((2 * Real.log ‖z - z₀‖ + C : ℝ) : EReal) := by
  set D : Set (ComplexModel d) := ball z₀ R with hD
  set w : ComplexModel d → ℝ≥0∞ := fun z => multiplierWeight 1 (Ψ z) with hw
  -- the weight is bounded below on `D`
  obtain ⟨Cu, -, hCu⟩ :=
    hΨ.exists_nonnegative_compact_upper_bound (isCompact_closedBall z₀ R) hRW
  set δ : ℝ := Real.exp (-((1 : ℝ) * Cu)) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z := by
    intro z hz
    rw [hw, hδdef, ← multiplierWeight_coe]
    exact multiplierWeight_antitone zero_le_one (hCu z (ball_subset_closedBall hz))
  set s : ℝ := R / 2 with hsdef
  have hs : 0 < s := by positivity
  have hsub : closedBall z₀ s ⊆ D := closedBall_subset_ball (by linarith)
  set L : ℝ := bergmanBoundConst d δ s with hL
  have hL0 : 0 ≤ L := bergmanBoundConst_nonneg d δ s
  set A : ℝ := L / (s / 2 / 2) + 1 with hA
  have hA0 : 0 < A := by positivity
  -- every element of the Bergman unit ball is `O(‖z - z₀‖)`, uniformly
  have hlin : ∀ f ∈ bergmanBall D w, ∀ z ∈ ball z₀ (s / 2 / 2), ‖f z‖ ≤ A * ‖z - z₀‖ := by
    intro f hf z hz
    have hbound : ∀ u ∈ ball z₀ (s / 2), ‖f u‖ ≤ L :=
      fun u hu => norm_le_bergmanBoundConst hδ hs hsub hlow hf hu
    have hdiff : DifferentiableOn ℂ f (ball z₀ (s / 2)) :=
      hf.1.mono (ball_subset_ball (by linarith))
    have h := Hironaka.norm_sub_le_of_forall_norm_le
      (by positivity : (0 : ℝ) < s / 2) hdiff hbound hz (mem_ball_self (by positivity))
    rw [hvan f hf, sub_zero] at h
    calc ‖f z‖ ≤ L / (s / 2 / 2) * ‖z - z₀‖ := h
      _ ≤ A * ‖z - z₀‖ := by
          gcongr
          rw [hA]
          linarith
  -- hence the kernel is `O(‖z - z₀‖²)`
  have hker : ∀ z ∈ ball z₀ (s / 2 / 2),
      bergmanSup D w z ≤ ENNReal.ofReal ((A * ‖z - z₀‖) ^ 2) := by
    intro z hz
    refine bergmanSup_le fun f hf => ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (hlin f hf z hz) 2
  -- Ohsawa--Takegoshi
  obtain ⟨C, hC, hOT⟩ := exists_le_log_bergmanSup (d := d) (‖z₀‖ + R) (by positivity)
  refine ⟨s / 2 / 2, Real.log C + 2 * Real.log A, by positivity, fun z hz hne => ?_⟩
  have hzD : z ∈ D := ball_subset_ball (by linarith) hz
  have hpos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hbd : ∀ u ∈ D, ‖u‖ < ‖z₀‖ + R := by
    intro u hu
    have h1 : ‖u - z₀‖ < R := mem_ball_iff_norm.mp hu
    have h2 : ‖u‖ ≤ ‖u - z₀‖ + ‖z₀‖ := by
      simpa using norm_add_le (u - z₀) z₀
    linarith
  have hΨD : PlurisubharmonicOn Ψ D := fun u hu => hΨ u (hRW (ball_subset_closedBall hu))
  induction hΨz : Ψ z using EReal.rec with
  | bot => exact bot_le
  | top =>
      exfalso
      obtain ⟨U, -, hzU, hU⟩ := hΨ z (hRW (ball_subset_closedBall hzD))
      exact hU.ne_top z hzU hΨz
  | coe p =>
      have h1 := hOT D isOpen_ball (convex_ball z₀ R) hbd Ψ hΨD z hzD p hΨz
      have h2 : ENNReal.log (bergmanSup D w z) ≤
          ((Real.log ((A * ‖z - z₀‖) ^ 2) : ℝ) : EReal) := by
        rw [← ENNReal.log_ofReal_of_pos (by positivity)]
        exact ENNReal.log_monotone (hker z hz)
      have h3 := h1.trans h2
      rw [EReal.coe_le_coe_iff] at h3
      rw [EReal.coe_le_coe_iff]
      have hlog : Real.log ((A * ‖z - z₀‖) ^ 2) = 2 * Real.log A + 2 * Real.log ‖z - z₀‖ := by
        rw [Real.log_pow, Real.log_mul hA0.ne' hpos.ne']
        push_cast
        ring
      linarith

end Local

/-! ### Skoda's theorem on a complex manifold -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem multiplierWeight_one_mul (c : ℝ) (a : EReal) :
    multiplierWeight 1 ((c : EReal) * a) = multiplierWeight c a := by
  simp only [multiplierWeight, EReal.coe_one, one_mul]

/-- **Points of the zero locus of `𝓘(cφ)` have Lelong number at least `2/c`.**  For every
`θ`-psh `φ` on a complex manifold, every `c > 0` and every `x` with `x ∈ Z(𝓘(cφ))`,
`ν(φ, x) ≥ 2/c` (project normalisations: `𝓘(cφ)` uses `e^{-cφ}`, `ν(log |z₁|²) = 2`). -/
theorem ofReal_two_div_le_lelongNumber_of_mem_zeroLocus {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) {c : ℝ} (hc : 0 < c) {x : M}
    (hx : x ∈ (multiplierIdeal (n := n) c φ).zeroLocus) :
    ENNReal.ofReal (2 / c) ≤ lelongNumber (n := n) φ x := by
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel n := e.val x with hz₀
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hφ e z₀ (e.val.map_source hxs)
  obtain ⟨hWo, -, hρs, -⟩ := hρ
  obtain ⟨R₀, hR₀, hR₀W⟩ := Metric.isOpen_iff.mp hWo z₀ hz₀W
  set R : ℝ := R₀ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRW : closedBall z₀ R ⊆ W := (closedBall_subset_ball (by linarith)).trans hR₀W
  set Φ : ComplexModel n → EReal := fun z => chartFunction φ e z + (ρ z : EReal) with hΦ
  set Ψ : ComplexModel n → EReal := fun z => (c : EReal) * Φ z with hΨ
  have hΨpsh : PlurisubharmonicOn Ψ W := hpsh.const_mul hc
  have hwΦ : AEMeasurable (fun z => multiplierWeight c (Φ z)) (volume.restrict (ball z₀ R)) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((hpsh.mono (ball_subset_closedBall.trans hRW)).upperSemicontinuousOn) hc.ne'
  -- every element of the Bergman unit ball vanishes at `z₀`
  have hvan : ∀ f ∈ bergmanBall (ball z₀ R) (fun z => multiplierWeight 1 (Ψ z)), f z₀ = 0 := by
    intro f hf
    have hint : ∫⁻ z in ball z₀ R, multiplierDensity Φ c f z ∂volume ≤ 1 := by
      have h := hf.2
      simp only [hΨ, multiplierWeight_one_mul] at h
      exact h
    have hG : MultiplierIntegrableAt Φ c f z₀ volume := by
      refine ⟨hc, ball z₀ R, isOpen_ball, mem_ball_self hR, hf.1, ?_,
        hint.trans_lt ENNReal.one_lt_top⟩
      exact ((ENNReal.continuous_ofReal.comp_continuousOn
          (hf.1.continuousOn.norm.pow 2)).aemeasurable isOpen_ball.measurableSet).mul hwΦ
    have hmem := DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hφ hc e hWo
      hρs.continuousOn hxs hz₀W hG
    exact hx _ hmem
  obtain ⟨r, C, hr, hbound⟩ := exists_log_bound_of_forall_bergmanBall_vanish hΨpsh hR hRW hvan
  -- back to the manifold
  have hρc : ContinuousAt ρ z₀ := (hρs.continuousOn z₀ hz₀W).continuousAt (hWo.mem_nhds hz₀W)
  have hT : Tendsto e.val (𝓝 x) (𝓝 z₀) := e.val.continuousAt hxs
  refine ofReal_le_lelongNumber (s := 2 / c) (C := C / c - ρ z₀ + 1) (by positivity) ?_
  filter_upwards [eventually_mem_chart_ball (n := n) (x := x) hr,
    nhdsWithin_le_nhds (hT.eventually (hρc.eventually (Metric.ball_mem_nhds (ρ z₀) one_pos)))]
    with y hy hyρ
  obtain ⟨hys, hpos, hlt⟩ := hy
  have hne : e.val y ≠ z₀ := by
    intro h
    rw [h, sub_self, norm_zero] at hpos
    exact lt_irrefl _ hpos
  have h1 := hbound (e.val y) (mem_ball_iff_norm.mpr hlt) hne
  have hφy : chartFunction φ e (e.val y) = φ y := chartFunction_apply_chart hys
  simp only [hΨ, hΦ, hφy] at h1
  have hρy : ρ z₀ - 1 < ρ (e.val y) := by
    have h2 : dist (ρ (e.val y)) (ρ z₀) < 1 := hyρ
    rw [Real.dist_eq] at h2
    linarith [(abs_lt.mp h2).1]
  induction hφ' : φ y using EReal.rec with
  | bot => exact bot_le
  | top =>
      exfalso
      rw [hφ', EReal.top_add_coe, EReal.coe_mul_top_of_pos hc] at h1
      exact EReal.coe_ne_top _ (top_le_iff.mp h1)
  | coe t =>
      rw [hφ', ← EReal.coe_add, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h1
      rw [EReal.coe_le_coe_iff]
      have h2 : t + ρ (e.val y) ≤ (2 * Real.log ‖e.val y - z₀‖ + C) / c := by
        rw [le_div_iff₀ hc]
        linarith
      have h3 : (2 * Real.log ‖e.val y - z₀‖ + C) / c =
          2 / c * Real.log ‖e.val y - z₀‖ + C / c := by
        field_simp
      linarith

/-- **Skoda's integrability theorem, zero-locus form**: `ν(φ, x) < 2/c ⟹ x ∉ Z(𝓘(cφ))`. -/
theorem notMem_zeroLocus_multiplierIdeal_of_lelongNumber_lt {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) {c : ℝ} (hc : 0 < c) {x : M}
    (hν : lelongNumber (n := n) φ x < ENNReal.ofReal (2 / c)) :
    x ∉ (multiplierIdeal (n := n) c φ).zeroLocus :=
  fun hx => (ofReal_two_div_le_lelongNumber_of_mem_zeroLocus hφ hc hx).not_gt hν

/-- A germ of `𝓘(cφ)` which does not vanish at `x` makes `𝓘(cφ)_x` the unit ideal. -/
theorem one_mem_multiplierIdeal_of_notMem_zeroLocus {c : ℝ} {φ : M → EReal} {x : M}
    (hx : x ∉ (multiplierIdeal (n := n) c φ).zeroLocus) :
    (multiplierIdeal (n := n) c φ).mem x (fun _ => 1) := by
  have hx' : ¬ ∀ g, (multiplierIdeal (n := n) c φ).mem x g → g x = 0 := hx
  obtain ⟨g, hg'⟩ := not_forall.mp hx'
  obtain ⟨hg, hgx⟩ := Classical.not_imp.mp hg'
  have hgc : ContinuousAt g x := hg.1.self_of_nhds.continuousAt
  have hne : ∀ᶠ y in 𝓝 x, g y ≠ 0 := hgc.eventually_ne hgx
  have ha : HolomorphicAt n (fun y => (g y)⁻¹) x := by
    filter_upwards [hg.1, hne] with y hy hy0
    exact (differentiableAt_inv (𝕜 := ℂ) hy0).mdifferentiableAt.comp y hy
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_congr
    (MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul ha hg) ?_
  filter_upwards [hne] with y hy
  exact inv_mul_cancel₀ hy

/-- **Skoda's integrability theorem** (Demailly, *Analytic methods*, Lemma 5.6 (a), in the
project normalisations): if `ν(φ, x) < 2/c` then `1 ∈ 𝓘(cφ)_x`, i.e. `e^{-cφ}` is integrable
on a neighbourhood of `x` in the preferred chart. -/
theorem one_mem_multiplierIdeal_of_lelongNumber_lt {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) {c : ℝ} (hc : 0 < c) {x : M}
    (hν : lelongNumber (n := n) φ x < ENNReal.ofReal (2 / c)) :
    (multiplierIdeal (n := n) c φ).mem x (fun _ => 1) :=
  one_mem_multiplierIdeal_of_notMem_zeroLocus
    (notMem_zeroLocus_multiplierIdeal_of_lelongNumber_lt hφ hc hν)

/-- **Zero Lelong number**: `ν(φ, x) = 0 ⟹ x ∉ Z(𝓘(cφ))` for every `c > 0`. -/
theorem notMem_zeroLocus_multiplierIdeal_of_lelongNumber_eq_zero {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) {c : ℝ} (hc : 0 < c) {x : M}
    (hν : lelongNumber (n := n) φ x = 0) :
    x ∉ (multiplierIdeal (n := n) c φ).zeroLocus := by
  refine notMem_zeroLocus_multiplierIdeal_of_lelongNumber_lt hφ hc ?_
  rw [hν]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- **Copy-4 `sec:setup`, the Skoda clause**: if `ν(φ, x_*) = 0` at a point `x_*` of `S`, then
`S ⊄ Z(𝓘(qφ))` for every `q ≥ 1`.  With `S = V` and `φ = V_θ` this is the clause
`∀ q ≥ 1, ¬ V ⊆ Z(𝓘(q V_θ))` of input (I2) in `Copy4FixedDataFromInputs.TraceInput`. -/
theorem not_subset_zeroLocus_multiplierIdeal_of_lelongNumber_eq_zero
    {θ : SmoothRealForm n M 2} {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) {S : Set M}
    {x : M} (hxS : x ∈ S) (hν : lelongNumber (n := n) φ x = 0) :
    ∀ q : ℕ, 1 ≤ q → ¬ S ⊆ (multiplierIdeal (n := n) (q : ℝ) φ).zeroLocus := by
  intro q hq hS
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact notMem_zeroLocus_multiplierIdeal_of_lelongNumber_eq_zero hφ hqR hν (hS hxS)

end Manifold

end

end Hironaka.SkodaIntegrability
