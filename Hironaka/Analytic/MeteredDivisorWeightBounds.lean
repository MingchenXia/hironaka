import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.FactorizedWeightForm

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The weight of a metered divisor is bounded off its support

Source: Copy-4, `sec:qpsh` and the collar step of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`), where the assertion used is
"`ψ_{𝓘_W}` is bounded on `Λ`" for a compact `Λ` disjoint from the support.

A `MeteredEffectiveQDivisor` records `ψ_E = ∑ aᵢ log |gᵢ|² + h` with `aᵢ ≥ 0`
rational, `gᵢ` holomorphic and `h` chartwise smooth.  Away from the support —
that is, at a point where `ψ_E ≠ -∞` — every generator carrying a positive
coefficient is nonzero, so `ψ_E` agrees near that point with a real function
continuous there.  Compactness then gives a single two-sided bound on any
compact set disjoint from the support.

This is the `ψ`-calculus the collar estimate runs on: it is what makes
`ψ_D + O(1)` a legitimate bookkeeping device away from `D`.  Everything here is
sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.MeteredDivisorWeightBounds

open Hironaka.HolomorphicIdealSheaves
  Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite `EReal` sum with one `⊥` entry is `⊥`; no hypothesis on the other
entries is needed, because `⊥ + x = ⊥` for every `x`. -/
theorem sum_eq_bot_of_eq_bot {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → EReal} {i₀ : ι} (hi₀ : i₀ ∈ s) (h : f i₀ = ⊥) :
    ∑ i ∈ s, f i = ⊥ := by
  rw [← Finset.add_sum_erase s f hi₀, h, EReal.bot_add]

/-- The coercion `ℝ → EReal` commutes with finite sums. -/
theorem coe_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

/-- Continuity at a point of a finite sum. -/
theorem continuousAt_finsetSum {ι X : Type*} [TopologicalSpace X] (s : Finset ι)
    {f : ι → X → ℝ} {x : X} (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x :=
  tendsto_finsetSum s hf

/-- The single-generator logarithmic weight, written as a real logarithm. -/
theorem generatorLog_single_eq_coe {X : Type*} {g : X → ℂ} {y : X} (hg : g y ≠ 0) :
    generatorLog (fun _ : Fin 1 => g) y = ((Real.log (‖g y‖ ^ 2) : ℝ) : EReal) := by
  rw [generatorLog_of_nonzero ⟨0, hg⟩]
  congr 1
  simp [generatorNormSq]

/-- Chartwise smoothness on an open set gives continuity at each of its points. -/
theorem continuousAt_of_chartContDiffOn {h : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hh : ∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U))
    {x : M} (hxU : x ∈ U) : ContinuousAt h x := by
  have hxe : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have hmem : (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target ∩
        (complexChartAt (n := n) x).val.symm ⁻¹' U :=
    ⟨(complexChartAt (n := n) x).val.map_source hxe, by
      rw [mem_preimage, (complexChartAt (n := n) x).val.left_inv hxe]; exact hxU⟩
  have h1 : ContinuousAt (fun z => h ((complexChartAt (n := n) x).val.symm z))
      ((complexChartAt (n := n) x).val x) :=
    ((hh (complexChartAt (n := n) x)).continuousOn _ hmem).continuousAt
      (((complexChartAt (n := n) x).val.isOpen_inter_preimage_symm hU).mem_nhds hmem)
  have h2 := h1.comp ((complexChartAt (n := n) x).val.continuousAt hxe)
  refine h2.congr ?_
  filter_upwards [(complexChartAt (n := n) x).val.open_source.mem_nhds hxe] with y hy
  simp [(complexChartAt (n := n) x).val.left_inv hy]

/-- **Off its support, the weight of a metered divisor is a real function,
continuous there.**  Concretely `ψ_E = ∑ aᵢ log ‖gᵢ‖² + h` near the point, with
every `gᵢ` carrying a positive coefficient nonvanishing. -/
theorem exists_real_continuousAt_eventuallyEq_of_notMem_support (E : MeteredEffectiveQDivisor n M) {x : M}
    (hx : x ∉ E.support) :
    ∃ F : M → ℝ, ContinuousAt F x ∧ ∀ᶠ y in 𝓝 x, E.weight y = ((F y : ℝ) : EReal) := by
  classical
  obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, -, hh, hw, -⟩ := E.local_presentation x
  have hxbot : E.weight x ≠ ⊥ := hx
  -- every generator with a positive coefficient is nonzero at `x`
  have hgx : ∀ i, 0 < a i → g i x ≠ 0 := by
    intro i hai hgi
    refine hxbot ?_
    rw [hw x hxU]
    refine (EReal.add_eq_bot_iff.mpr (Or.inl ?_))
    refine sum_eq_bot_of_eq_bot (Finset.mem_univ i) ?_
    rw [(generatorLog_eq_bot_iff _ x).mpr (fun _ => hgi),
      EReal.coe_mul_bot_of_pos (by exact_mod_cast hai)]
  set F : M → ℝ := fun y => (∑ i, (a i : ℝ) * Real.log (‖g i y‖ ^ 2)) + h y with hF
  have hgc : ∀ i, ContinuousAt (g i) x := by
    intro i
    exact ((hg i).continuousOn).continuousAt (hU.mem_nhds hxU)
  have hhc : ContinuousAt h x := continuousAt_of_chartContDiffOn hU hh hxU
  refine ⟨F, ?_, ?_⟩
  · refine ContinuousAt.add (continuousAt_finsetSum _ fun i _ => ?_) hhc
    rcases eq_or_lt_of_le (ha i) with hai | hai
    · simp only [← hai, Rat.cast_zero, zero_mul]
      exact continuousAt_const
    · have hne : g i x ≠ 0 := hgx i hai
      refine continuousAt_const.mul ?_
      exact (Real.continuousAt_log (by positivity)).comp
        (((hgc i).norm).pow 2)
  · have hne : ∀ᶠ y in 𝓝 x, ∀ i, 0 < a i → g i y ≠ 0 := by
      rw [eventually_all]
      intro i
      by_cases hai : 0 < a i
      · have := (hgc i).eventually (isOpen_ne.mem_nhds (hgx i hai))
        filter_upwards [this] with y hy _ using hy
      · exact Eventually.of_forall fun y hy => absurd hy hai
    filter_upwards [hU.mem_nhds hxU, hne] with y hyU hyne
    rw [hw y hyU, hF]
    have hterm : ∀ i, ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y =
        (((a i : ℝ) * Real.log (‖g i y‖ ^ 2) : ℝ) : EReal) := by
      intro i
      rcases eq_or_lt_of_le (ha i) with hai | hai
      · simp [← hai]
      · rw [generatorLog_single_eq_coe (hyne i hai), ← EReal.coe_mul]
    simp only [hterm]
    rw [← coe_finsetSum, ← EReal.coe_add]

/-- **A compact set disjoint from the support carries a two-sided bound on the
weight.**  This is Copy-4's "`ψ_E` is bounded on `Λ`". -/
theorem exists_bound_of_isCompact_disjoint_support (E : MeteredEffectiveQDivisor n M) {Λ : Set M} (hΛ : IsCompact Λ)
    (hdisj : Disjoint Λ E.support) :
    ∃ C : ℝ, ∀ y ∈ Λ, ((-C : ℝ) : EReal) ≤ E.weight y ∧ E.weight y ≤ ((C : ℝ) : EReal) := by
  classical
  have key : ∀ x ∈ Λ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      ((-C : ℝ) : EReal) ≤ E.weight y ∧ E.weight y ≤ ((C : ℝ) : EReal) := by
    intro x hxΛ
    have hx : x ∉ E.support := Set.disjoint_left.mp hdisj hxΛ
    obtain ⟨F, hFc, hFeq⟩ := exists_real_continuousAt_eventuallyEq_of_notMem_support E hx
    refine ⟨|F x| + 1, ?_⟩
    have hbnd : ∀ᶠ y in 𝓝 x, |F y| ≤ |F x| + 1 := by
      have := hFc (Metric.ball_mem_nhds (F x) one_pos)
      filter_upwards [this] with y hy
      have : |F y - F x| < 1 := by
        simpa [Real.dist_eq] using (Metric.mem_ball.mp hy)
      have := abs_sub_abs_le_abs_sub (F y) (F x)
      linarith [abs_nonneg (F x), (abs_lt.mp ‹|F y - F x| < 1›).1,
        (abs_lt.mp ‹|F y - F x| < 1›).2, le_abs_self (F y), neg_abs_le (F y)]
    filter_upwards [hFeq, hbnd] with y hy hyb
    rw [hy]
    exact ⟨EReal.coe_le_coe_iff.mpr (by linarith [neg_abs_le (F y), abs_le.mp hyb |>.1]),
      EReal.coe_le_coe_iff.mpr ((le_abs_self (F y)).trans hyb)⟩
  choose! Cf hCf using key
  set V : M → Set M := fun x =>
    {y | ((-Cf x : ℝ) : EReal) ≤ E.weight y ∧ E.weight y ≤ ((Cf x : ℝ) : EReal)} with hV
  obtain ⟨t, htΛ, htcover⟩ := hΛ.elim_nhds_subcover V (fun x hx => hCf x hx)
  refine ⟨∑ x ∈ t, |Cf x|, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := by simpa using htcover hy
  have hle : |Cf x| ≤ ∑ x ∈ t, |Cf x| :=
    Finset.single_le_sum (f := fun x => |Cf x|) (fun i _ => abs_nonneg _) hxt
  have h1 : Cf x ≤ ∑ x ∈ t, |Cf x| := (le_abs_self _).trans hle
  have h2 : -(∑ x ∈ t, |Cf x|) ≤ -Cf x := by
    have := neg_abs_le (Cf x)
    linarith
  exact ⟨le_trans (EReal.coe_le_coe_iff.mpr h2) hyx.1,
    le_trans hyx.2 (EReal.coe_le_coe_iff.mpr h1)⟩


end

end Hironaka.MeteredDivisorWeightBounds
