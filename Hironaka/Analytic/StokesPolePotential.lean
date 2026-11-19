import Hironaka.Analytic.SubmanifoldConcentrationPotential
import Hironaka.Analytic.StokesCutoff
import Hironaka.Coherence.CartanIrreducible

set_option autoImplicit false

/-!
# Poles along a closed analytic set and the cutoffs of the one-sided probe (TN.4 #4)

Blueprint `ana:stokes-pole-potential` and `ana:stokes-cutoffs` (Demailly--Păun, `dp04-kahler-cone:2.1`;
Demailly, `demailly-cadg:III.2.2`, analytic case).

Let `A` be a closed analytic subset of a compact complex manifold `M` with a Kähler form `ω`.

* `isCoherent_vanishingIdeal` — the vanishing ideal `𝓘_A` is coherent (Cartan's theorem,
  `CartanIrreducible.cartanCoherence`).
* `exists_polePotential` — **the pole potential**: a chart-smooth `W ≥ 0` with `W = 0` exactly on
  `A`, `W < 1`, and `C > 0` with `L(log W) ≥ -C ω` at every point where `W > 0`.  Then
  `u = ½ log W` is smooth off `A`, negative, `-∞` exactly on `A` (in the limit), and
  `ddᶜ u ≥ -(C / 2π) ω` off `A`.  `W` is a positive multiple of the weight of a concentration
  partition of `𝓘_A` (`SubmanifoldConcentrationPotential`), whose `s = 0` Hessian bound is
  `ConcentrationPartition.exists_pos_levi_log_weight`.
* `cutoff W m` — `χ_m = θ(e^{u/m})`, extended by `0` on `{W = 0}`, with the convex glue `θ` of
  `StokesCutoff`.  `chartSmooth_cutoff`, `cutoff_nonneg`, `cutoff_le_one`,
  `cutoff_eq_zero_of_lt` (`χ_m = 0` on the open neighbourhood `{W < 4^{-m}}` of `A`),
  `tendsto_cutoff` (`χ_m → 1` off `A`).
* `exists_stokesCutoffs` — **the cutoffs of the one-sided probe**: `χ_m` chart-smooth,
  `0 ≤ χ_m ≤ 1`, `χ_m = 0` on an open neighbourhood of `A`, `χ_m → 1` pointwise off `A`, and
  `ddᶜ χ_m + (C/(m+1)) ω ≥ 0` (CADG III.2.2 b) with the constant `θ'(1) = 4`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.StokesPolePotential

open Hironaka.HolomorphicIdealSheaves SubmanifoldConcentrationPotential StokesCutoff
  ManifoldTubePositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Cartan's theorem**: the vanishing ideal of an analytic subset is coherent. -/
theorem isCoherent_vanishingIdeal {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) :
    (vanishingIdeal (n := n) A).IsCoherent :=
  CartanIrreducible.cartanCoherence A hA

/-- The Levi form depends only on the germ of the function. -/
theorem leviForm_congr_of_eventuallyEq {F G : ComplexModel n → ℝ} {x : ComplexModel n}
    (h : F =ᶠ[𝓝 x] G) (v : ComplexModel n) : leviForm F x v = leviForm G x v := by
  simp only [leviForm, realHessian_eq_fderiv, h.fderiv.fderiv_eq]

/-- A chart-smooth function is continuous at the points of a chart target, in the chart. -/
theorem continuousAt_chart_of_chartSmooth {W : M → ℝ} (hW : ChartSmooth (n := n) W)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ContinuousAt (fun w => W (e.val.symm w)) z :=
  ((hW e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz)

/-! ### The pole potential -/

/-- **A pole potential along a closed analytic set** (`dp04-kahler-cone:2.1` for a coherent ideal,
with `s = 0`): a chart-smooth `W` with `0 ≤ W < 1`, `W = 0` exactly on `A`, and `C > 0` with
`L(log W) ≥ -C ω` at every point where `W > 0`. -/
theorem exists_polePotential [CompactSpace M] (omega : PositiveClasses.KahlerBackground n M)
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hAc : IsClosed A) :
    ∃ (W : M → ℝ) (C : ℝ), 0 < C ∧ ChartSmooth (n := n) W ∧ Continuous W ∧
      (∀ y, 0 ≤ W y) ∧ (∀ y, W y < 1) ∧ (∀ y, W y = 0 ↔ y ∈ A) ∧
      ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        0 < W (e.val.symm z) → ∀ v : ComplexModel n,
          -(C * omega.form.val.coeff e z ![v, Complex.I • v]) ≤
            leviForm (fun w => Real.log (W (e.val.symm w))) z v := by
  classical
  obtain ⟨ι, hι, ⟨P⟩⟩ := exists_of_isCoherent (isCoherent_vanishingIdeal hA)
  obtain ⟨B, hB, hlevi⟩ := P.exists_pos_levi_log_weight omega
  -- the weight is bounded on the compact `M`
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ y, P.weight y ≤ S := by
    obtain ⟨S, hS⟩ := (isCompact_univ.image P.continuous_weight).isBounded.bddAbove
    exact ⟨S, fun y => hS ⟨y, mem_univ y, rfl⟩⟩
  set K : ℝ := |S| + 1 with hK
  have hK0 : 0 < K := by positivity
  have hwK : ∀ y, P.weight y < K := fun y => by
    have := hS y; have := le_abs_self S; linarith
  refine ⟨fun y => P.weight y / K, Real.pi * B, mul_pos Real.pi_pos hB,
    fun e => (P.chartSmooth_weight e).div_const K, P.continuous_weight.div_const K,
    fun y => div_nonneg (P.weight_nonneg y) hK0.le,
    fun y => (div_lt_one hK0).2 (hwK y), fun y => ?_, ?_⟩
  · constructor
    · intro h
      by_contra hy
      have := P.weight_pos_of_notMem hAc hy
      have : 0 < P.weight y / K := div_pos this hK0
      linarith
    · intro hy
      simp [P.weight_eq_zero_of_mem hy]
  · intro e z hz hpos v
    have hpos' : 0 < P.weight (e.val.symm z) := by
      have := mul_pos hpos hK0
      rwa [div_mul_cancel₀ _ hK0.ne'] at this
    -- near `z`, `log (W/K) = log W - log K`
    have hev : ∀ᶠ w in 𝓝 z, 0 < P.weight (e.val.symm w) :=
      (continuousAt_chart_of_chartSmooth P.chartSmooth_weight e hz).eventually
        (lt_mem_nhds hpos')
    have hfun : (fun w => Real.log (P.weight (e.val.symm w) / K)) =ᶠ[𝓝 z]
        (fun w => Real.log (P.weight (e.val.symm w))) + fun _ => -Real.log K := by
      filter_upwards [hev] with w hw
      simp only [Pi.add_apply]
      rw [Real.log_div hw.ne' hK0.ne']
      ring
    have hlog2 : ContDiffAt ℝ 2 (fun w => Real.log (P.weight (e.val.symm w))) z :=
      ((((P.chartSmooth_weight e).contDiffAt (e.val.open_target.mem_nhds hz)).log
        hpos'.ne').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    rw [leviForm_congr_of_eventuallyEq hfun, leviForm_add hlog2 contDiffAt_const,
      leviForm_const, add_zero]
    have h := hlevi e z hz hpos' v
    have hpi := Real.pi_pos
    have key : leviForm (fun w => Real.log (P.weight (e.val.symm w))) z v / Real.pi +
        B * omega.form.val.coeff e z ![v, Complex.I • v] =
        (leviForm (fun w => Real.log (P.weight (e.val.symm w))) z v +
          Real.pi * B * omega.form.val.coeff e z ![v, Complex.I • v]) / Real.pi := by
      field_simp
    rw [key] at h
    have := (div_nonneg_iff.1 h).resolve_right (fun h' => absurd h'.2 (not_le.2 hpi))
    linarith [this.1]

/-! ### The cutoffs -/

section Cutoff

variable {X : Type*}

/-- **The cutoff** `χ_m = θ(e^{u/m})`, `u = ½ log W`, extended by `0` where `W = 0`. -/
def cutoff (W : X → ℝ) (m : ℝ) (y : X) : ℝ :=
  if 0 < W y then glue (Real.exp (Real.log (W y) / 2 / m)) else 0

/-- The threshold `4^{-m}` below which the cutoff vanishes. -/
def threshold (m : ℝ) : ℝ := Real.exp (-(2 * m * Real.log 2))

theorem threshold_pos (m : ℝ) : 0 < threshold m := Real.exp_pos _

theorem cutoff_eq_zero_of_lt {W : X → ℝ} {m : ℝ} (hm : 0 < m) {y : X}
    (hy : W y < threshold m) : cutoff W m y = 0 := by
  unfold cutoff
  split_ifs with hpos
  · apply glue_exp_eq_zero hm
    have hlog : Real.log (W y) ≤ -(2 * m * Real.log 2) := by
      rw [← Real.log_exp (-(2 * m * Real.log 2))]
      exact Real.log_le_log hpos hy.le
    linarith
  · rfl

theorem cutoff_nonneg (W : X → ℝ) (m : ℝ) (y : X) : 0 ≤ cutoff W m y := by
  unfold cutoff
  split_ifs
  · exact glue_exp_nonneg _ _
  · exact le_rfl

theorem cutoff_le_one {W : X → ℝ} (hW1 : ∀ y, W y < 1) {m : ℝ} (hm : 0 < m) (y : X) :
    cutoff W m y ≤ 1 := by
  unfold cutoff
  split_ifs with hpos
  · refine glue_exp_le_one hm ?_
    have := Real.log_neg hpos (hW1 y)
    linarith
  · exact zero_le_one

theorem tendsto_cutoff {W : X → ℝ} {y : X} (hy : 0 < W y) :
    Tendsto (fun m : ℕ => cutoff W ((m : ℝ) + 1) y) atTop (𝓝 1) := by
  have h := (tendsto_glue_exp (Real.log (W y) / 2)).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, cutoff, if_pos hy, Nat.cast_add, Nat.cast_one]

end Cutoff

/-- Near a point where `W > 0`, the cutoff is `θ ∘ exp ∘ (½ log W / m)`. -/
theorem cutoff_chart_eventuallyEq {W : M → ℝ} (hW : ChartSmooth (n := n) W) (m : ℝ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpos : 0 < W (e.val.symm z)) :
    (fun w => cutoff W m (e.val.symm w)) =ᶠ[𝓝 z]
      fun w => glue (Real.exp (Real.log (W (e.val.symm w)) / 2 / m)) := by
  filter_upwards [(continuousAt_chart_of_chartSmooth hW e hz).eventually (lt_mem_nhds hpos)]
    with w hw
  simp only [cutoff, if_pos hw]

/-- Near a point where `W < 4^{-m}`, the cutoff vanishes. -/
theorem cutoff_chart_eventuallyEq_zero {W : M → ℝ} (hW : ChartSmooth (n := n) W) {m : ℝ}
    (hm : 0 < m) (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hlt : W (e.val.symm z) < threshold m) :
    (fun w => cutoff W m (e.val.symm w)) =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(continuousAt_chart_of_chartSmooth hW e hz).eventually (gt_mem_nhds hlt)]
    with w hw
  exact cutoff_eq_zero_of_lt hm hw

theorem contDiffAt_log_chart {W : M → ℝ} (hW : ChartSmooth (n := n) W) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (hpos : 0 < W (e.val.symm z)) :
    ContDiffAt ℝ ∞ (fun w => Real.log (W (e.val.symm w))) z :=
  ((hW e).contDiffAt (e.val.open_target.mem_nhds hz)).log hpos.ne'

/-- The cutoff is chart-smooth. -/
theorem chartSmooth_cutoff {W : M → ℝ} (hW : ChartSmooth (n := n) W) (hW0 : ∀ y, 0 ≤ W y)
    {m : ℝ} (hm : 0 < m) : ChartSmooth (n := n) (cutoff W m) := by
  intro e z hz
  refine ContDiffAt.contDiffWithinAt ?_
  rcases (hW0 (e.val.symm z)).lt_or_eq with hpos | hzero
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (cutoff_chart_eventuallyEq hW m e hz hpos)
    exact (contDiff_glue (k := ⊤)).contDiffAt.comp z
      (Real.contDiff_exp.contDiffAt.comp z
        (((contDiffAt_log_chart hW e hz hpos).div_const 2).div_const m))
  · refine ContDiffAt.congr_of_eventuallyEq contDiffAt_const
      (cutoff_chart_eventuallyEq_zero hW hm e hz ?_)
    rw [← hzero]; exact threshold_pos m

/-- **The Levi bound of the cutoff** at every point (CADG III.2.2 b)): if `L(log W) ≥ -C ω`
where `W > 0` and `W < 1`, then `L(χ_m) ≥ -(2C/m) ω`. -/
theorem neg_le_leviForm_cutoff (omega : PositiveClasses.KahlerBackground n M) {W : M → ℝ}
    (hW : ChartSmooth (n := n) W) (hW0 : ∀ y, 0 ≤ W y) (hW1 : ∀ y, W y < 1) {C : ℝ}
    (hC : 0 ≤ C)
    (hlevi : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        0 < W (e.val.symm z) → ∀ v : ComplexModel n,
          -(C * omega.form.val.coeff e z ![v, Complex.I • v]) ≤
            leviForm (fun w => Real.log (W (e.val.symm w))) z v)
    {m : ℝ} (hm : 0 < m) (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (v : ComplexModel n) :
    -(2 * C / m * omega.form.val.coeff e z ![v, Complex.I • v]) ≤
      leviForm (fun w => cutoff W m (e.val.symm w)) z v := by
  have hω : 0 ≤ omega.form.val.coeff e z ![v, Complex.I • v] :=
    KahlerDomination.lineValue_nonneg_of_isHermitian omega.isKahler.1 e hz v
  rcases (hW0 (e.val.symm z)).lt_or_eq with hpos | hzero
  · rw [leviForm_congr_of_eventuallyEq (cutoff_chart_eventuallyEq hW m e hz hpos)]
    set u : ComplexModel n → ℝ := fun w => Real.log (W (e.val.symm w)) / 2 with hu
    have hu2 : ContDiffAt ℝ 2 u z :=
      ((contDiffAt_log_chart hW e hz hpos).div_const 2).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hu0 : u z ≤ 0 := by
      have := Real.log_neg hpos (hW1 _)
      simp only [hu]; linarith
    have hLu : -(C * omega.form.val.coeff e z ![v, Complex.I • v] / 2) ≤ leviForm u z v := by
      have hfun : u = (1 / 2 : ℝ) • fun w => Real.log (W (e.val.symm w)) := by
        funext w; simp only [hu, Pi.smul_apply, smul_eq_mul]; ring
      have hlog2 : ContDiffAt ℝ 2 (fun w => Real.log (W (e.val.symm w))) z :=
        (contDiffAt_log_chart hW e hz hpos).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      rw [hfun, leviForm_smul hlog2]
      have := hlevi e z hz hpos v
      linarith
    have h := neg_le_leviForm_glue_exp hu2 hu0 hm
      (div_nonneg (mul_nonneg hC hω) zero_le_two) v hLu
    have e1 : 4 * (C * omega.form.val.coeff e z ![v, Complex.I • v] / 2) / m =
        2 * C / m * omega.form.val.coeff e z ![v, Complex.I • v] := by ring
    rw [e1] at h
    exact h
  · rw [leviForm_congr_of_eventuallyEq (cutoff_chart_eventuallyEq_zero hW hm e hz
      (by rw [← hzero]; exact threshold_pos m)), leviForm_const]
    have : 0 ≤ 2 * C / m * omega.form.val.coeff e z ![v, Complex.I • v] :=
      mul_nonneg (div_nonneg (mul_nonneg zero_le_two hC) hm.le) hω
    linarith

/-- **The cutoffs of the one-sided probe** (`ana:stokes-cutoffs`; CADG III.2.2 b), analytic case):
for a closed analytic subset `A` of a compact complex manifold with a Kähler form `ω`, there are
`C > 0` and chart-smooth `χ_m` with `0 ≤ χ_m ≤ 1`, `χ_m = 0` on an open neighbourhood of `A`,
`χ_m → 1` pointwise off `A`, and `ddᶜ χ_m + (C / (m + 1)) ω ≥ 0`. -/
theorem exists_stokesCutoffs [CompactSpace M] (omega : PositiveClasses.KahlerBackground n M)
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hAc : IsClosed A) :
    ∃ (C : ℝ) (χ : ℕ → M → ℝ) (hχ : ∀ m, ChartSmooth (n := n) (χ m)), 0 < C ∧
      (∀ m y, 0 ≤ χ m y ∧ χ m y ≤ 1) ∧
      (∀ m, ∃ U : Set M, IsOpen U ∧ A ⊆ U ∧ ∀ y ∈ U, χ m y = 0) ∧
      (∀ y, y ∉ A → Tendsto (fun m => χ m y) atTop (𝓝 1)) ∧
      ∀ m, (ddcClosedForm (χ m) (hχ m) + (C / ((m : ℝ) + 1)) • omega.form).val.IsSemipositive := by
  obtain ⟨W, C, hC, hW, hWc, hW0, hW1, hWA, hlevi⟩ := exists_polePotential omega hA hAc
  have hm : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  refine ⟨2 * C / Real.pi, fun m => cutoff W ((m : ℝ) + 1),
    fun m => chartSmooth_cutoff hW hW0 (hm m), div_pos (mul_pos two_pos hC) Real.pi_pos,
    fun m y => ⟨cutoff_nonneg W _ y, cutoff_le_one hW1 (hm m) y⟩, fun m => ?_,
    fun y hy => tendsto_cutoff (lt_of_le_of_ne (hW0 y) (fun h => hy ((hWA y).1 h.symm))),
    fun m => ?_⟩
  · refine ⟨{y | W y < threshold ((m : ℝ) + 1)}, isOpen_lt hWc continuous_const,
      fun y hy => ?_, fun y hy => cutoff_eq_zero_of_lt (hm m) hy⟩
    show W y < threshold ((m : ℝ) + 1)
    rw [(hWA y).2 hy]
    exact threshold_pos _
  · intro e z hz v
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have h1 := quad_ddcClosedForm_coeff (chartSmooth_cutoff hW hW0 (hm m)) e hz v
    simp only [PositivityPerturbation.quad] at h1
    rw [h1]
    have h2 := neg_le_leviForm_cutoff omega hW hW0 hW1 hC.le hlevi (hm m) e hz v
    have hpi := Real.pi_pos
    have key : leviForm (fun w => cutoff W ((m : ℝ) + 1) (e.val.symm w)) z v / Real.pi +
        2 * C / Real.pi / ((m : ℝ) + 1) * omega.form.val.coeff e z ![v, Complex.I • v] =
        (leviForm (fun w => cutoff W ((m : ℝ) + 1) (e.val.symm w)) z v +
          2 * C / ((m : ℝ) + 1) * omega.form.val.coeff e z ![v, Complex.I • v]) / Real.pi := by
      field_simp
    rw [key]
    exact div_nonneg (by linarith) hpi.le

end

end Hironaka.StokesPolePotential
