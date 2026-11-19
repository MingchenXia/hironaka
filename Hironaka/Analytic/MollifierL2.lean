import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

/-!
# Mollifiers in `L²` and weak derivatives

For a normalized smooth bump `ρ` on a finite-dimensional real normed space (in particular
a finite-dimensional real inner product space):
* convolution with `ρ` is a contraction of `L²`;
* `ρ_k ⋆ f → f` in `L²` when the radii of `ρ_k` tend to zero;
* a weak first-order linear relation `∑ cᵢ ∂_{wᵢ} fᵢ = ζ` on an open set passes to the
  mollifications at every point whose `rOut`-ball lies in the open set.
-/

noncomputable section

open Set Function Filter Metric MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology ENNReal Pointwise

namespace Hironaka

/-- Jensen/Cauchy–Schwarz for a probability density in `ℝ≥0∞`. -/
theorem lintegral_mul_sq_le_of_lintegral_eq_one {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {w a : α → ℝ≥0∞} (hw : Measurable w) (hw1 : ∫⁻ t, w t ∂ν = 1)
    (ha : Measurable a) :
    (∫⁻ t, w t * a t ∂ν) ^ 2 ≤ ∫⁻ t, w t * a t ^ 2 ∂ν := by
  set ν' := ν.withDensity w
  have : IsProbabilityMeasure ν' := ⟨by simp [ν', withDensity_apply, hw1]⟩
  have h1 : ∫⁻ t, w t * a t ∂ν = ∫⁻ t, a t ∂ν' :=
    (lintegral_withDensity_eq_lintegral_mul ν hw ha).symm
  have h2 : ∫⁻ t, w t * a t ^ 2 ∂ν = ∫⁻ t, a t ^ 2 ∂ν' :=
    (lintegral_withDensity_eq_lintegral_mul ν hw (ha.pow_const 2)).symm
  rw [h1, h2]
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq ν' Real.HolderConjugate.two_two ha.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, measure_univ,
    ENNReal.rpow_two, one_pow, ENNReal.one_rpow] at this
  calc _ ≤ ((∫⁻ t, a t ^ 2 ∂ν') ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] in
theorem measurable_ofReal_bump_normed (ρ : ContDiffBump (0 : E)) :
    Measurable fun t ↦ ENNReal.ofReal (ρ.normed μ t) :=
  ENNReal.measurable_ofReal.comp ρ.continuous_normed.measurable

theorem lintegral_ofReal_bump_normed (ρ : ContDiffBump (0 : E)) :
    ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) ∂μ = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal ρ.integrable_normed
    (Eventually.of_forall ρ.nonneg_normed), ρ.integral_normed, ENNReal.ofReal_one]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Pointwise triangle inequality for a mollification. -/
theorem enorm_bump_convolution_le (ρ : ContDiffBump (0 : E)) (f : E → ℂ) (x : E) :
    ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ‖f (x - t)‖ₑ ∂μ := by
  rw [convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  ext t
  simp only [lsmul_apply, enorm_smul, Real.enorm_of_nonneg (ρ.nonneg_normed t)]

/-- Pointwise Cauchy–Schwarz bound for a mollification. -/
theorem enorm_bump_convolution_sq_le (ρ : ContDiffBump (0 : E)) {f : E → ℂ}
    (hf : StronglyMeasurable f) (x : E) :
    ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ‖f (x - t)‖ₑ ^ 2 ∂μ := by
  have ha : Measurable fun t ↦ ‖f (x - t)‖ₑ :=
    (hf.measurable.comp (measurable_const.sub measurable_id)).enorm
  refine le_trans ?_ (lintegral_mul_sq_le_of_lintegral_eq_one
    (measurable_ofReal_bump_normed ρ) (lintegral_ofReal_bump_normed ρ) ha)
  gcongr
  exact enorm_bump_convolution_le ρ f x

/-- Convolution with a normalized bump is a contraction for the `L¹` seminorm. -/
theorem lintegral_enorm_bump_convolution_le (ρ : ContDiffBump (0 : E)) {f : E → ℂ}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have hcongr : ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f = ρ.normed μ ⋆[lsmul ℝ ℝ, μ] hf.mk f :=
    convolution_congr _ (EventuallyEq.refl _ _) hf.ae_eq_mk
  rw [hcongr]
  set g := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have hw := measurable_ofReal_bump_normed (μ := μ) ρ
  calc _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ‖g (x - t)‖ₑ ∂μ ∂μ :=
        lintegral_mono fun x ↦ enorm_bump_convolution_le ρ g x
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ.normed μ t) * ‖g (x - t)‖ₑ ∂μ ∂μ :=
        lintegral_lintegral_swap (((hw.comp measurable_snd).mul
          (hg.measurable.comp (measurable_fst.sub measurable_snd)).enorm).aemeasurable)
    _ = ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ∫⁻ x, ‖g x‖ₑ ∂μ ∂μ := by
        congr 1
        ext t
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun x ↦ ‖g x‖ₑ) t]
    _ = ∫⁻ x, ‖g x‖ₑ ∂μ := by
        rw [lintegral_mul_const _ hw, lintegral_ofReal_bump_normed, one_mul]
    _ = _ := lintegral_congr_ae (hf.ae_eq_mk.mono fun x hx ↦ by rw [hx])

/-- Convolution with a normalized bump is a contraction for the `L²` seminorm. -/
theorem eLpNorm_bump_convolution_le (ρ : ContDiffBump (0 : E)) {f : E → ℂ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) 2 μ ≤ eLpNorm f 2 μ := by
  have hcongr : ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f = ρ.normed μ ⋆[lsmul ℝ ℝ, μ] hf.mk f :=
    convolution_congr _ (EventuallyEq.refl _ _) hf.ae_eq_mk
  rw [hcongr, eLpNorm_congr_ae hf.ae_eq_mk]
  set g := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have hw := measurable_ofReal_bump_normed (μ := μ) ρ
  have key : ∫⁻ x, ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
    simp only [ENNReal.rpow_two]
    calc _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ‖g (x - t)‖ₑ ^ 2 ∂μ ∂μ :=
          lintegral_mono fun x ↦ enorm_bump_convolution_sq_le ρ hg x
      _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ.normed μ t) * ‖g (x - t)‖ₑ ^ 2 ∂μ ∂μ :=
          lintegral_lintegral_swap (((hw.comp measurable_snd).mul
            ((hg.measurable.comp (measurable_fst.sub measurable_snd)).enorm.pow_const 2)).aemeasurable)
      _ = ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ∂μ := by
          congr 1
          ext t
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_right_eq_self (fun x ↦ ‖g x‖ₑ ^ 2) t]
      _ = _ := by rw [lintegral_mul_const _ hw, lintegral_ofReal_bump_normed, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  gcongr

/-- Mollification of a locally integrable function is smooth. -/
theorem contDiff_bump_convolution (ρ : ContDiffBump (0 : E)) {f : E → ℂ}
    (hf : LocallyIntegrable f μ) : ContDiff ℝ ∞ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed hf

/-- Mollification of an `L²` function is in `L²`. -/
theorem memLp_bump_convolution (ρ : ContDiffBump (0 : E)) {f : E → ℂ} (hf : MemLp f 2 μ) :
    MemLp (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) 2 μ :=
  ⟨(contDiff_bump_convolution ρ (hf.locallyIntegrable one_le_two)).continuous.aestronglyMeasurable,
    (eLpNorm_bump_convolution_le ρ hf.1).trans_lt hf.2⟩

/-- Support of a mollification. -/
theorem tsupport_bump_convolution_subset (ρ : ContDiffBump (0 : E))
    (f : E → ℂ) :
    tsupport (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) ⊆ tsupport f + closedBall 0 ρ.rOut := by
  refine closure_minimal ((support_convolution_subset_swap (lsmul ℝ ℝ)).trans ?_)
    ((isClosed_tsupport f).add_right_of_isCompact (isCompact_closedBall 0 _))
  rw [ρ.support_normed_eq]
  exact Set.add_subset_add (subset_tsupport f) ball_subset_closedBall

/-- Mollification is additive on differences of locally integrable functions. -/
theorem bump_convolution_sub (ρ : ContDiffBump (0 : E)) {f g : E → ℂ}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f - g)) x =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x - (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x := by
  have h1 := (ρ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
    (ρ.continuous_normed (μ := μ)) hf x).integrable
  have h2 := (ρ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
    (ρ.continuous_normed (μ := μ)) hg x).integrable
  simp only [convolution_def, Pi.sub_apply, map_sub]
  exact integral_sub h1 h2

/-- For a continuous compactly supported function, mollifications converge in `L²`. -/
theorem tendsto_eLpNorm_bump_convolution_sub_of_continuous {g : E → ℂ}
    (hgc : HasCompactSupport g) (hg : Continuous g) {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) x - g x) 2 μ)
      atTop (𝓝 0) := by
  set K := tsupport g + closedBall (0 : E) 1 with hK
  have hKc : IsCompact K := hgc.isCompact.add (isCompact_closedBall 0 1)
  have hKμ : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hlim : Tendsto (fun η : ℝ ↦ ENNReal.ofReal η * μ K ^ (1 / (2 : ℝ≥0∞).toReal))
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ ↦ ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.tendsto_ofReal (tendsto_id : Tendsto (fun η : ℝ ↦ η) (𝓝 0) (𝓝 0))).mono_left
        nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const this
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKμ))
  have huc := hgc.uniformContinuous_of_continuous hg
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hηε, hη⟩ :=
    ((ENNReal.tendsto_nhds_zero.1 hlim ε hε).and self_mem_nhdsWithin).exists
  have hη : (0 : ℝ) < η := hη
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 huc η hη
  filter_upwards [hφ.eventually (eventually_lt_nhds (lt_min hδ one_pos))] with k hk
  refine le_trans ?_ hηε
  refine eLpNorm_sub_le_of_dist_bdd μ ENNReal.ofNat_ne_top hKc.isClosed.measurableSet hη.le
    (f := (φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) (g := g) ?_ ?_ ?_
  · intro x
    exact (φ k).dist_normed_convolution_le hg.aestronglyMeasurable fun y hy ↦
      (hδg ((mem_ball.1 hy).trans (hk.trans_le (min_le_left _ _)))).le
  · exact (subset_tsupport _).trans ((tsupport_bump_convolution_subset _ _).trans
      (Set.add_subset_add_left (closedBall_subset_closedBall (hk.le.trans (min_le_right _ _)))))
  · exact (subset_tsupport g).trans (Set.subset_add_left _ (mem_closedBall_self zero_le_one))

/-- **`L²` convergence of mollifiers.** If the radii of the normalized bumps `φ k` tend to
zero, then `φ k ⋆ f → f` in `L²` for every `f ∈ L²`. -/
theorem tendsto_eLpNorm_bump_convolution_sub {f : E → ℂ} (hf : MemLp f 2 μ)
    {φ : ℕ → ContDiffBump (0 : E)} (hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] f) x - f x) 2 μ)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have h3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 h3
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  obtain ⟨g, hgc, hgs, hfg⟩ := hf.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two hδ
  have hg2 : MemLp g 2 μ := hgs.continuous.memLp_of_hasCompactSupport hgc
  have hfl := hf.locallyIntegrable one_le_two
  have hgl := hg2.locallyIntegrable one_le_two
  filter_upwards [ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_bump_convolution_sub_of_continuous (μ := μ) hgc hgs.continuous hφ)
    (ε / 3) h3] with k hk
  have hdecomp : (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] f) x - f x) =
      ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] (f - g)) +
        ((fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) x - g x) + (g - f)) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, bump_convolution_sub (φ k) hfl hgl x]
    ring
  have hm1 : AEStronglyMeasurable ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] (f - g)) μ :=
    (contDiff_bump_convolution (φ k) (hfl.sub hgl)).continuous.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) x - g x) μ :=
    ((contDiff_bump_convolution (φ k) hgl).continuous.sub hgs.continuous).aestronglyMeasurable
  rw [hdecomp]
  calc _ ≤ eLpNorm ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] (f - g)) 2 μ +
        (eLpNorm (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) x - g x) 2 μ +
          eLpNorm (g - f) 2 μ) := by
        refine (eLpNorm_add_le hm1 (hm2.add (hg2.1.sub hf.1)) one_le_two).trans ?_
        gcongr
        exact eLpNorm_add_le hm2 (hg2.1.sub hf.1) one_le_two
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        · exact (eLpNorm_bump_convolution_le _ (hf.1.sub hg2.1)).trans
            (hfg.trans hδε.le)
        · rw [eLpNorm_sub_comm]
          exact hfg.trans hδε.le
    _ = ε := by rw [← add_assoc, ENNReal.add_thirds]

/-- A mollification written as an integral against the reflected, translated bump. -/
theorem bump_convolution_apply_eq_integral (ρ : ContDiffBump (0 : E)) (f : E → ℂ) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x = ∫ y, (ρ.normed μ (x - y) : ℂ) * f y ∂μ := by
  rw [convolution_eq_swap]
  simp only [lsmul_apply, Complex.real_smul]

/-- Directional derivative of a mollification: the derivative falls on the bump. -/
theorem fderiv_bump_convolution_apply (ρ : ContDiffBump (0 : E)) {f : E → ℂ}
    (hf : LocallyIntegrable f μ) (x w : E) :
    fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x w =
      ∫ y, (fderiv ℝ (ρ.normed μ) (x - y) w : ℂ) * f y ∂μ := by
  have hc1 : ContDiff ℝ 1 (ρ.normed μ) := ρ.contDiff_normed
  rw [(ρ.hasCompactSupport_normed.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hc1 hf x).fderiv,
    convolution_eq_swap]
  have hex := (ρ.hasCompactSupport_normed.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL E) (hc1.continuous_fderiv one_ne_zero) hf x
  rw [ContinuousLinearMap.integral_apply hex.integrable_swap]
  simp [Complex.real_smul]

set_option linter.unusedVariables false in
/-- **Weak derivatives commute with mollification, locally.** If
`∑ cᵢ ∂_{wᵢ} fᵢ = ζ` weakly on `U`, then the same identity holds pointwise for the
mollifications at every `x` whose closed `rOut`-ball lies in `U`.  (The openness of `U` and
the local integrability of `ζ` are not needed by the proof.) -/
theorem sum_fderiv_bump_convolution_eq_of_weak {ι : Type*} [Fintype ι] {U : Set E}
    (hU : IsOpen U) {f : ι → E → ℂ} (hf : ∀ i, LocallyIntegrable (f i) μ) {ζ : E → ℂ}
    (hζ : LocallyIntegrable ζ μ) (c : ι → ℂ) (w : ι → E)
    (hweak : ∀ g : E → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∑ i, c i * ∫ x, f i x * fderiv ℝ g x (w i) ∂μ = -∫ x, ζ x * g x ∂μ)
    (ρ : ContDiffBump (0 : E)) {x : E} (hx : closedBall x ρ.rOut ⊆ U) :
    ∑ i, c i * fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f i) x (w i) =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ζ) x := by
  set g : E → ℂ := fun y ↦ (ρ.normed μ (x - y) : ℂ) with hg_def
  have hg_supp : support g ⊆ closedBall x ρ.rOut := by
    intro y hy
    have : x - y ∈ support (ρ.normed μ) := fun h ↦ hy (by simp [g, h])
    rw [ρ.support_normed_eq, mem_ball_zero_iff, ← dist_eq_norm] at this
    rw [mem_closedBall, dist_comm]
    exact this.le
  have hg_tsupp : tsupport g ⊆ closedBall x ρ.rOut :=
    closure_minimal hg_supp isClosed_closedBall
  have hg_cs : HasCompactSupport g :=
    (isCompact_closedBall x ρ.rOut).of_isClosed_subset (isClosed_tsupport g) hg_tsupp
  have hsmooth : ContDiff ℝ ∞ (ρ.normed μ) := ρ.contDiff_normed
  have hg_smooth : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp (hsmooth.comp (contDiff_const.sub contDiff_id))
  have hg_deriv : ∀ y v, fderiv ℝ g y v = -(fderiv ℝ (ρ.normed μ) (x - y) v : ℂ) := by
    intro y v
    have h1 : HasFDerivAt (fun y : E ↦ x - y) (-ContinuousLinearMap.id ℝ E) y := by
      simpa using (hasFDerivAt_id y).const_sub x
    have h2 := ((hsmooth.differentiable (by simp)).differentiableAt (x := x - y)).hasFDerivAt
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y (h2.comp y h1)
    have h4 : fderiv ℝ g y = _ := h3.fderiv
    rw [h4]
    simp
  have key := hweak g hg_smooth hg_cs (hg_tsupp.trans hx)
  simp only [hg_deriv, mul_neg, integral_neg, mul_neg, Finset.sum_neg_distrib, neg_inj] at key
  rw [bump_convolution_apply_eq_integral,
    show (∫ y, (ρ.normed μ (x - y) : ℂ) * ζ y ∂μ) = ∫ y, ζ y * g y ∂μ from
      integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _), ← key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_bump_convolution_apply ρ (hf i)]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)

end Hironaka
