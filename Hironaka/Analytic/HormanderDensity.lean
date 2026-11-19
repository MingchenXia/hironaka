import Hironaka.Analytic.HormanderAPriori
import Hironaka.Analytic.MollifierL2

set_option autoImplicit false

/-!
# Density of test forms for Hörmander's three weights

Let `D ⊆ ℂⁿ` be open, `w₃, ψ₀` smooth on `D`, `w₂ = w₃ - ψ₀`, `w₁ = w₃ - 2ψ₀`, and let
`η k` be cutoffs, compactly supported in `D`, eventually `1` near each point of `D`, with
`‖Dη_k‖² ≤ e^{ψ₀}`.  If a `(0,1)`-form `β ∈ L²(e^{-w₂})` has weak `T* β = γ ∈ L²(e^{-w₁})` and
weak `∂̄ β = σ ∈ L²(e^{-w₃})`, then there are test forms `βs m` with `βs m → β`,
`T* βs m → γ` and `∂̄ βs m → σ` in the respective weighted `L²` spaces.

This is Hörmander, *An introduction to complex analysis in several variables*, Lemma 4.1.3.
The proof cuts off with `η k` (the gradient bound controls the commutator terms) and then
mollifies the compactly supported forms `e^{-w₂} η_k β` (the weak equations pass to the
mollifications), followed by a diagonal argument.
-/

open MeasureTheory Set Filter Complex Metric
open scoped ComplexConjugate ContDiff Topology ENNReal Convolution Pointwise

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ}

namespace Density

/-! ### Weighted `L²` on compact subsets -/

section Weighted

variable {D : Set (ComplexModel n)} {w : ComplexModel n → ℝ}

theorem exists_forall_exp_neg_le {K : Set (ComplexModel n)} (hK : IsCompact K) {f : ComplexModel n → ℝ}
    (hf : ContinuousOn f K) : ∃ M : ℝ, ∀ x ∈ K, Real.exp (f x) ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf
  exact ⟨Real.exp M, fun x hx ↦ Real.exp_le_exp.mpr ((Real.le_norm_self _).trans (hM x hx))⟩

/-- On a compact subset of `D`, the weighted volume is dominated by a multiple of Lebesgue
measure. -/
theorem exists_weightedVolume_restrict_le (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (weightedVolume D w).restrict K ≤ C • volume.restrict K := by
  obtain ⟨M, hM⟩ := exists_forall_exp_neg_le hK ((hw.mono hKD).neg)
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  rw [Measure.restrict_apply hs, weightedVolume_eq_withDensity_weightDensity hD,
    withDensity_apply _ (hs.inter hK.isClosed.measurableSet), Measure.smul_apply,
    Measure.restrict_apply hs, smul_eq_mul]
  calc ∫⁻ x in s ∩ K, weightDensity D w x ∂volume.restrict D
      ≤ ∫⁻ _ in s ∩ K, ENNReal.ofReal M ∂volume.restrict D := by
        refine setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun x hx ↦ ?_)
        unfold weightDensity
        by_cases hxD : x ∈ D
        · simp only [hxD, Set.indicator_of_mem]
          exact ENNReal.ofReal_le_ofReal (hM x hx.2)
        · simp [hxD]
    _ = ENNReal.ofReal M * (volume.restrict D) (s ∩ K) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal M * volume (s ∩ K) := by
        gcongr; exact Measure.restrict_le_self

/-- On a compact subset of `D`, Lebesgue measure is dominated by a multiple of the weighted
volume. -/
theorem exists_volume_restrict_le (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ volume.restrict K ≤ C • weightedVolume D w := by
  obtain ⟨M, hM⟩ := exists_forall_exp_neg_le hK (hw.mono hKD)
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  rw [Measure.restrict_apply hs, weightedVolume_eq_withDensity_weightDensity hD,
    Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]
  have hsK : MeasurableSet (s ∩ K) := hs.inter hK.isClosed.measurableSet
  calc volume (s ∩ K) = ∫⁻ x in s ∩ K, ENNReal.ofReal (Real.exp (w x)) *
        weightDensity D w x ∂volume := by
        rw [← setLIntegral_one]
        refine setLIntegral_congr_fun hsK fun x hx ↦ ?_
        simp only [weightDensity, hKD hx.2, Set.indicator_of_mem]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp
    _ ≤ ∫⁻ x in s ∩ K, ENNReal.ofReal M * weightDensity D w x ∂volume := by
        refine setLIntegral_mono_ae ((measurable_weightDensity hD hw).const_mul _).aemeasurable
          (Eventually.of_forall fun x hx ↦ ?_)
        gcongr
        exact hM x hx.2
    _ = ENNReal.ofReal M * ∫⁻ x in s ∩ K, weightDensity D w x ∂volume := by
        rw [lintegral_const_mul]
        exact measurable_weightDensity hD hw
    _ ≤ ENNReal.ofReal M * ∫⁻ x in s, weightDensity D w x ∂volume.restrict D := by
        rw [Measure.restrict_restrict hs]
        gcongr ?_ * ?_
        · exact le_rfl
        · exact lintegral_mono_set (fun x (hx : x ∈ s ∩ K) ↦ (⟨hx.1, hKD hx.2⟩ : x ∈ s ∩ D))

theorem absolutelyContinuous_weightedVolume (hD : IsOpen D) (hw : ContinuousOn w D) :
    volume.restrict D ≪ weightedVolume D w := by
  rw [weightedVolume_eq_withDensity_weightDensity hD]
  refine withDensity_absolutelyContinuous' (measurable_weightDensity hD hw).aemeasurable ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  simp [weightDensity, hx, Real.exp_pos]

theorem aestronglyMeasurable_weightedVolume_iff {V : Type*} [TopologicalSpace V]
    (hD : IsOpen D) (hw : ContinuousOn w D) {f : ComplexModel n → V} :
    AEStronglyMeasurable f (weightedVolume D w) ↔ AEStronglyMeasurable f (volume.restrict D) :=
  ⟨fun h ↦ h.mono_ac (absolutelyContinuous_weightedVolume hD hw),
    fun h ↦ h.mono_ac (withDensity_absolutelyContinuous _ _)⟩

theorem memLp_restrict_of_weightedVolume (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {f : ComplexModel n → ℂ}
    (hf : MemLp f 2 (weightedVolume D w)) : MemLp f 2 (volume.restrict K) := by
  obtain ⟨C, hC, hle⟩ := exists_volume_restrict_le hD hw hK hKD
  exact (hf.smul_measure hC).mono_measure hle

/-- A weighted `L²` function times a bounded function supported in a compact `K ⊆ D` is in
unweighted `L²`. -/
theorem memLp_mul_of_weightedVolume (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {u v : ComplexModel n → ℂ}
    (hu : MemLp u 2 (weightedVolume D w)) (hv : ContinuousOn v K) (hv0 : ∀ x ∉ K, v x = 0) :
    MemLp (fun x ↦ v x * u x) 2 volume := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hv
  have hu' := memLp_restrict_of_weightedVolume hD hw hK hKD hu
  have h1 : MemLp (fun x ↦ v x * u x) 2 (volume.restrict K) := by
    refine hu'.of_le_mul (c := M) ((hv.aestronglyMeasurable hKm).mul hu'.1) ?_
    filter_upwards [ae_restrict_mem hKm] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)
  rw [← memLp_indicator_iff_restrict hKm] at h1
  have he : (K.indicator fun x ↦ v x * u x) = fun x ↦ v x * u x := by
    funext x
    by_cases hx : x ∈ K <;> simp [hx, hv0]
  rwa [he] at h1

theorem integrable_of_memLp_two_of_eq_zero_off {V : Type*} [NormedAddCommGroup V]
    {K : Set (ComplexModel n)} (hK : IsCompact K) {f : ComplexModel n → V}
    (hf : MemLp f 2 volume) (h0 : ∀ x ∉ K, f x = 0) : Integrable f := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have h := (hf.restrict K).integrable one_le_two
  exact (integrableOn_iff_integrable_of_support_subset
    (fun x hx ↦ by_contra fun h' ↦ hx (h0 x h'))).mp h

theorem integrable_mul_of_weightedVolume (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {u v : ComplexModel n → ℂ}
    (hu : MemLp u 2 (weightedVolume D w)) (hv : ContinuousOn v K) (hv0 : ∀ x ∉ K, v x = 0) :
    Integrable (fun x ↦ v x * u x) :=
  integrable_of_memLp_two_of_eq_zero_off hK (memLp_mul_of_weightedVolume hD hw hK hKD hu hv hv0)
    fun x hx ↦ by simp [hv0 x hx]

theorem exists_eLpNorm_weightedVolume_le (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ComplexModel n → ℂ, (∀ x ∉ K, f x = 0) →
      eLpNorm f 2 (weightedVolume D w) ≤ C * eLpNorm f 2 (volume.restrict K) := by
  obtain ⟨C, hC, hle⟩ := exists_weightedVolume_restrict_le hD hw hK hKD
  refine ⟨C ^ (1 / (2 : ℝ≥0∞)).toReal, ENNReal.rpow_ne_top_of_nonneg (by positivity) hC,
    fun f hf ↦ ?_⟩
  have hs : Function.support f ⊆ K := fun x hx ↦ by_contra fun h ↦ hx (hf x h)
  rw [← eLpNorm_restrict_eq_of_support_subset hs]
  calc _ ≤ eLpNorm f 2 (C • volume.restrict K) := eLpNorm_mono_measure f hle
    _ = _ := by rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul]

/-- Convergence in weighted `L²` from a pointwise bound on a compact `K ⊆ D` by functions
converging in unweighted `L²`. -/
theorem tendsto_eLpNorm_weightedVolume_of_le {V : Type*} [NormedAddCommGroup V]
    (hD : IsOpen D) (hw : ContinuousOn w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {f : ℕ → ComplexModel n → ℂ}
    {g : ℕ → ComplexModel n → V} {C : ℝ} (hf0 : ∀ m, ∀ x ∉ K, f m x = 0)
    (hfg : ∀ m, ∀ x ∈ K, ‖f m x‖ ≤ C * ‖g m x‖)
    (hg : Tendsto (fun m ↦ eLpNorm (g m) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun m ↦ eLpNorm (f m) 2 (weightedVolume D w)) atTop (𝓝 0) := by
  obtain ⟨C', hC', hle⟩ := exists_eLpNorm_weightedVolume_le hD hw hK hKD
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hb : ∀ m, eLpNorm (f m) 2 (weightedVolume D w) ≤
      C' * ENNReal.ofReal C * eLpNorm (g m) 2 volume := fun m ↦ by
    refine (hle _ (hf0 m)).trans ?_
    rw [mul_assoc]
    gcongr
    have h1 : eLpNorm (f m) 2 (volume.restrict K) ≤
        ENNReal.ofReal C * eLpNorm (g m) 2 (volume.restrict K) := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
      filter_upwards [ae_restrict_mem hKm] with x hx using hfg m x hx
    refine h1.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hlim : Tendsto (fun m ↦ C' * ENNReal.ofReal C * eLpNorm (g m) 2 volume) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hg (Or.inr (ENNReal.mul_ne_top hC' ENNReal.ofReal_ne_top))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le) hb

theorem enorm_rpow_two_eq {V : Type*} [NormedAddCommGroup V] (z : V) :
    ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem eLpNorm_weightedVolume_eq (hD : IsOpen D) (hw : ContinuousOn w D)
    (f : ComplexModel n → ℂ) :
    eLpNorm f 2 (weightedVolume D w) =
      (∫⁻ x in D, ENNReal.ofReal (Real.exp (-w x) * ‖f x‖ ^ 2)) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    lintegral_weightedVolume hD hw]
  simp only [ENNReal.toReal_ofNat, enorm_rpow_two_eq]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **Dominated convergence in weighted `L²`.** -/
theorem tendsto_eLpNorm_mul_weightedVolume (hD : IsOpen D) {w' : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) (hw' : ContinuousOn w' D) {β : ComplexModel n → ℂ}
    (hβ : MemLp β 2 (weightedVolume D w')) {c : ℕ → ComplexModel n → ℂ}
    (hc : ∀ k, AEStronglyMeasurable (c k) (volume.restrict D))
    (hcb : ∀ k, ∀ x ∈ D, ‖c k x‖ ^ 2 ≤ Real.exp (w x - w' x))
    (hc0 : ∀ x ∈ D, Tendsto (fun k ↦ c k x) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ c k x * β x) 2 (weightedVolume D w)) atTop (𝓝 0) := by
  simp_rw [eLpNorm_weightedVolume_eq hD hw]
  have hDm := hD.measurableSet
  have hβm : AEStronglyMeasurable β (volume.restrict D) :=
    (aestronglyMeasurable_weightedVolume_iff hD hw').mp hβ.1
  have hfin : ∫⁻ x in D, ENNReal.ofReal (Real.exp (-w' x) * ‖β x‖ ^ 2) ≠ ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hβ.2
    rw [lintegral_weightedVolume hD hw'] at h
    simp only [ENNReal.toReal_ofNat, enorm_rpow_two_eq] at h
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun x ↦ ?_)) h)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hlim : Tendsto (fun k ↦ ∫⁻ x in D, ENNReal.ofReal (Real.exp (-w x) * ‖c k x * β x‖ ^ 2))
      atTop (𝓝 (∫⁻ _ in D, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_of_dominated_convergence' _ (fun k ↦ ?_) (fun k ↦ ?_) hfin ?_
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      have he : AEStronglyMeasurable (fun x ↦ Real.exp (-w x)) (volume.restrict D) :=
        (Real.continuous_exp.comp_continuousOn hw.neg).aestronglyMeasurable hDm
      exact (he.mul (((hc k).mul hβm).norm.pow 2)).aemeasurable
    · filter_upwards [ae_restrict_mem hDm] with x hx
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, mul_pow]
      calc Real.exp (-w x) * (‖c k x‖ ^ 2 * ‖β x‖ ^ 2)
          ≤ Real.exp (-w x) * (Real.exp (w x - w' x) * ‖β x‖ ^ 2) := by
            gcongr; exact hcb k x hx
        _ = Real.exp (-w' x) * ‖β x‖ ^ 2 := by
            rw [← mul_assoc, ← Real.exp_add]; ring_nf
    · filter_upwards [ae_restrict_mem hDm] with x hx
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have h1 : Tendsto (fun k ↦ ‖c k x * β x‖) atTop (𝓝 0) := by
        simpa using ((hc0 x hx).mul_const (β x)).norm
      simpa using (h1.pow 2).const_mul (Real.exp (-w x))
  rw [lintegral_zero] at hlim
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem tendsto_eLpNorm_add {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    {μ : Measure α} {f g : ℕ → α → V} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hf0 : Tendsto (fun k ↦ eLpNorm (f k) 2 μ) atTop (𝓝 0))
    (hg0 : Tendsto (fun k ↦ eLpNorm (g k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ f k x + g k x) 2 μ) atTop (𝓝 0) := by
  have h := hf0.add hg0
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    fun k ↦ eLpNorm_add_le (hf k) (hg k) one_le_two

theorem tendsto_eLpNorm_sub {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    {μ : Measure α} {f g : ℕ → α → V} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hf0 : Tendsto (fun k ↦ eLpNorm (f k) 2 μ) atTop (𝓝 0))
    (hg0 : Tendsto (fun k ↦ eLpNorm (g k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ f k x - g k x) 2 μ) atTop (𝓝 0) := by
  have h := hf0.add hg0
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    fun k ↦ eLpNorm_sub_le (hf k) (hg k) one_le_two

theorem tendsto_eLpNorm_sum {α ι V : Type*} [MeasurableSpace α] [Fintype ι]
    [NormedAddCommGroup V] {μ : Measure α} {f : ℕ → ι → α → V} (hf : ∀ k i, AEStronglyMeasurable (f k i) μ)
    (hf0 : ∀ i, Tendsto (fun k ↦ eLpNorm (f k i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ ∑ i, f k i x) 2 μ) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ ↦ hf0 i
  rw [Finset.sum_const_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    fun k ↦ ?_
  have e : (fun x ↦ ∑ i, f k i x) = ∑ i, f k i := by
    funext x; simp [Finset.sum_apply]
  rw [e]
  exact eLpNorm_sum_le (fun i _ ↦ hf k i) one_le_two

end Weighted

/-! ### Test functions -/

section Test

variable {D : Set (ComplexModel n)}

theorem isTestFunctionOn_contDiff_one {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    ContDiff ℝ 1 g :=
  hg.1.of_le (by norm_cast)

theorem isTestFunctionOn_ofReal_mul {θ : ComplexModel n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    IsTestFunctionOn D (fun x ↦ (θ x : ℂ) * g x) :=
  ⟨(contDiff_ofReal_comp hθ).mul hg.1, hg.2.1.mul_left, tsupport_mul_subset_right.trans hg.2.2⟩

theorem isTestFunctionOn_conj {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    IsTestFunctionOn D (fun x ↦ conj (g x)) :=
  ⟨Complex.conjCLE.contDiff.comp hg.1, hg.2.1.comp_left (map_zero _),
    (tsupport_comp_subset (map_zero _) _).trans hg.2.2⟩

theorem continuous_dDir_of_contDiff {v : ComplexModel n} {f : ComplexModel n → ℂ}
    (hf : ContDiff ℝ 1 f) : Continuous (dDir v f) :=
  (contDiff_dDir (k := 0) (by simpa using hf)).continuous

theorem dDir_ofReal_eq_conj_dbarDir {v : ComplexModel n} {θ : ComplexModel n → ℝ}
    {x : ComplexModel n} (hθ : DifferentiableAt ℝ θ x) :
    dDir v (fun y ↦ (θ y : ℂ)) x = conj (dbarDir v (fun y ↦ (θ y : ℂ)) x) := by
  have h := dDir_conj (v := v) (differentiableAt_ofReal_comp hθ)
  simpa only [Complex.conj_ofReal] using h

theorem dbarDir_eq_zero_of_notMem_tsupport_real {θ : ComplexModel n → ℝ} {x v : ComplexModel n}
    (hx : x ∉ tsupport θ) : dbarDir v (fun y ↦ (θ y : ℂ)) x = 0 := by
  refine dbarDir_eq_zero_of_notMem_tsupport fun h ↦ hx ?_
  exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero θ) h

theorem dDir_eq_zero_of_notMem_tsupport_real {θ : ComplexModel n → ℝ} {x v : ComplexModel n}
    (hx : x ∉ tsupport θ) : dDir v (fun y ↦ (θ y : ℂ)) x = 0 := by
  have h : (fun y ↦ (θ y : ℂ)) =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]
  simp [dDir, h.fderiv_eq]

end Test

/-! ### Step 1: cutting off -/

section Cutoff

variable {D : Set (ComplexModel n)}

/-- The weak `T*` of the cut-off form `θ β`: `θ γ - e^{-ψ₀} Σ_j (∂_j θ) β_j`. -/
def cutoffTstar (ψ₀ θ : ComplexModel n → ℝ) (β : Fin n → ComplexModel n → ℂ)
    (γ : ComplexModel n → ℂ) (x : ComplexModel n) : ℂ :=
  (θ x : ℂ) * γ x -
    ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ∑ j, dDir (coordVec j) (fun y ↦ (θ y : ℂ)) x * β j x

/-- The weak `∂̄` of the cut-off form `θ β`: `θ σ + (∂̄_j θ β_k - ∂̄_k θ β_j)`. -/
def cutoffDbar (θ : ComplexModel n → ℝ) (β : Fin n → ComplexModel n → ℂ)
    (σ : Fin n × Fin n → ComplexModel n → ℂ) (p : Fin n × Fin n) (x : ComplexModel n) : ℂ :=
  (θ x : ℂ) * σ p x + (dbarDir (coordVec p.1) (fun y ↦ (θ y : ℂ)) x * β p.2 x -
    dbarDir (coordVec p.2) (fun y ↦ (θ y : ℂ)) x * β p.1 x)

/-- **Weak `T*` of a cut-off form.** -/
theorem weakTstar_cutoff (hD : IsOpen D) {w₁ w₂ ψ₀ : ComplexModel n → ℝ}
    (hw₁ : ContinuousOn w₁ D) (hw₂ : ContinuousOn w₂ D) (hw : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x)
    {θ : ComplexModel n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {β : Fin n → ComplexModel n → ℂ} {γ : ComplexModel n → ℂ}
    (hβ : ∀ j, MemLp (β j) 2 (weightedVolume D w₂)) (hγ : MemLp γ 2 (weightedVolume D w₁))
    (hT : ∀ g, IsTestFunctionOn D g →
      ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * β j x * Real.exp (-w₂ x) =
        ∫ x in D, conj (g x) * γ x * Real.exp (-w₁ x))
    {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * ((θ x : ℂ) * β j x) * Real.exp (-w₂ x) =
      ∫ x in D, conj (g x) * cutoffTstar ψ₀ θ β γ x * Real.exp (-w₁ x) := by
  set K := tsupport g with hK
  have hKc : IsCompact K := hg.2.1
  have hKD : K ⊆ D := hg.2.2
  have hg1 := isTestFunctionOn_contDiff_one hg
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_cast)
  have hgK : ∀ x ∉ K, g x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hdgK : ∀ j, ∀ x ∉ K, dbarDir (coordVec j) g x = 0 := fun j x hx ↦
    dbarDir_eq_zero_of_notMem_tsupport hx
  have hcθ : Continuous fun x ↦ (θ x : ℂ) := by have := hθ1.continuous; fun_prop
  have hdθ : ∀ j, Continuous (dDir (coordVec j) fun y ↦ (θ y : ℂ)) := fun j ↦
    continuous_dDir_of_contDiff (contDiff_ofReal_comp hθ1)
  have he₂ : ContinuousOn (fun x ↦ ((Real.exp (-w₂ x) : ℝ) : ℂ)) K :=
    (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn hw₂.neg)).mono hKD
  have he₁ : ContinuousOn (fun x ↦ ((Real.exp (-w₁ x) : ℝ) : ℂ)) K :=
    (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn hw₁.neg)).mono hKD
  -- the three families of integrands
  set A : Fin n → ComplexModel n → ℂ := fun j x ↦
    conj (dbarDir (coordVec j) g x) * ((θ x : ℂ) * β j x) * Real.exp (-w₂ x) with hA
  set B : Fin n → ComplexModel n → ℂ := fun j x ↦
    conj (g x) * (((Real.exp (-ψ₀ x) : ℝ) : ℂ) * (dDir (coordVec j) (fun y ↦ (θ y : ℂ)) x *
      β j x)) * Real.exp (-w₁ x) with hB
  have hAi : ∀ j, Integrable (A j) := fun j ↦ by
    have h := integrable_mul_of_weightedVolume hD hw₂ hKc hKD (hβ j)
      (v := fun x ↦ conj (dbarDir (coordVec j) g x) * (θ x : ℂ) * Real.exp (-w₂ x))
      (((continuous_conj.comp (continuous_dbarDir hg1)).mul hcθ).continuousOn.mul he₂)
      (fun x hx ↦ by simp [hdgK j x hx])
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [hA]; ring
  have hBD : ∀ j, ∀ x ∈ D, B j x =
      dDir (coordVec j) (fun y ↦ (θ y : ℂ)) x * conj (g x) * β j x * Real.exp (-w₂ x) := by
    intro j x hx
    simp only [hB, hw x hx]
    rw [show -(w₁ x + ψ₀ x) = -ψ₀ x + -w₁ x by ring, Real.exp_add, Complex.ofReal_mul]
    ring
  have hBi : ∀ j, IntegrableOn (B j) D := fun j ↦ by
    have h := integrable_mul_of_weightedVolume hD hw₂ hKc hKD (hβ j)
      (v := fun x ↦ dDir (coordVec j) (fun y ↦ (θ y : ℂ)) x * conj (g x) * Real.exp (-w₂ x))
      (((hdθ j).mul (continuous_conj.comp hg1.continuous)).continuousOn.mul he₂)
      (fun x hx ↦ by simp [hgK x hx])
    refine h.integrableOn.congr_fun (fun x hx ↦ ?_) hD.measurableSet
    rw [hBD j x hx]; ring
  have hCi : Integrable fun x ↦ conj (g x) * ((θ x : ℂ) * γ x) * Real.exp (-w₁ x) := by
    have h := integrable_mul_of_weightedVolume hD hw₁ hKc hKD hγ
      (v := fun x ↦ conj (g x) * (θ x : ℂ) * Real.exp (-w₁ x))
      (((continuous_conj.comp hg1.continuous).mul hcθ).continuousOn.mul he₁)
      (fun x hx ↦ by simp [hgK x hx])
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    ring
  -- apply the hypothesis to the test function `θ g`
  have key := hT _ (isTestFunctionOn_ofReal_mul hθ hg)
  have hsplit : ∀ j, ∫ x in D, conj (dbarDir (coordVec j) (fun y ↦ (θ y : ℂ) * g y) x) * β j x *
      Real.exp (-w₂ x) = (∫ x in D, A j x) + ∫ x in D, B j x := by
    intro j
    rw [← integral_add (hAi j).integrableOn (hBi j)]
    refine setIntegral_congr_fun hD.measurableSet fun x hx ↦ ?_
    rw [hBD j x hx, dbarDir_ofReal_mul (hθ1.differentiable one_ne_zero x)
      (hg1.differentiable one_ne_zero x), dDir_ofReal_eq_conj_dbarDir
      (hθ1.differentiable one_ne_zero x)]
    simp only [hA, map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hsplit, Finset.sum_add_distrib] at key
  have hrhs : ∫ x in D, conj (g x) * cutoffTstar ψ₀ θ β γ x * Real.exp (-w₁ x) =
      (∫ x in D, conj (g x) * ((θ x : ℂ) * γ x) * Real.exp (-w₁ x)) - ∑ j, ∫ x in D, B j x := by
    rw [← integral_finsetSum _ fun j _ ↦ hBi j, ← integral_sub hCi.integrableOn
      (integrable_finsetSum _ fun j _ ↦ hBi j)]
    refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
    simp only [cutoffTstar, hB, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hC : ∫ x in D, conj ((θ x : ℂ) * g x) * γ x * Real.exp (-w₁ x) =
      ∫ x in D, conj (g x) * ((θ x : ℂ) * γ x) * Real.exp (-w₁ x) := by
    refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
    simp only [map_mul, Complex.conj_ofReal]; ring
  rw [hrhs, ← hC, ← key]
  ring

/-- **Weak `∂̄` of a cut-off form.** -/
theorem weakDbar_cutoff (hD : IsOpen D) {w₂ w₃ : ComplexModel n → ℝ}
    (hw₂ : ContinuousOn w₂ D) (hw₃ : ContinuousOn w₃ D)
    {θ : ComplexModel n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {β : Fin n → ComplexModel n → ℂ} {σ : Fin n × Fin n → ComplexModel n → ℂ}
    (hβ : ∀ j, MemLp (β j) 2 (weightedVolume D w₂)) (hσ : ∀ p, MemLp (σ p) 2 (weightedVolume D w₃))
    (hS : ∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (β k x * dbarDir (coordVec j) h x - β j x * dbarDir (coordVec k) h x) =
        -∫ x, σ (j, k) x * h x)
    {h : ComplexModel n → ℂ} (hh : IsTestFunctionOn D h) (j k : Fin n) :
    ∫ x, ((θ x : ℂ) * β k x * dbarDir (coordVec j) h x -
        (θ x : ℂ) * β j x * dbarDir (coordVec k) h x) =
      -∫ x, cutoffDbar θ β σ (j, k) x * h x := by
  set K := tsupport h with hK
  have hKc : IsCompact K := hh.2.1
  have hKD : K ⊆ D := hh.2.2
  have hh1 := isTestFunctionOn_contDiff_one hh
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_cast)
  have hhK : ∀ x ∉ K, h x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hdhK : ∀ i, ∀ x ∉ K, dbarDir (coordVec i) h x = 0 := fun i x hx ↦
    dbarDir_eq_zero_of_notMem_tsupport hx
  have hcθ : Continuous fun x ↦ (θ x : ℂ) := by have := hθ1.continuous; fun_prop
  have hdθ : ∀ i, Continuous (dbarDir (coordVec i) fun y ↦ (θ y : ℂ)) := fun i ↦
    continuous_dbarDir (contDiff_ofReal_comp hθ1)
  -- atomic integrable pieces
  have iA : ∀ i l, Integrable fun x ↦ (θ x : ℂ) * β l x * dbarDir (coordVec i) h x := by
    intro i l
    have h := integrable_mul_of_weightedVolume hD hw₂ hKc hKD (hβ l)
      (v := fun x ↦ (θ x : ℂ) * dbarDir (coordVec i) h x)
      (hcθ.mul (continuous_dbarDir hh1)).continuousOn (fun x hx ↦ by simp [hdhK i x hx])
    exact h.congr (Eventually.of_forall fun x ↦ by ring)
  have iB : ∀ i l, Integrable fun x ↦ dbarDir (coordVec i) (fun y ↦ (θ y : ℂ)) x * β l x * h x := by
    intro i l
    have h := integrable_mul_of_weightedVolume hD hw₂ hKc hKD (hβ l)
      (v := fun x ↦ dbarDir (coordVec i) (fun y ↦ (θ y : ℂ)) x * h x)
      ((hdθ i).mul hh1.continuous).continuousOn (fun x hx ↦ by simp [hhK x hx])
    exact h.congr (Eventually.of_forall fun x ↦ by ring)
  have iC : Integrable fun x ↦ (θ x : ℂ) * σ (j, k) x * h x := by
    have h := integrable_mul_of_weightedVolume hD hw₃ hKc hKD (hσ (j, k))
      (v := fun x ↦ (θ x : ℂ) * h x) (hcθ.mul hh1.continuous).continuousOn
      (fun x hx ↦ by simp [hhK x hx])
    exact h.congr (Eventually.of_forall fun x ↦ by ring)
  have key := hS _ (isTestFunctionOn_ofReal_mul hθ hh) j k
  have e1 : (fun x ↦ β k x * dbarDir (coordVec j) (fun y ↦ (θ y : ℂ) * h y) x -
      β j x * dbarDir (coordVec k) (fun y ↦ (θ y : ℂ) * h y) x) = fun x ↦
      (((θ x : ℂ) * β k x * dbarDir (coordVec j) h x -
        (θ x : ℂ) * β j x * dbarDir (coordVec k) h x) +
      (dbarDir (coordVec j) (fun y ↦ (θ y : ℂ)) x * β k x * h x -
        dbarDir (coordVec k) (fun y ↦ (θ y : ℂ)) x * β j x * h x)) := by
    funext x
    rw [dbarDir_ofReal_mul (hθ1.differentiable one_ne_zero x) (hh1.differentiable one_ne_zero x),
      dbarDir_ofReal_mul (hθ1.differentiable one_ne_zero x) (hh1.differentiable one_ne_zero x)]
    ring
  have e2 : (fun x ↦ cutoffDbar θ β σ (j, k) x * h x) = fun x ↦
      (θ x : ℂ) * σ (j, k) x * h x +
      (dbarDir (coordVec j) (fun y ↦ (θ y : ℂ)) x * β k x * h x -
        dbarDir (coordVec k) (fun y ↦ (θ y : ℂ)) x * β j x * h x) := by
    funext x
    simp only [cutoffDbar]
    ring
  have e3 : (fun x ↦ σ (j, k) x * ((θ x : ℂ) * h x)) = fun x ↦ (θ x : ℂ) * σ (j, k) x * h x := by
    funext x; ring
  have i1 : Integrable fun x ↦ (θ x : ℂ) * β k x * dbarDir (coordVec j) h x -
      (θ x : ℂ) * β j x * dbarDir (coordVec k) h x := (iA j k).sub (iA k j)
  have i2 : Integrable fun x ↦ dbarDir (coordVec j) (fun y ↦ (θ y : ℂ)) x * β k x * h x -
      dbarDir (coordVec k) (fun y ↦ (θ y : ℂ)) x * β j x * h x := (iB j k).sub (iB k j)
  rw [e1, integral_add i1 i2, e3] at key
  rw [e2, integral_add iC i2]
  linear_combination key

theorem norm_dbarDir_le {f : ComplexModel n → ℂ} {x v : ComplexModel n} (hv : ‖v‖ = 1) :
    ‖dbarDir v f x‖ ≤ ‖fderiv ℝ f x‖ := by
  have h1 : ‖fderiv ℝ f x v‖ ≤ ‖fderiv ℝ f x‖ := by
    simpa [hv] using (fderiv ℝ f x).le_opNorm v
  have h2 : ‖fderiv ℝ f x (I • v)‖ ≤ ‖fderiv ℝ f x‖ := by
    simpa [norm_smul, hv] using (fderiv ℝ f x).le_opNorm (I • v)
  unfold dbarDir
  rw [norm_div, RCLike.norm_ofNat]
  calc ‖fderiv ℝ f x v + I * fderiv ℝ f x (I • v)‖ / 2
      ≤ (‖fderiv ℝ f x v‖ + ‖I * fderiv ℝ f x (I • v)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ (‖fderiv ℝ f x‖ + ‖fderiv ℝ f x‖) / 2 := by
        gcongr; rw [norm_mul, norm_I, one_mul]; exact h2
    _ = ‖fderiv ℝ f x‖ := by ring

section Limits

variable {w₁ w₂ w₃ ψ₀ : ComplexModel n → ℝ} {η : ℕ → ComplexModel n → ℝ}

theorem eventually_fderiv_ofReal_eq_zero (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    {x : ComplexModel n} (hx : x ∈ D) :
    ∀ᶠ k in atTop, η k x = 1 ∧ fderiv ℝ (fun y ↦ (η k y : ℂ)) x = 0 := by
  filter_upwards [hη1 x hx] with k hk
  refine ⟨hk.eq_of_nhds, ?_⟩
  have h : (fun y ↦ (η k y : ℂ)) =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ) := by
    filter_upwards [hk] with y hy
    simp [hy]
  rw [h.fderiv_eq]
  simp

theorem tendsto_dDir_cutoff (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    {x : ComplexModel n} (hx : x ∈ D) (v : ComplexModel n) :
    Tendsto (fun k ↦ dDir v (fun y ↦ (η k y : ℂ)) x) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_fderiv_ofReal_eq_zero hη1 hx] with k hk
  simp [dDir, hk.2]

theorem tendsto_dbarDir_cutoff (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    {x : ComplexModel n} (hx : x ∈ D) (v : ComplexModel n) :
    Tendsto (fun k ↦ dbarDir v (fun y ↦ (η k y : ℂ)) x) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_fderiv_ofReal_eq_zero hη1 hx] with k hk
  simp [dbarDir, hk.2]

theorem tendsto_cutoff_sub_one (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    {x : ComplexModel n} (hx : x ∈ D) :
    Tendsto (fun k ↦ (η k x : ℂ) - 1) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_fderiv_ofReal_eq_zero hη1 hx] with k hk
  simp [hk.1]

/-- `η_k β → β` in weighted `L²`. -/
theorem tendsto_eLpNorm_cutoff_mul_sub (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) (hη : ∀ k, Continuous (η k)) (hη01 : ∀ k x, 0 ≤ η k x ∧ η k x ≤ 1)
    (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    {β : ComplexModel n → ℂ} (hβ : MemLp β 2 (weightedVolume D w)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ (η k x : ℂ) * β x - β x) 2 (weightedVolume D w))
      atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_mul_weightedVolume hD hw hw hβ (c := fun k x ↦ (η k x : ℂ) - 1)
    (fun k ↦ (by have := hη k; fun_prop : Continuous fun x ↦ (η k x : ℂ) - 1).aestronglyMeasurable)
    (fun k x _ ↦ ?_) (fun x hx ↦ tendsto_cutoff_sub_one hη1 hx)
  · refine h.congr fun k ↦ ?_
    congr 1; funext x; ring
  · rw [sub_self, Real.exp_zero]
    have e : (η k x : ℂ) - 1 = ((η k x - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [hη01 k x]

theorem norm_sq_dDir_cutoff_le {θ : ComplexModel n → ℝ} (hθ : ContDiff ℝ 1 θ) (j : Fin n)
    (x : ComplexModel n) :
    ‖dDir (coordVec j) (fun y ↦ (θ y : ℂ)) x‖ ^ 2 ≤ ‖fderiv ℝ θ x‖ ^ 2 := by
  have h := norm_dDir_le (f := fun y ↦ (θ y : ℂ)) (x := x) (norm_coordVec j)
  rw [norm_fderiv_ofReal_comp (hθ.differentiable one_ne_zero x)] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem norm_sq_dbarDir_cutoff_le {θ : ComplexModel n → ℝ} (hθ : ContDiff ℝ 1 θ) (j : Fin n)
    (x : ComplexModel n) :
    ‖dbarDir (coordVec j) (fun y ↦ (θ y : ℂ)) x‖ ^ 2 ≤ ‖fderiv ℝ θ x‖ ^ 2 := by
  have h := norm_dbarDir_le (f := fun y ↦ (θ y : ℂ)) (x := x) (norm_coordVec j)
  rw [norm_fderiv_ofReal_comp (hθ.differentiable one_ne_zero x)] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `T* (η_k β) → γ` in `L²(e^{-w₁})`. -/
theorem tendsto_eLpNorm_cutoffTstar_sub (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D)
    (hw₂ : ContinuousOn w₂ D) (hψ : ContinuousOn ψ₀ D) (hw : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x)
    (hη : ∀ k, ContDiff ℝ ∞ (η k)) (hη01 : ∀ k x, 0 ≤ η k x ∧ η k x ≤ 1)
    (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    (hηgrad : ∀ k, ∀ x ∈ D, ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x))
    {β : Fin n → ComplexModel n → ℂ} {γ : ComplexModel n → ℂ}
    (hβ : ∀ j, MemLp (β j) 2 (weightedVolume D w₂)) (hγ : MemLp γ 2 (weightedVolume D w₁)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ cutoffTstar ψ₀ (η k) β γ x - γ x) 2
      (weightedVolume D w₁)) atTop (𝓝 0) := by
  have hη1' : ∀ k, ContDiff ℝ 1 (η k) := fun k ↦ (hη k).of_le (by norm_cast)
  have hDm := hD.measurableSet
  have hβm : ∀ j, AEStronglyMeasurable (β j) (volume.restrict D) := fun j ↦
    (aestronglyMeasurable_weightedVolume_iff hD hw₂).mp (hβ j).1
  set c : ℕ → Fin n → ComplexModel n → ℂ := fun k j x ↦
    ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * dDir (coordVec j) (fun y ↦ (η k y : ℂ)) x with hc
  have hcm : ∀ k j, AEStronglyMeasurable (c k j) (volume.restrict D) := fun k j ↦ by
    refine ContinuousOn.aestronglyMeasurable ?_ hDm
    exact (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn hψ.neg)).mul
      (continuous_dDir_of_contDiff (contDiff_ofReal_comp (hη1' k))).continuousOn
  have hf := tendsto_eLpNorm_cutoff_mul_sub hD hw₁ (fun k ↦ (hη k).continuous) hη01 hη1 hγ
  have hg : Tendsto (fun k ↦ eLpNorm (fun x ↦ ∑ j, c k j x * β j x) 2 (weightedVolume D w₁))
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sum (fun k j ↦ ?_) fun j ↦ ?_
    · exact (aestronglyMeasurable_weightedVolume_iff hD hw₁).mpr ((hcm k j).mul (hβm j))
    · refine tendsto_eLpNorm_mul_weightedVolume hD hw₁ hw₂ (hβ j) (fun k ↦ hcm k j)
        (fun k x hx ↦ ?_) fun x hx ↦ ?_
      · simp only [hc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        calc Real.exp (-ψ₀ x) ^ 2 * ‖dDir (coordVec j) (fun y ↦ (η k y : ℂ)) x‖ ^ 2
            ≤ Real.exp (-ψ₀ x) ^ 2 * Real.exp (ψ₀ x) := by
              gcongr
              exact (norm_sq_dDir_cutoff_le (hη1' k) j x).trans (hηgrad k x hx)
          _ = Real.exp (w₁ x - w₂ x) := by
              rw [hw x hx, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      · simpa [hc] using (tendsto_dDir_cutoff hη1 hx (coordVec j)).const_mul
          ((Real.exp (-ψ₀ x) : ℝ) : ℂ)
  have h := tendsto_eLpNorm_sub (μ := weightedVolume D w₁)
    (f := fun k x ↦ (η k x : ℂ) * γ x - γ x) (g := fun k x ↦ ∑ j, c k j x * β j x)
    (fun k ↦ ((aestronglyMeasurable_weightedVolume_iff hD hw₁).mpr
      (((by have := (hη k).continuous; fun_prop : Continuous fun x ↦ (η k x : ℂ)).aestronglyMeasurable).mul
        ((aestronglyMeasurable_weightedVolume_iff hD hw₁).mp hγ.1))).sub hγ.1)
    (fun k ↦ (aestronglyMeasurable_weightedVolume_iff hD hw₁).mpr
      (Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦ (hcm k j).mul (hβm j))) hf hg
  refine h.congr fun k ↦ ?_
  congr 1
  funext x
  simp only [cutoffTstar, hc, Finset.mul_sum]
  ring_nf

/-- `∂̄ (η_k β) → σ` in `L²(e^{-w₃})`. -/
theorem tendsto_eLpNorm_cutoffDbar_sub (hD : IsOpen D) (hw₂ : ContinuousOn w₂ D)
    (hw₃ : ContinuousOn w₃ D) (hw : ∀ x ∈ D, w₃ x = w₂ x + ψ₀ x)
    (hη : ∀ k, ContDiff ℝ ∞ (η k)) (hη01 : ∀ k x, 0 ≤ η k x ∧ η k x ≤ 1)
    (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    (hηgrad : ∀ k, ∀ x ∈ D, ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x))
    {β : Fin n → ComplexModel n → ℂ} {σ : Fin n × Fin n → ComplexModel n → ℂ}
    (hβ : ∀ j, MemLp (β j) 2 (weightedVolume D w₂)) (hσ : ∀ p, MemLp (σ p) 2 (weightedVolume D w₃))
    (p : Fin n × Fin n) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ cutoffDbar (η k) β σ p x - σ p x) 2
      (weightedVolume D w₃)) atTop (𝓝 0) := by
  have hη1' : ∀ k, ContDiff ℝ 1 (η k) := fun k ↦ (hη k).of_le (by norm_cast)
  have hDm := hD.measurableSet
  have hβm : ∀ j, AEStronglyMeasurable (β j) (volume.restrict D) := fun j ↦
    (aestronglyMeasurable_weightedVolume_iff hD hw₂).mp (hβ j).1
  have hcm : ∀ k i, AEStronglyMeasurable (dbarDir (coordVec i) (fun y ↦ (η k y : ℂ)))
      (volume.restrict D) := fun k i ↦
    (continuous_dbarDir (contDiff_ofReal_comp (hη1' k))).aestronglyMeasurable
  have hterm : ∀ i l, Tendsto (fun k ↦ eLpNorm (fun x ↦
      dbarDir (coordVec i) (fun y ↦ (η k y : ℂ)) x * β l x) 2 (weightedVolume D w₃))
      atTop (𝓝 0) := by
    intro i l
    refine tendsto_eLpNorm_mul_weightedVolume hD hw₃ hw₂ (hβ l) (fun k ↦ hcm k i)
      (fun k x hx ↦ ?_) fun x hx ↦ tendsto_dbarDir_cutoff hη1 hx _
    calc _ ≤ ‖fderiv ℝ (η k) x‖ ^ 2 := norm_sq_dbarDir_cutoff_le (hη1' k) i x
      _ ≤ Real.exp (ψ₀ x) := hηgrad k x hx
      _ = Real.exp (w₃ x - w₂ x) := by rw [hw x hx]; ring_nf
  have hmeas : ∀ k i l, AEStronglyMeasurable (fun x ↦
      dbarDir (coordVec i) (fun y ↦ (η k y : ℂ)) x * β l x) (weightedVolume D w₃) :=
    fun k i l ↦ (aestronglyMeasurable_weightedVolume_iff hD hw₃).mpr ((hcm k i).mul (hβm l))
  have hf := tendsto_eLpNorm_cutoff_mul_sub hD hw₃ (fun k ↦ (hη k).continuous) hη01 hη1 (hσ p)
  have hg := tendsto_eLpNorm_sub (fun k ↦ hmeas k p.1 p.2) (fun k ↦ hmeas k p.2 p.1)
    (hterm p.1 p.2) (hterm p.2 p.1)
  have h := tendsto_eLpNorm_add (μ := weightedVolume D w₃)
    (f := fun k x ↦ (η k x : ℂ) * σ p x - σ p x)
    (g := fun k x ↦ dbarDir (coordVec p.1) (fun y ↦ (η k y : ℂ)) x * β p.2 x -
      dbarDir (coordVec p.2) (fun y ↦ (η k y : ℂ)) x * β p.1 x)
    (fun k ↦ ((aestronglyMeasurable_weightedVolume_iff hD hw₃).mpr
      (((by have := (hη k).continuous; fun_prop : Continuous fun x ↦ (η k x : ℂ)).aestronglyMeasurable).mul
        ((aestronglyMeasurable_weightedVolume_iff hD hw₃).mp (hσ p).1))).sub (hσ p).1)
    (fun k ↦ (hmeas k p.1 p.2).sub (hmeas k p.2 p.1)) hf hg
  refine h.congr fun k ↦ ?_
  congr 1
  funext x
  simp only [cutoffDbar]
  ring

end Limits

end Cutoff

/-! ### Step 2: mollifying compactly supported data -/

section Mollify

variable {D : Set (ComplexModel n)}

theorem integrable_mul_of_continuous {u v : ComplexModel n → ℂ} (hu : Integrable u)
    (hv : Continuous v) (hvc : HasCompactSupport v) : Integrable fun x ↦ u x * v x := by
  obtain ⟨C, hC⟩ := hv.bounded_above_of_compact_support hvc
  exact hu.mul_bdd hv.aestronglyMeasurable (Eventually.of_forall hC)

theorem memLp_mul_of_eq_zero_off {Q : Set (ComplexModel n)} (hQ : IsCompact Q)
    {u v : ComplexModel n → ℂ} (hu : MemLp u 2 volume) (hu0 : ∀ x ∉ Q, u x = 0)
    (hv : Continuous v) : MemLp (fun x ↦ u x * v x) 2 volume := by
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hv.continuousOn
  simp_rw [mul_comm (u _)]
  refine hu.of_le_mul (c := C) (hv.aestronglyMeasurable.mul hu.1) (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ Q
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)
  · have h0 : ‖v x * u x‖ = 0 := by simp [hu0 x hx]
    rw [h0, hu0 x hx, norm_zero, mul_zero]

theorem dbarDir_neg_fun {v : ComplexModel n} {f : ComplexModel n → ℂ} {x : ComplexModel n} :
    dbarDir v (fun y ↦ -f y) x = -dbarDir v f x := by
  simp only [dbarDir, fderiv_fun_neg, neg_apply]
  ring

theorem hasFDerivAt_ofReal_exp {W : ComplexModel n → ℝ} {x : ComplexModel n}
    (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ)) x =
      ((Real.exp (W x) : ℝ) : ℂ) • fderiv ℝ (fun y ↦ (W y : ℂ)) x := by
  have h1 : HasFDerivAt (fun y ↦ Real.exp (W y)) (Real.exp (W x) • fderiv ℝ W x) x :=
    hW.hasFDerivAt.exp
  have h2 : fderiv ℝ (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ)) x =
      Complex.ofRealCLM.comp (Real.exp (W x) • fderiv ℝ W x) :=
    ((Complex.ofRealCLM.hasFDerivAt).comp x h1).fderiv
  have h3 : fderiv ℝ (fun y ↦ (W y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ W x) :=
    ((Complex.ofRealCLM.hasFDerivAt).comp x hW.hasFDerivAt).fderiv
  rw [h2, h3]
  ext v
  simp [Complex.real_smul]

theorem dDir_ofReal_exp {v : ComplexModel n} {W : ComplexModel n → ℝ} {x : ComplexModel n}
    (hW : DifferentiableAt ℝ W x) :
    dDir v (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ)) x =
      ((Real.exp (W x) : ℝ) : ℂ) * dDir v (fun y ↦ (W y : ℂ)) x := by
  simp only [dDir, hasFDerivAt_ofReal_exp hW, smul_apply, smul_eq_mul]
  ring

theorem dbarDir_ofReal_exp {v : ComplexModel n} {W : ComplexModel n → ℝ} {x : ComplexModel n}
    (hW : DifferentiableAt ℝ W x) :
    dbarDir v (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ)) x =
      ((Real.exp (W x) : ℝ) : ℂ) * dbarDir v (fun y ↦ (W y : ℂ)) x := by
  simp only [dbarDir, hasFDerivAt_ofReal_exp hW, smul_apply, smul_eq_mul]
  ring

theorem differentiableAt_ofReal_exp {W : ComplexModel n → ℝ} {x : ComplexModel n}
    (hW : DifferentiableAt ℝ W x) :
    DifferentiableAt ℝ (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ)) x :=
  differentiableAt_ofReal_comp hW.exp

/-- `δ^W_v (e^W F) = e^W ∂_v F`. -/
theorem deltaDir_exp_mul {v : ComplexModel n} {W : ComplexModel n → ℝ} {F : ComplexModel n → ℂ}
    {x : ComplexModel n} (hW : DifferentiableAt ℝ W x) (hF : DifferentiableAt ℝ F x) :
    deltaDir v W (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ) * F y) x =
      ((Real.exp (W x) : ℝ) : ℂ) * dDir v F x := by
  rw [deltaDir, dDir_mul (differentiableAt_ofReal_exp hW) hF, dDir_ofReal_exp hW]
  ring

/-- `∂̄_v (e^W F) = e^W (∂̄_v W · F + ∂̄_v F)`. -/
theorem dbarDir_exp_mul {v : ComplexModel n} {W : ComplexModel n → ℝ} {F : ComplexModel n → ℂ}
    {x : ComplexModel n} (hW : DifferentiableAt ℝ W x) (hF : DifferentiableAt ℝ F x) :
    dbarDir v (fun y ↦ ((Real.exp (W y) : ℝ) : ℂ) * F y) x =
      ((Real.exp (W x) : ℝ) : ℂ) * (dbarDir v (fun y ↦ (W y : ℂ)) x * F x + dbarDir v F x) := by
  rw [dbarDir_mul (differentiableAt_ofReal_exp hW) hF, dbarDir_ofReal_exp hW]
  ring

/-- **The weak `T*` equation passes to mollifications.**  For data supported in a compact
`Q ⊆ D`, with `b_j = β_j e^{-W₂}` and `c = γ e^{-W₁}` (where `W_i = w_i` on `Q`),
`-Σ_j ∂_j (ρ ⋆ b_j) = ρ ⋆ c` at every point whose `rOut`-ball lies in `D`. -/
theorem neg_sum_dDir_bump_convolution_eq (hD : IsOpen D) {Q : Set (ComplexModel n)}
    (hQ : IsCompact Q) (hQD : Q ⊆ D) {w₁ w₂ W₁ W₂ : ComplexModel n → ℝ}
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hWQ₁ : ∀ x ∈ Q, W₁ x = w₁ x)
    (hWQ₂ : ∀ x ∈ Q, W₂ x = w₂ x)
    {β : Fin n → ComplexModel n → ℂ} {γ : ComplexModel n → ℂ}
    (hβQ : ∀ j, ∀ x ∉ Q, β j x = 0) (hγQ : ∀ x ∉ Q, γ x = 0)
    (hβ : ∀ j, MemLp (β j) 2 volume) (hγ : MemLp γ 2 volume)
    (hT : ∀ g, IsTestFunctionOn D g →
      ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * β j x * Real.exp (-w₂ x) =
        ∫ x in D, conj (g x) * γ x * Real.exp (-w₁ x))
    (ρ : ContDiffBump (0 : ComplexModel n)) {x : ComplexModel n}
    (hx : closedBall x ρ.rOut ⊆ D) :
    -∑ j, dDir (coordVec j) (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y ↦ β j y * Real.exp (-W₂ y)) x =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y ↦ γ y * Real.exp (-W₁ y)) x := by
  set b : Fin n → ComplexModel n → ℂ := fun j y ↦ β j y * Real.exp (-W₂ y) with hb
  set c : ComplexModel n → ℂ := fun y ↦ γ y * Real.exp (-W₁ y) with hc
  have hexp : ∀ W : ComplexModel n → ℝ, Continuous W →
      Continuous fun y ↦ ((Real.exp (-W y) : ℝ) : ℂ) := fun W hW ↦ by fun_prop
  have hbL : ∀ j, MemLp (b j) 2 volume := fun j ↦ by
    exact memLp_mul_of_eq_zero_off hQ (hβ j) (hβQ j) (hexp W₂ hW₂)
  have hcL : MemLp c 2 volume := memLp_mul_of_eq_zero_off hQ hγ hγQ (hexp W₁ hW₁)
  have hbQ : ∀ j, ∀ y ∉ Q, b j y = 0 := fun j y hy ↦ by simp [hb, hβQ j y hy]
  have hcQ : ∀ y ∉ Q, c y = 0 := fun y hy ↦ by simp [hc, hγQ y hy]
  have hbI : ∀ j, Integrable (b j) := fun j ↦
    integrable_of_memLp_two_of_eq_zero_off hQ (hbL j) (hbQ j)
  have hcI : Integrable c := integrable_of_memLp_two_of_eq_zero_off hQ hcL hcQ
  have hweak : ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ D →
      ∑ i : Fin n ⊕ Fin n, (Sum.elim (fun _ ↦ (-1 / 2 : ℂ)) (fun _ ↦ I / 2) i) *
        ∫ y, Sum.elim b b i y * fderiv ℝ g y (Sum.elim (fun j ↦ (coordVec j : ComplexModel n))
          (fun j ↦ I • (coordVec j : ComplexModel n)) i) = -∫ y, c y * g y := by
    intro g hg hgc hgD
    have hgt : IsTestFunctionOn D g := ⟨hg, hgc, hgD⟩
    have hg1 := isTestFunctionOn_contDiff_one hgt
    have key := hT _ (isTestFunctionOn_conj hgt)
    have hL : ∀ j, ∫ y in D, conj (dbarDir (coordVec j) (fun z ↦ conj (g z)) y) * β j y *
        Real.exp (-w₂ y) = ∫ y, b j y * dDir (coordVec j) g y := by
      intro j
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
        simp [hβQ j y fun h ↦ hy (hQD h)]]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      by_cases hy : y ∈ Q
      · simp only [hb, dbarDir_conj (hg1.differentiable one_ne_zero y), conj_conj, hWQ₂ y hy]
        ring
      · simp [hb, hβQ j y hy]
    have hR : ∫ y in D, conj (conj (g y)) * γ y * Real.exp (-w₁ y) = ∫ y, c y * g y := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
        simp [hγQ y fun h ↦ hy (hQD h)]]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      by_cases hy : y ∈ Q
      · simp only [hc, conj_conj, hWQ₁ y hy]
        ring
      · simp [hc, hγQ y hy]
    simp only [hL, hR] at key
    have hsplit : ∀ j, ∫ y, b j y * dDir (coordVec j) g y =
        (1 / 2 : ℂ) * (∫ y, b j y * fderiv ℝ g y (coordVec j)) +
          (-I / 2) * ∫ y, b j y * fderiv ℝ g y (I • coordVec j) := by
      intro j
      have i1 : Integrable fun y ↦ b j y * fderiv ℝ g y (coordVec j) :=
        integrable_mul_of_continuous (hbI j) (continuous_fderiv_apply' hg1 _)
          (hgc.fderiv_apply (𝕜 := ℝ) _)
      have i2 : Integrable fun y ↦ b j y * fderiv ℝ g y (I • coordVec j) :=
        integrable_mul_of_continuous (hbI j) (continuous_fderiv_apply' hg1 _)
          (hgc.fderiv_apply (𝕜 := ℝ) _)
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
        (i2.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [dDir]
      ring
    simp only [hsplit] at key
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← key, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h := sum_fderiv_bump_convolution_eq_of_weak (μ := volume) hD
    (f := Sum.elim b b) (fun i ↦ by cases i <;> exact (hbL _).locallyIntegrable one_le_two)
    (hcL.locallyIntegrable one_le_two) _ _ hweak ρ hx
  rw [← h, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, dDir]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **The weak `∂̄` equation passes to mollifications.**  For data supported in a compact
`Q ⊆ D` and a smooth `W`, with `b_j = β_j e^{-W}` and
`ζ = σ_{jk} e^{-W} - (∂̄_j W b_k - ∂̄_k W b_j)`, one has
`∂̄_j (ρ ⋆ b_k) - ∂̄_k (ρ ⋆ b_j) = ρ ⋆ ζ` at every point whose `rOut`-ball lies in `D`. -/
theorem dbarDir_bump_convolution_sub_eq (hD : IsOpen D) {Q : Set (ComplexModel n)}
    (hQ : IsCompact Q) {W : ComplexModel n → ℝ} (hW : ContDiff ℝ ∞ W)
    {β : Fin n → ComplexModel n → ℂ} {σ : Fin n × Fin n → ComplexModel n → ℂ}
    (hβQ : ∀ j, ∀ x ∉ Q, β j x = 0) (hσQ : ∀ p, ∀ x ∉ Q, σ p x = 0)
    (hβ : ∀ j, MemLp (β j) 2 volume) (hσ : ∀ p, MemLp (σ p) 2 volume)
    (hS : ∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (β k x * dbarDir (coordVec j) h x - β j x * dbarDir (coordVec k) h x) =
        -∫ x, σ (j, k) x * h x)
    (ρ : ContDiffBump (0 : ComplexModel n)) {x : ComplexModel n}
    (hx : closedBall x ρ.rOut ⊆ D) (j k : Fin n) :
    dbarDir (coordVec j) (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y ↦ β k y * Real.exp (-W y)) x -
      dbarDir (coordVec k) (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y ↦ β j y * Real.exp (-W y)) x =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y ↦
        σ (j, k) y * Real.exp (-W y) -
          (dbarDir (coordVec j) (fun z ↦ (W z : ℂ)) y * (β k y * Real.exp (-W y)) -
            dbarDir (coordVec k) (fun z ↦ (W z : ℂ)) y * (β j y * Real.exp (-W y)))) x := by
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_cast)
  set b : Fin n → ComplexModel n → ℂ := fun i y ↦ β i y * Real.exp (-W y) with hb
  set ζ : ComplexModel n → ℂ := fun y ↦ σ (j, k) y * Real.exp (-W y) -
    (dbarDir (coordVec j) (fun z ↦ (W z : ℂ)) y * b k y -
      dbarDir (coordVec k) (fun z ↦ (W z : ℂ)) y * b j y) with hζ
  have hexp : Continuous fun y ↦ ((Real.exp (-W y) : ℝ) : ℂ) := by
    have := hW.continuous; fun_prop
  have hdW : ∀ i, Continuous (dbarDir (coordVec i) fun z ↦ (W z : ℂ)) := fun i ↦
    continuous_dbarDir (contDiff_ofReal_comp hW1)
  have hbL : ∀ i, MemLp (b i) 2 volume := fun i ↦
    memLp_mul_of_eq_zero_off hQ (hβ i) (hβQ i) hexp
  have hbQ : ∀ i, ∀ y ∉ Q, b i y = 0 := fun i y hy ↦ by simp [hb, hβQ i y hy]
  have hbI : ∀ i, Integrable (b i) := fun i ↦
    integrable_of_memLp_two_of_eq_zero_off hQ (hbL i) (hbQ i)
  have hsL : MemLp (fun y ↦ σ (j, k) y * Real.exp (-W y)) 2 volume :=
    memLp_mul_of_eq_zero_off hQ (hσ (j, k)) (hσQ (j, k)) hexp
  have hsI : Integrable fun y ↦ σ (j, k) y * Real.exp (-W y) :=
    integrable_of_memLp_two_of_eq_zero_off hQ hsL fun y hy ↦ by simp [hσQ (j, k) y hy]
  have hdb : ∀ i l, MemLp (fun y ↦ dbarDir (coordVec i) (fun z ↦ (W z : ℂ)) y * b l y) 2 volume :=
    fun i l ↦ MemLp.ae_eq (Eventually.of_forall fun y ↦ mul_comm _ _)
      (memLp_mul_of_eq_zero_off hQ (hbL l) (hbQ l) (hdW i))
  have hζL : MemLp ζ 2 volume := hsL.sub ((hdb j k).sub (hdb k j))
  have hweak : ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ D →
      ∑ i : Fin 4, (![(1 / 2 : ℂ), I / 2, -1 / 2, -I / 2] i) *
        ∫ y, (![b k, b k, b j, b j] i) y * fderiv ℝ g y
          (![(coordVec j : ComplexModel n), I • coordVec j, coordVec k, I • coordVec k] i) =
        -∫ y, ζ y * g y := by
    intro g hg hgc hgD
    have hgt : IsTestFunctionOn D g := ⟨hg, hgc, hgD⟩
    have hg1 := isTestFunctionOn_contDiff_one hgt
    have hθ : ContDiff ℝ ∞ fun y ↦ Real.exp (-W y) := hW.neg.exp
    have key := hS _ (isTestFunctionOn_ofReal_mul hθ hgt) j k
    have hdH : ∀ i y, dbarDir (coordVec i) (fun z ↦ ((Real.exp (-W z) : ℝ) : ℂ) * g z) y =
        ((Real.exp (-W y) : ℝ) : ℂ) *
          (-dbarDir (coordVec i) (fun z ↦ (W z : ℂ)) y * g y + dbarDir (coordVec i) g y) := by
      intro i y
      have e : (fun z ↦ ((-W z : ℝ) : ℂ)) = fun z ↦ -(W z : ℂ) := by funext z; push_cast; ring
      rw [dbarDir_exp_mul (W := fun z ↦ -W z) (hW1.differentiable one_ne_zero y).neg
        (hg1.differentiable one_ne_zero y), e, dbarDir_neg_fun]
    have iA : ∀ i l, Integrable fun y ↦ b l y * dbarDir (coordVec i) g y := fun i l ↦
      integrable_mul_of_continuous (hbI l) (continuous_dbarDir hg1) (hasCompactSupport_dbarDir hgc)
    have iB : ∀ i l, Integrable fun y ↦ b l y * (dbarDir (coordVec i) (fun z ↦ (W z : ℂ)) y * g y) :=
      fun i l ↦ integrable_mul_of_continuous (hbI l) ((hdW i).mul hg1.continuous) hgc.mul_left
    have iS : Integrable fun y ↦ σ (j, k) y * Real.exp (-W y) * g y :=
      integrable_mul_of_continuous hsI hg1.continuous hgc
    have e1 : (fun y ↦ β k y * dbarDir (coordVec j) (fun z ↦ ((Real.exp (-W z) : ℝ) : ℂ) * g z) y -
        β j y * dbarDir (coordVec k) (fun z ↦ ((Real.exp (-W z) : ℝ) : ℂ) * g z) y) = fun y ↦
        (b k y * dbarDir (coordVec j) g y - b j y * dbarDir (coordVec k) g y) -
        (b k y * (dbarDir (coordVec j) (fun z ↦ (W z : ℂ)) y * g y) -
          b j y * (dbarDir (coordVec k) (fun z ↦ (W z : ℂ)) y * g y)) := by
      funext y; simp only [hdH, hb]; ring
    have e2 : (fun y ↦ σ (j, k) y * (((Real.exp (-W y) : ℝ) : ℂ) * g y)) =
        fun y ↦ σ (j, k) y * Real.exp (-W y) * g y := by funext y; ring
    have iAA : Integrable fun y ↦ b k y * dbarDir (coordVec j) g y -
        b j y * dbarDir (coordVec k) g y := (iA j k).sub (iA k j)
    have iBB : Integrable fun y ↦ b k y * (dbarDir (coordVec j) (fun z ↦ (W z : ℂ)) y * g y) -
        b j y * (dbarDir (coordVec k) (fun z ↦ (W z : ℂ)) y * g y) := (iB j k).sub (iB k j)
    rw [e1, e2, integral_sub iAA iBB] at key
    have hζg : ∫ y, ζ y * g y = (∫ y, σ (j, k) y * Real.exp (-W y) * g y) -
        ∫ y, (b k y * (dbarDir (coordVec j) (fun z ↦ (W z : ℂ)) y * g y) -
          b j y * (dbarDir (coordVec k) (fun z ↦ (W z : ℂ)) y * g y)) := by
      rw [← integral_sub iS iBB]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [hζ]; ring
    have hD4 : ∀ (l : Fin n) (v : ComplexModel n),
        Integrable fun y ↦ b l y * fderiv ℝ g y v := fun l v ↦
      integrable_mul_of_continuous (hbI l) (continuous_fderiv_apply' hg1 _)
        (hgc.fderiv_apply (𝕜 := ℝ) _)
    have hsplit2 : ∀ (l i : Fin n), ∫ y, b l y * dbarDir (coordVec i) g y =
        (1 / 2 : ℂ) * (∫ y, b l y * fderiv ℝ g y (coordVec i)) +
          (I / 2) * ∫ y, b l y * fderiv ℝ g y (I • coordVec i) := by
      intro l i
      have i1 : Integrable fun y ↦ b l y * fderiv ℝ g y (coordVec i) := hD4 l _
      have i2 : Integrable fun y ↦ b l y * fderiv ℝ g y (I • coordVec i) := hD4 l _
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
        (i2.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [dbarDir]
      ring
    have hAsplit : ∫ y, (b k y * dbarDir (coordVec j) g y - b j y * dbarDir (coordVec k) g y) =
        (1 / 2 : ℂ) * (∫ y, b k y * fderiv ℝ g y (coordVec j)) +
          (I / 2) * (∫ y, b k y * fderiv ℝ g y (I • coordVec j)) +
          (-1 / 2) * (∫ y, b j y * fderiv ℝ g y (coordVec k)) +
          (-I / 2) * ∫ y, b j y * fderiv ℝ g y (I • coordVec k) := by
      rw [integral_sub (iA j k) (iA k j), hsplit2, hsplit2]
      ring
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hζg]
    linear_combination key - hAsplit
  have h := sum_fderiv_bump_convolution_eq_of_weak (μ := volume) hD
    (f := ![b k, b k, b j, b j]) (fun i ↦ by
      fin_cases i <;> exact (hbL _).locallyIntegrable one_le_two)
    (hζL.locallyIntegrable one_le_two) _ _ hweak ρ hx
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  rw [← h]
  simp only [dbarDir]
  ring

theorem norm_exp_mul_combo_le (e d₁ d₂ A B Z : ℂ) :
    ‖e * (d₁ * A - d₂ * B + Z)‖ ≤ ‖e‖ * (‖d₁‖ + ‖d₂‖ + 1) * (‖A‖ + ‖B‖ + ‖Z‖) := by
  rw [norm_mul, mul_assoc]
  gcongr
  calc ‖d₁ * A - d₂ * B + Z‖ ≤ ‖d₁‖ * ‖A‖ + ‖d₂‖ * ‖B‖ + ‖Z‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (‖d₁‖ + ‖d₂‖ + 1) * (‖A‖ + ‖B‖ + ‖Z‖) := by
        have := norm_nonneg d₁; have := norm_nonneg d₂; have := norm_nonneg A
        have := norm_nonneg B; have := norm_nonneg Z
        nlinarith [mul_nonneg (norm_nonneg d₁) (norm_nonneg B),
          mul_nonneg (norm_nonneg d₁) (norm_nonneg Z), mul_nonneg (norm_nonneg d₂) (norm_nonneg A),
          mul_nonneg (norm_nonneg d₂) (norm_nonneg Z)]

theorem dDir_congr_of_eventuallyEq {v : ComplexModel n} {f g : ComplexModel n → ℂ}
    {x : ComplexModel n} (h : f =ᶠ[𝓝 x] g) : dDir v f x = dDir v g x := by
  simp only [dDir, h.fderiv_eq]

theorem deltaDir_congr_weight_of_eventuallyEq {v : ComplexModel n} {w W : ComplexModel n → ℝ}
    {a : ComplexModel n → ℂ} {x : ComplexModel n} (h : W =ᶠ[𝓝 x] w) :
    deltaDir v w a x = deltaDir v W a x := by
  have h' : (fun y ↦ (w y : ℂ)) =ᶠ[𝓝 x] fun y ↦ (W y : ℂ) := by
    filter_upwards [h] with y hy
    rw [hy]
  simp only [deltaDir, dDir_congr_of_eventuallyEq h']

/-- **Step 2: compactly supported data are limits of test forms.** -/
theorem exists_testForm_tendsto_of_compact (hD : IsOpen D) {Q : Set (ComplexModel n)}
    (hQ : IsCompact Q) (hQD : Q ⊆ D) {w₁ w₂ w₃ ψ₀ : ComplexModel n → ℝ}
    (hw₁ : ContDiffOn ℝ ∞ w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hw₃ : ContinuousOn w₃ D)
    (hψ : ContinuousOn ψ₀ D) (hw : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x)
    {β : Fin n → ComplexModel n → ℂ} {γ : ComplexModel n → ℂ}
    {σ : Fin n × Fin n → ComplexModel n → ℂ}
    (hβQ : ∀ j, ∀ x ∉ Q, β j x = 0) (hγQ : ∀ x ∉ Q, γ x = 0) (hσQ : ∀ p, ∀ x ∉ Q, σ p x = 0)
    (hβ : ∀ j, MemLp (β j) 2 volume) (hγ : MemLp γ 2 volume) (hσ : ∀ p, MemLp (σ p) 2 volume)
    (hT : ∀ g, IsTestFunctionOn D g →
      ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * β j x * Real.exp (-w₂ x) =
        ∫ x in D, conj (g x) * γ x * Real.exp (-w₁ x))
    (hS : ∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (β k x * dbarDir (coordVec j) h x - β j x * dbarDir (coordVec k) h x) =
        -∫ x, σ (j, k) x * h x) :
    ∃ βs : ℕ → Fin n → ComplexModel n → ℂ, (∀ m j, IsTestFunctionOn D (βs m j)) ∧
      (∀ j, Tendsto (fun m ↦ eLpNorm (fun x ↦ βs m j x - β j x) 2 (weightedVolume D w₂))
        atTop (𝓝 0)) ∧
      Tendsto (fun m ↦ eLpNorm (fun x ↦ tstarForm w₂ ψ₀ (βs m) x - γ x) 2
        (weightedVolume D w₁)) atTop (𝓝 0) ∧
      ∀ p, Tendsto (fun m ↦ eLpNorm (fun x ↦ dbarForm (βs m) p x - σ p x) 2
        (weightedVolume D w₃)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδD⟩ := hQ.exists_cthickening_subset_open hD hQD
  set K := cthickening (δ / 2) Q with hK
  have hKc : IsCompact K := hQ.cthickening
  have hKD : K ⊆ D := (cthickening_mono (by linarith) Q).trans hδD
  have hQK : Q ⊆ K := self_subset_cthickening Q
  obtain ⟨W₂, hW₂, hW₂e⟩ := exists_contDiff_eventuallyEq_nhdsSet hD hw₂ hKc hKD
  obtain ⟨W₁, hW₁, hW₁e⟩ := exists_contDiff_eventuallyEq_nhdsSet hD hw₁ hKc hKD
  have hW₂n : ∀ x ∈ K, W₂ =ᶠ[𝓝 x] w₂ := fun x hx ↦ hW₂e.filter_mono (nhds_le_nhdsSet hx)
  have hW₁n : ∀ x ∈ K, W₁ =ᶠ[𝓝 x] w₁ := fun x hx ↦ hW₁e.filter_mono (nhds_le_nhdsSet hx)
  have hW₂K : ∀ x ∈ K, W₂ x = w₂ x := fun x hx ↦ (hW₂n x hx).eq_of_nhds
  have hW₁K : ∀ x ∈ K, W₁ x = w₁ x := fun x hx ↦ (hW₁n x hx).eq_of_nhds
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_cast)
  -- the mollifiers
  set r : ℕ → ℝ := fun m ↦ δ / 4 * (1 / ((m : ℝ) + 1)) with hr
  have hrpos : ∀ m, 0 < r m := fun m ↦ by simp only [hr]; positivity
  have hrle : ∀ m, r m ≤ δ / 4 := fun m ↦ by
    simp only [hr]
    have : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    nlinarith
  let ρ : ℕ → ContDiffBump (0 : ComplexModel n) := fun m ↦
    ⟨r m / 2, r m, by linarith [hrpos m], by linarith [hrpos m]⟩
  have hρ0 : Tendsto (fun m ↦ (ρ m).rOut) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (δ / 4)
    rw [mul_zero] at h
    exact h
  have hball : ∀ m, ∀ x ∈ K, closedBall x (ρ m).rOut ⊆ D := fun m x hx ↦
    (closedBall_subset_cthickening hx _).trans ((cthickening_cthickening_subset (hrpos m).le
      (by linarith) Q).trans ((cthickening_mono (by linarith [hrle m]) Q).trans hδD))
  -- the data
  have hexp : ∀ W : ComplexModel n → ℝ, Continuous W →
      Continuous fun y ↦ ((Real.exp (-W y) : ℝ) : ℂ) := fun W hW ↦ by fun_prop
  set b : Fin n → ComplexModel n → ℂ := fun j y ↦ β j y * Real.exp (-W₂ y) with hb
  set c : ComplexModel n → ℂ := fun y ↦ γ y * Real.exp (-W₁ y) with hc
  set ζ : Fin n × Fin n → ComplexModel n → ℂ := fun p y ↦ σ p y * Real.exp (-W₂ y) -
    (dbarDir (coordVec p.1) (fun z ↦ (W₂ z : ℂ)) y * (β p.2 y * Real.exp (-W₂ y)) -
      dbarDir (coordVec p.2) (fun z ↦ (W₂ z : ℂ)) y * (β p.1 y * Real.exp (-W₂ y))) with hζ
  have hbL : ∀ j, MemLp (b j) 2 volume := fun j ↦
    memLp_mul_of_eq_zero_off hQ (hβ j) (hβQ j) (hexp W₂ hW₂.continuous)
  have hbQ : ∀ j, ∀ y ∉ Q, b j y = 0 := fun j y hy ↦ by simp [hb, hβQ j y hy]
  have hcL : MemLp c 2 volume := memLp_mul_of_eq_zero_off hQ hγ hγQ (hexp W₁ hW₁.continuous)
  have hdW : ∀ i, Continuous (dbarDir (coordVec i) fun z ↦ (W₂ z : ℂ)) := fun i ↦
    continuous_dbarDir (contDiff_ofReal_comp hW₂1)
  have hζL : ∀ p, MemLp (ζ p) 2 volume := fun p ↦ by
    have hdb : ∀ i l, MemLp (fun y ↦ dbarDir (coordVec i) (fun z ↦ (W₂ z : ℂ)) y *
        (β l y * Real.exp (-W₂ y))) 2 volume :=
      fun i l ↦ MemLp.ae_eq (Eventually.of_forall fun y ↦ mul_comm _ _)
        (memLp_mul_of_eq_zero_off hQ (hbL l) (hbQ l) (hdW i))
    exact (memLp_mul_of_eq_zero_off hQ (hσ p) (hσQ p) (hexp W₂ hW₂.continuous)).sub
      ((hdb p.1 p.2).sub (hdb p.2 p.1))
  set F : ℕ → Fin n → ComplexModel n → ℂ := fun m j ↦
    (ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b j with hF
  have hFs : ∀ m j, ContDiff ℝ ∞ (F m j) := fun m j ↦
    contDiff_bump_convolution (ρ m) ((hbL j).locallyIntegrable one_le_two)
  have hFsupp : ∀ m j, tsupport (F m j) ⊆ cthickening (δ / 4) Q := fun m j ↦ by
    have hbs : tsupport (b j) ⊆ Q := closure_minimal (fun y hy ↦ by_contra fun h ↦ hy (hbQ j y h))
      hQ.isClosed
    refine (tsupport_bump_convolution_subset (ρ m) (b j)).trans ?_
    refine (Set.add_subset_add_right hbs).trans ?_
    rw [hQ.add_closedBall_zero (hrpos m).le]
    exact cthickening_mono (hrle m) Q
  have hFK : ∀ m j, tsupport (F m j) ⊆ K := fun m j ↦
    (hFsupp m j).trans (cthickening_mono (by linarith) Q)
  set βs : ℕ → Fin n → ComplexModel n → ℂ := fun m j y ↦
    ((Real.exp (W₂ y) : ℝ) : ℂ) * F m j y with hβs
  have hβsK : ∀ m j, tsupport (βs m j) ⊆ K := fun m j ↦
    tsupport_mul_subset_right.trans (hFK m j)
  have hβs_test : ∀ m j, IsTestFunctionOn D (βs m j) := fun m j ↦
    ⟨(contDiff_ofReal_comp hW₂.exp).mul (hFs m j),
      hKc.of_isClosed_subset (isClosed_tsupport _) (hβsK m j), (hβsK m j).trans hKD⟩
  have hβs0 : ∀ m j, ∀ x ∉ K, βs m j x = 0 := fun m j x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hβsK m j h)
  have hβe : ∀ j y, β j y = ((Real.exp (W₂ y) : ℝ) : ℂ) * b j y := fun j y ↦ by
    have h1 : ((Real.exp (W₂ y) : ℝ) : ℂ) * ((Real.exp (-W₂ y) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    simp only [hb]
    linear_combination (-(β j y)) * h1
  have hnexp : ∀ y, ‖((Real.exp (W₂ y) : ℝ) : ℂ)‖ = Real.exp (W₂ y) := fun y ↦ by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ⟨βs, hβs_test, fun j ↦ ?_, ?_, fun p ↦ ?_⟩
  · obtain ⟨C, hC⟩ := exists_forall_exp_neg_le hKc hW₂.continuous.continuousOn
    refine tendsto_eLpNorm_weightedVolume_of_le hD hw₂.continuousOn hKc hKD (C := C)
      (g := fun m y ↦ F m j y - b j y) (fun m x hx ↦ ?_) (fun m x hx ↦ ?_)
      (tendsto_eLpNorm_bump_convolution_sub (hbL j) hρ0)
    · rw [hβs0 m j x hx, hβQ j x fun h ↦ hx (hQK h), sub_zero]
    · rw [hβe j x, show βs m j x = ((Real.exp (W₂ x) : ℝ) : ℂ) * F m j x from rfl, ← mul_sub,
        norm_mul, hnexp]
      exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)
  · obtain ⟨C, hC⟩ := exists_forall_exp_neg_le hKc (f := fun y ↦ W₂ y - ψ₀ y)
      (hW₂.continuous.continuousOn.sub (hψ.mono hKD))
    refine tendsto_eLpNorm_weightedVolume_of_le hD hw₁.continuousOn hKc hKD (C := C)
      (g := fun m y ↦ ((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] c) y - c y)
      (fun m x hx ↦ ?_) (fun m x hx ↦ ?_) (tendsto_eLpNorm_bump_convolution_sub hcL hρ0)
    · have h0 : tstarForm w₂ ψ₀ (βs m) x = 0 := by
        simp only [tstarForm]
        rw [Finset.sum_eq_zero fun j _ ↦
          deltaDir_eq_zero_of_notMem_tsupport fun h ↦ hx (hβsK m j h), mul_zero]
      rw [h0, hγQ x fun h ↦ hx (hQK h), sub_zero]
    · have hmoll : -∑ j, dDir (coordVec j) (F m j) x =
          ((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] c) x :=
        neg_sum_dDir_bump_convolution_eq hD hQ hQD hW₁.continuous hW₂.continuous
          (fun y hy ↦ hW₁K y (hQK hy)) (fun y hy ↦ hW₂K y (hQK hy)) hβQ hγQ hβ hγ hT (ρ m)
          (hball m x hx)
      have hδx : ∀ j, deltaDir (coordVec j) w₂ (βs m j) x =
          ((Real.exp (W₂ x) : ℝ) : ℂ) * dDir (coordVec j) (F m j) x := fun j ↦ by
        rw [deltaDir_congr_weight_of_eventuallyEq (hW₂n x hx)]
        exact deltaDir_exp_mul (hW₂1.differentiable one_ne_zero x)
          ((hFs m j).differentiable (by simp) x)
      have hts : tstarForm w₂ ψ₀ (βs m) x = ((Real.exp (-ψ₀ x) : ℝ) : ℂ) *
          ((Real.exp (W₂ x) : ℝ) : ℂ) *
            ((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] c) x := by
        simp only [tstarForm, hδx, ← Finset.mul_sum]
        rw [← hmoll]
        ring
      have hγx : γ x = ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ((Real.exp (W₂ x) : ℝ) : ℂ) * c x := by
        have h1 : ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ((Real.exp (W₂ x) : ℝ) : ℂ) *
            ((Real.exp (-W₁ x) : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add,
            hW₂K x hx, hW₁K x hx, hw x (hKD hx)]
          simp
        simp only [hc]
        linear_combination (-(γ x)) * h1
      rw [hts, hγx, ← mul_sub, norm_mul, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), ← Real.exp_add]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [show -ψ₀ x + W₂ x = W₂ x - ψ₀ x by ring]
      exact hC x hx
  · obtain ⟨j, k⟩ := p
    set ζjk := ζ (j, k) with hζjk
    set dj := dbarDir (coordVec j) fun z ↦ (W₂ z : ℂ) with hdj
    set dk := dbarDir (coordVec k) fun z ↦ (W₂ z : ℂ) with hdk
    have hcont : Continuous fun y ↦ Real.exp (W₂ y) * (‖dj y‖ + ‖dk y‖ + 1) := by
      have := hW₂.continuous; have := hdW j; have := hdW k; fun_prop
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
    have hmeasF : ∀ m i, AEStronglyMeasurable (fun y ↦ F m i y - b i y) volume := fun m i ↦
      (hFs m i).continuous.aestronglyMeasurable.sub (hbL i).1
    have hmeasZ : ∀ m, AEStronglyMeasurable (fun y ↦
        ((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζjk) y - ζjk y) volume :=
      fun m ↦ (contDiff_bump_convolution (ρ m) ((hζL (j, k)).locallyIntegrable one_le_two)).continuous.aestronglyMeasurable.sub
        (hζL (j, k)).1
    have hg : Tendsto (fun m ↦ eLpNorm (fun y ↦ ‖F m k y - b k y‖ + ‖F m j y - b j y‖ +
        ‖((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζjk) y - ζjk y‖) 2 volume)
        atTop (𝓝 0) := by
      refine tendsto_eLpNorm_add (f := fun m y ↦ ‖F m k y - b k y‖ + ‖F m j y - b j y‖)
        (g := fun m y ↦ ‖((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζjk) y -
          ζjk y‖) (fun m ↦ (hmeasF m k).norm.add (hmeasF m j).norm) (fun m ↦ (hmeasZ m).norm)
        ?_ ?_
      · refine tendsto_eLpNorm_add (f := fun m y ↦ ‖F m k y - b k y‖)
          (g := fun m y ↦ ‖F m j y - b j y‖) (fun m ↦ (hmeasF m k).norm)
          (fun m ↦ (hmeasF m j).norm) ?_ ?_
        · simpa only [eLpNorm_norm] using tendsto_eLpNorm_bump_convolution_sub (hbL k) hρ0
        · simpa only [eLpNorm_norm] using tendsto_eLpNorm_bump_convolution_sub (hbL j) hρ0
      · simpa only [eLpNorm_norm] using tendsto_eLpNorm_bump_convolution_sub (hζL (j, k)) hρ0
    refine tendsto_eLpNorm_weightedVolume_of_le hD hw₃ hKc hKD (C := C) (fun m x hx ↦ ?_)
      (fun m x hx ↦ ?_) hg
    · simp only [dbarForm]
      rw [dbarDir_eq_zero_of_notMem_tsupport fun h ↦ hx (hβsK m k h),
        dbarDir_eq_zero_of_notMem_tsupport fun h ↦ hx (hβsK m j h),
        hσQ _ x fun h ↦ hx (hQK h)]
      simp
    · have hmoll : dbarDir (coordVec j) (F m k) x - dbarDir (coordVec k) (F m j) x =
          ((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζjk) x :=
        dbarDir_bump_convolution_sub_eq hD hQ hW₂ hβQ hσQ hβ hσ hS (ρ m) (hball m x hx) j k
      have hd : ∀ i l, dbarDir (coordVec l) (βs m i) x = ((Real.exp (W₂ x) : ℝ) : ℂ) *
          (dbarDir (coordVec l) (fun z ↦ (W₂ z : ℂ)) x * F m i x +
            dbarDir (coordVec l) (F m i) x) := fun i l ↦
        dbarDir_exp_mul (hW₂1.differentiable one_ne_zero x) ((hFs m i).differentiable (by simp) x)
      have hσx : σ (j, k) x = ((Real.exp (W₂ x) : ℝ) : ℂ) *
          (ζjk x + (dj x * b k x - dk x * b j x)) := by
        have h1 : ((Real.exp (W₂ x) : ℝ) : ℂ) * ((Real.exp (-W₂ x) : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
            Complex.ofReal_one]
        simp only [hζjk, hζ, hb]
        linear_combination (-(σ (j, k) x)) * h1
      have hdiff : dbarForm (βs m) (j, k) x - σ (j, k) x = ((Real.exp (W₂ x) : ℝ) : ℂ) *
          (dj x * (F m k x - b k x) - dk x * (F m j x - b j x) +
            (((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζjk) x - ζjk x)) := by
        simp only [dbarForm]
        rw [hd, hd, hσx, ← hmoll]
        ring
      rw [hdiff]
      refine (norm_exp_mul_combo_le _ _ _ _ _ _).trans ?_
      rw [hnexp]
      have hg0 : 0 ≤ ‖F m k x - b k x‖ + ‖F m j x - b j x‖ +
          ‖((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζjk) x - ζjk x‖ := by
        positivity
      rw [Real.norm_of_nonneg hg0]
      exact mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans (hC x hx)) hg0

end Mollify

/-! ### Step 3: the diagonal argument -/

section Diagonal

variable {D : Set (ComplexModel n)}

theorem tendsto_eLpNorm_sub_of_approx {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    {μ : Measure α} {a b : ℕ → α → V} {f : α → V} {ε : ℕ → ℝ≥0∞}
    (ha : ∀ k, AEStronglyMeasurable (a k) μ) (hb : ∀ k, AEStronglyMeasurable (b k) μ)
    (hf : AEStronglyMeasurable f μ)
    (hab : ∀ k, eLpNorm (fun x ↦ a k x - b k x) 2 μ ≤ ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hbf : Tendsto (fun k ↦ eLpNorm (fun x ↦ b k x - f x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ a k x - f x) 2 μ) atTop (𝓝 0) := by
  have h := hε.add hbf
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    fun k ↦ ?_
  have e : (fun x ↦ a k x - f x) = fun x ↦ (a k x - b k x) + (b k x - f x) := by
    funext x; abel
  rw [e]
  exact (eLpNorm_add_le ((ha k).sub (hb k)) ((hb k).sub hf) one_le_two).trans
    (add_le_add (hab k) le_rfl)

theorem continuousOn_dDir_ofReal {v : ComplexModel n} {w : ComplexModel n → ℝ}
    (hD : IsOpen D) (hw : ContDiffOn ℝ ∞ w D) :
    ContinuousOn (dDir v fun y ↦ (w y : ℂ)) D := by
  have hc : ContDiffOn ℝ ∞ (fun y ↦ (w y : ℂ)) D :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hw
  have hf := hc.continuousOn_fderiv_of_isOpen hD (by norm_cast)
  have h1 := hf.clm_apply (continuousOn_const (c := v))
  have h2 := hf.clm_apply (continuousOn_const (c := I • v))
  unfold dDir
  exact ((h1.sub (continuousOn_const.mul h2)).div_const 2)

theorem continuousOn_tstarForm {w₂ ψ₀ : ComplexModel n → ℝ} (hD : IsOpen D)
    (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hψ : ContinuousOn ψ₀ D) {α : Fin n → ComplexModel n → ℂ}
    (hα : ∀ j, IsTestFunctionOn D (α j)) : ContinuousOn (tstarForm w₂ ψ₀ α) D := by
  have hd : ∀ j, ContinuousOn (deltaDir (coordVec j) w₂ (α j)) D := fun j ↦ by
    have h1 := continuous_dDir_of_contDiff (v := coordVec j) (isTestFunctionOn_contDiff_one (hα j))
    have h2 := continuousOn_dDir_ofReal (v := coordVec j) hD hw₂
    have h3 := (isTestFunctionOn_contDiff_one (hα j)).continuous
    exact h1.continuousOn.sub (h2.mul h3.continuousOn)
  have he : ContinuousOn (fun x ↦ ((Real.exp (-ψ₀ x) : ℝ) : ℂ)) D :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hψ.neg)
  unfold tstarForm
  exact (he.neg).mul (continuousOn_finsetSum _ fun j _ ↦ hd j)

end Diagonal

end Density

open Density in
/-- **Density of test forms for Hörmander's three weights** (Hörmander, *An introduction to
complex analysis in several variables*, Lemma 4.1.3).

Let `D ⊆ ℂⁿ` be open, `w₃, ψ₀` smooth on `D`, `w₂ = w₃ - ψ₀`, `w₁ = w₃ - 2ψ₀`, and let `η k` be
smooth cutoffs with values in `[0, 1]`, compactly supported in `D`, eventually `1` near each
point of `D`, with `‖Dη_k‖² ≤ e^{ψ₀}` on `D`.  If `β ∈ L²_{(0,1)}(e^{-w₂})` has weak
`T* β = γ ∈ L²(e^{-w₁})` and weak `∂̄ β = σ ∈ L²(e^{-w₃})`, then there are test forms `βs m`
with `βs m → β`, `T* βs m → γ` and `∂̄ βs m → σ` in the respective weighted `L²` spaces. -/
theorem exists_testForm_tendsto {D : Set (ComplexModel n)} (hD : IsOpen D)
    {w₃ ψ₀ : ComplexModel n → ℝ} (hw₃ : ContDiffOn ℝ ∞ w₃ D) (hψ₀ : ContDiffOn ℝ ∞ ψ₀ D)
    {η : ℕ → ComplexModel n → ℝ} (hη : ∀ k, ContDiff ℝ ∞ (η k))
    (hηc : ∀ k, HasCompactSupport (η k)) (hηD : ∀ k, tsupport (η k) ⊆ D)
    (hη01 : ∀ k x, 0 ≤ η k x ∧ η k x ≤ 1)
    (hη1 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    (hηgrad : ∀ k, ∀ x ∈ D, ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x))
    {β : Fin n → ComplexModel n → ℂ} {γ : ComplexModel n → ℂ}
    {σ : Fin n × Fin n → ComplexModel n → ℂ}
    (hβ : ∀ j, MemLp (β j) 2 (weightedVolume D fun x ↦ w₃ x - ψ₀ x))
    (hγ : MemLp γ 2 (weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x))
    (hσ : ∀ p, MemLp (σ p) 2 (weightedVolume D w₃))
    (hT : ∀ g, IsTestFunctionOn D g →
      ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * β j x * Real.exp (-(w₃ x - ψ₀ x)) =
        ∫ x in D, conj (g x) * γ x * Real.exp (-(w₃ x - 2 * ψ₀ x)))
    (hS : ∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (β k x * dbarDir (coordVec j) h x - β j x * dbarDir (coordVec k) h x) =
        -∫ x, σ (j, k) x * h x) :
    ∃ βs : ℕ → Fin n → ComplexModel n → ℂ, (∀ m j, IsTestFunctionOn D (βs m j)) ∧
      (∀ j, Tendsto (fun m ↦ eLpNorm (fun x ↦ βs m j x - β j x) 2
        (weightedVolume D fun x ↦ w₃ x - ψ₀ x)) atTop (𝓝 0)) ∧
      Tendsto (fun m ↦ eLpNorm (fun x ↦ tstarForm (fun x ↦ w₃ x - ψ₀ x) ψ₀ (βs m) x - γ x) 2
        (weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x)) atTop (𝓝 0) ∧
      ∀ p, Tendsto (fun m ↦ eLpNorm (fun x ↦ dbarForm (βs m) p x - σ p x) 2
        (weightedVolume D w₃)) atTop (𝓝 0) := by
  set w₂ : ComplexModel n → ℝ := fun x ↦ w₃ x - ψ₀ x with hw₂def
  set w₁ : ComplexModel n → ℝ := fun x ↦ w₃ x - 2 * ψ₀ x with hw₁def
  have hw₂ : ContDiffOn ℝ ∞ w₂ D := hw₃.sub hψ₀
  have hw₁ : ContDiffOn ℝ ∞ w₁ D := hw₃.sub (contDiffOn_const.mul hψ₀)
  have hw₁c := hw₁.continuousOn
  have hw₂c := hw₂.continuousOn
  have hw₃c := hw₃.continuousOn
  have hψc := hψ₀.continuousOn
  have hw21 : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x := fun x _ ↦ by simp only [hw₂def, hw₁def]; ring
  have hw32 : ∀ x ∈ D, w₃ x = w₂ x + ψ₀ x := fun x _ ↦ by simp only [hw₂def]; ring
  have hη1' : ∀ k, ContDiff ℝ 1 (η k) := fun k ↦ (hη k).of_le (by norm_cast)
  have hηC : ∀ k, Continuous fun x ↦ (η k x : ℂ) := fun k ↦ by
    have := (hη k).continuous; fun_prop
  -- the cut-off data
  set βk : ℕ → Fin n → ComplexModel n → ℂ := fun k j x ↦ (η k x : ℂ) * β j x with hβk
  set γk : ℕ → ComplexModel n → ℂ := fun k ↦ cutoffTstar ψ₀ (η k) β γ with hγk
  set σk : ℕ → Fin n × Fin n → ComplexModel n → ℂ := fun k ↦ cutoffDbar (η k) β σ with hσk
  have hη0 : ∀ k, ∀ x ∉ tsupport (η k), η k x = 0 := fun k x hx ↦
    image_eq_zero_of_notMem_tsupport hx
  have hβm : ∀ j, AEStronglyMeasurable (β j) (volume.restrict D) := fun j ↦
    (aestronglyMeasurable_weightedVolume_iff hD hw₂c).mp (hβ j).1
  have happrox : ∀ k, ∃ α : Fin n → ComplexModel n → ℂ, (∀ j, IsTestFunctionOn D (α j)) ∧
      (∀ j, eLpNorm (fun x ↦ α j x - βk k j x) 2 (weightedVolume D w₂) ≤
        ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) ∧
      eLpNorm (fun x ↦ tstarForm w₂ ψ₀ α x - γk k x) 2 (weightedVolume D w₁) ≤
        ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ∧
      ∀ p, eLpNorm (fun x ↦ dbarForm α p x - σk k p x) 2 (weightedVolume D w₃) ≤
        ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro k
    have hQc := hηc k
    have hQD := hηD k
    have hdθ : ∀ i, Continuous (dDir (coordVec i) fun y ↦ (η k y : ℂ)) := fun i ↦
      continuous_dDir_of_contDiff (contDiff_ofReal_comp (hη1' k))
    have hdbθ : ∀ i, Continuous (dbarDir (coordVec i) fun y ↦ (η k y : ℂ)) := fun i ↦
      continuous_dbarDir (contDiff_ofReal_comp (hη1' k))
    have hβL : ∀ j, MemLp (βk k j) 2 volume := fun j ↦
      memLp_mul_of_weightedVolume hD hw₂c hQc hQD (hβ j) (hηC k).continuousOn
        fun x hx ↦ by simp [hη0 k x hx]
    have hγL : MemLp (γk k) 2 volume := by
      have e : γk k = fun x ↦ (η k x : ℂ) * γ x - ∑ j, (((Real.exp (-ψ₀ x) : ℝ) : ℂ) *
          dDir (coordVec j) (fun y ↦ (η k y : ℂ)) x) * β j x := by
        funext x; simp only [hγk, cutoffTstar, Finset.mul_sum]; congr 1
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      rw [e]
      refine (memLp_mul_of_weightedVolume hD hw₁c hQc hQD hγ (hηC k).continuousOn
        fun x hx ↦ by simp [hη0 k x hx]).sub (memLp_finsetSum _ fun j _ ↦ ?_)
      exact memLp_mul_of_weightedVolume hD hw₂c hQc hQD (hβ j)
        ((Complex.continuous_ofReal.comp_continuousOn
          (Real.continuous_exp.comp_continuousOn hψc.neg)).mono hQD |>.mul (hdθ j).continuousOn)
        fun x hx ↦ by simp [dDir_eq_zero_of_notMem_tsupport_real hx]
    have hσL : ∀ p, MemLp (σk k p) 2 volume := fun p ↦ by
      have e : σk k p = fun x ↦ (η k x : ℂ) * σ p x +
          (dbarDir (coordVec p.1) (fun y ↦ (η k y : ℂ)) x * β p.2 x -
            dbarDir (coordVec p.2) (fun y ↦ (η k y : ℂ)) x * β p.1 x) := rfl
      rw [e]
      refine (memLp_mul_of_weightedVolume hD hw₃c hQc hQD (hσ p) (hηC k).continuousOn
        fun x hx ↦ by simp [hη0 k x hx]).add ((memLp_mul_of_weightedVolume hD hw₂c hQc hQD
          (hβ p.2) (hdbθ p.1).continuousOn fun x hx ↦ by
            simp [dbarDir_eq_zero_of_notMem_tsupport_real hx]).sub
        (memLp_mul_of_weightedVolume hD hw₂c hQc hQD (hβ p.1) (hdbθ p.2).continuousOn
          fun x hx ↦ by simp [dbarDir_eq_zero_of_notMem_tsupport_real hx]))
    obtain ⟨βs, htest, h1, h2, h3⟩ := exists_testForm_tendsto_of_compact hD hQc hQD hw₁ hw₂
      hw₃c hψc hw21 (β := βk k) (γ := γk k) (σ := σk k)
      (fun j x hx ↦ by simp [hβk, hη0 k x hx])
      (fun x hx ↦ by
        simp [hγk, cutoffTstar, hη0 k x hx, dDir_eq_zero_of_notMem_tsupport_real hx])
      (fun p x hx ↦ by
        simp [hσk, cutoffDbar, hη0 k x hx, dbarDir_eq_zero_of_notMem_tsupport_real hx])
      hβL hγL hσL
      (fun g hg ↦ weakTstar_cutoff hD hw₁c hw₂c hw21 (hη k) hβ hγ hT hg)
      (fun h hh j l ↦ weakDbar_cutoff hD hw₂c hw₃c (hη k) hβ hσ hS hh j l)
    have hε : (0 : ℝ≥0∞) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
    have ev1 := (Filter.eventually_all.mpr fun j ↦ ENNReal.tendsto_nhds_zero.mp (h1 j) _ hε)
    have ev2 := ENNReal.tendsto_nhds_zero.mp h2 _ hε
    have ev3 := (Filter.eventually_all.mpr fun p ↦ ENNReal.tendsto_nhds_zero.mp (h3 p) _ hε)
    obtain ⟨m, hm1, hm2, hm3⟩ := (ev1.and (ev2.and ev3)).exists
    exact ⟨βs m, htest m, hm1, hm2, hm3⟩
  choose α hαtest hα1 hα2 hα3 using happrox
  have hε : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  refine ⟨α, hαtest, fun j ↦ ?_, ?_, fun p ↦ ?_⟩
  · refine tendsto_eLpNorm_sub_of_approx (b := fun k ↦ βk k j)
      (fun k ↦ (hαtest k j).1.continuous.aestronglyMeasurable)
      (fun k ↦ (hηC k).aestronglyMeasurable.mul (hβ j).1) (hβ j).1 (fun k ↦ hα1 k j) hε ?_
    exact tendsto_eLpNorm_cutoff_mul_sub hD hw₂c (fun k ↦ (hη k).continuous) hη01 hη1 (hβ j)
  · refine tendsto_eLpNorm_sub_of_approx (b := γk)
      (fun k ↦ (aestronglyMeasurable_weightedVolume_iff hD hw₁c).mpr
        ((continuousOn_tstarForm hD hw₂ hψc (hαtest k)).aestronglyMeasurable hD.measurableSet))
      (fun k ↦ (aestronglyMeasurable_weightedVolume_iff hD hw₁c).mpr ?_) hγ.1 hα2 hε
      (tendsto_eLpNorm_cutoffTstar_sub hD hw₁c hw₂c hψc hw21 hη hη01 hη1 hηgrad hβ hγ)
    have he : AEStronglyMeasurable (fun x ↦ ((Real.exp (-ψ₀ x) : ℝ) : ℂ)) (volume.restrict D) :=
      (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn hψc.neg)).aestronglyMeasurable hD.measurableSet
    exact ((hηC k).aestronglyMeasurable.mul
      ((aestronglyMeasurable_weightedVolume_iff hD hw₁c).mp hγ.1)).sub
      (he.mul (Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦
        (continuous_dDir_of_contDiff (contDiff_ofReal_comp (hη1' k))).aestronglyMeasurable.mul
          (hβm j)))
  · refine tendsto_eLpNorm_sub_of_approx (b := fun k ↦ σk k p)
      (fun k ↦ ((continuous_dbarDir (isTestFunctionOn_contDiff_one (hαtest k p.2))).sub
        (continuous_dbarDir (isTestFunctionOn_contDiff_one (hαtest k p.1)))).aestronglyMeasurable)
      (fun k ↦ (aestronglyMeasurable_weightedVolume_iff hD hw₃c).mpr ?_) (hσ p).1
      (fun k ↦ hα3 k p) hε
      (tendsto_eLpNorm_cutoffDbar_sub hD hw₂c hw₃c hw32 hη hη01 hη1 hηgrad hβ hσ p)
    have hb : ∀ i l, AEStronglyMeasurable (fun x ↦
        dbarDir (coordVec i) (fun y ↦ (η k y : ℂ)) x * β l x) (volume.restrict D) := fun i l ↦
      (continuous_dbarDir (contDiff_ofReal_comp (hη1' k))).aestronglyMeasurable.mul (hβm l)
    exact ((hηC k).aestronglyMeasurable.mul
      ((aestronglyMeasurable_weightedVolume_iff hD hw₃c).mp (hσ p).1)).add
      ((hb p.1 p.2).sub (hb p.2 p.1))

end

end Hironaka.Hormander
