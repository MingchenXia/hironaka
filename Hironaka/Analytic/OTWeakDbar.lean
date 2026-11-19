import Hironaka.Analytic.HormanderInterface
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

/-!
# Weak `∂̄` for functions smooth on an open set

Tools for applying Hörmander's estimate (`Hironaka.HormanderInterface`) to functions which are
only smooth on the domain `D`.

* `dbarDir_eq_zero_of_differentiableAt`: holomorphic functions have vanishing `∂̄`.
* `integral_mul_dbarDir_eq_neg_of_contDiffOn`: integration by parts against a test function
  supported in `D`, for `a` of class `C¹` on `D` only.
* `weakDbarEq_of_contDiffOn`, `weakDbarClosed_of_contDiffOn`: the classical `∂̄` of such a
  function is its weak `∂̄`, and is weakly `∂̄`-closed.
* `integral_mul_dbarDir_eq_zero_of_coord`: weak `∂̄`-closedness in the coordinate directions
  gives it in every direction.
* Weighted `L²` helpers: `memLp_weightedVolume_iff`, `locallyIntegrableOn_of_memLp_weightedVolume`.
-/

open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff ComplexConjugate ENNReal

namespace Hironaka.OTChen

noncomputable section

open CauchyGreen Hormander

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Holomorphic functions have vanishing `∂̄`. -/
theorem dbarDir_eq_zero_of_differentiableAt {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x)
    (v : E) : dbarDir v f x = 0 := by
  have h : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ := hf.fderiv_restrictScalars ℝ
  simp only [dbarDir, h, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  rw [← mul_assoc, I_mul_I]
  ring

omit [NormedSpace ℂ E] in
theorem eventually_eq_zero_of_notMem_tsupport {F : Type*} [NormedAddCommGroup F]
    {h : E → F} {y : E} (hy : y ∉ tsupport h) : h =ᶠ[𝓝 y] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp hy

theorem tsupport_dbarDir_subset (v : E) (h : E → ℂ) : tsupport (dbarDir v h) ⊆ tsupport h := by
  intro y hy
  by_contra hny
  have hev := eventually_eq_zero_of_notMem_tsupport hny
  have hz : dbarDir v h =ᶠ[𝓝 y] 0 := by
    filter_upwards [hev.eventually_nhds] with z hz
    have hz' : fderiv ℝ h z = 0 := by
      rw [(show h =ᶠ[𝓝 z] fun _ ↦ 0 from hz).fderiv_eq]
      simp
    simp [dbarDir, hz']
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hy

/-- A product `a h` with `a` smooth on an open set containing `tsupport h` is smooth. -/
theorem contDiff_mul_of_tsupport_subset {D : Set E} (hD : IsOpen D) {a h : E → ℂ}
    {k : WithTop ℕ∞} (ha : ContDiffOn ℝ k a D) (hh : ContDiff ℝ k h) (hts : tsupport h ⊆ D) :
    ContDiff ℝ k (fun y ↦ a y * h y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ D
  · exact ((ha y hy).contDiffAt (hD.mem_nhds hy)).mul hh.contDiffAt
  · have hny : y ∉ tsupport h := fun h' ↦ hy (hts h')
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [eventually_eq_zero_of_notMem_tsupport hny] with z hz
    simp [hz]

omit [NormedSpace ℂ E] in
/-- A product `a h` with `a` continuous on an open set containing `tsupport h` is continuous. -/
theorem continuous_mul_of_tsupport_subset {D : Set E} (hD : IsOpen D) {a h : E → ℂ}
    (ha : ContinuousOn a D) (hh : Continuous h) (hts : tsupport h ⊆ D) :
    Continuous (fun y ↦ a y * h y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ D
  · exact ((ha y hy).continuousAt (hD.mem_nhds hy)).mul hh.continuousAt
  · have hny : y ∉ tsupport h := fun h' ↦ hy (hts h')
    apply (continuousAt_const (y := (0 : ℂ))).congr
    filter_upwards [eventually_eq_zero_of_notMem_tsupport hny] with z hz
    simp [hz]

theorem continuousOn_dbarDir_of_contDiffOn {D : Set E} (hD : IsOpen D) {a : E → ℂ}
    (ha : ContDiffOn ℝ 1 a D) (v : E) : ContinuousOn (dbarDir v a) D := by
  have hc : ContinuousOn (fderiv ℝ a) D := ha.continuousOn_fderiv_of_isOpen hD le_rfl
  have h1 : ContinuousOn (fun x ↦ fderiv ℝ a x v) D := hc.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun x ↦ fderiv ℝ a x (I • v)) D := hc.clm_apply continuousOn_const
  unfold dbarDir
  exact (h1.add (continuousOn_const.mul h2)).div_const _

theorem continuous_dbarDir' {v : E} {a : E → ℂ} (ha : ContDiff ℝ 1 a) :
    Continuous (dbarDir v a) :=
  (contDiff_dbarDir (k := 0) (by simpa using ha)).continuous

variable [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Integration by parts for `∂̄` on an open set.** -/
theorem integral_mul_dbarDir_eq_neg_of_contDiffOn {D : Set E} (hD : IsOpen D) {a h : E → ℂ}
    (ha : ContDiffOn ℝ 1 a D) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (hts : tsupport h ⊆ D) (v : E) :
    ∫ x, a x * dbarDir v h x ∂μ = -∫ x, dbarDir v a x * h x ∂μ := by
  set b : E → ℂ := fun y ↦ a y * h y with hb
  have hbd : ContDiff ℝ 1 b := contDiff_mul_of_tsupport_subset hD ha hh hts
  have hbc : HasCompactSupport b := hc.mul_left
  have h0 := integral_mul_dbarDir_eq_neg (μ := μ) (f := fun _ ↦ (1 : ℂ)) (g := b)
    contDiff_const hbd (Or.inr hbc) v
  simp only [one_mul, dbarDir_const, zero_mul, integral_zero, neg_zero] at h0
  have hpt : ∀ y, dbarDir v b y = dbarDir v a y * h y + a y * dbarDir v h y := by
    intro y
    by_cases hy : y ∈ D
    · exact dbarDir_mul ((ha.differentiableOn one_ne_zero y hy).differentiableAt (hD.mem_nhds hy))
        (hh.differentiable one_ne_zero y)
    · have hny : y ∉ tsupport h := fun h' ↦ hy (hts h')
      have hbz : b =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [eventually_eq_zero_of_notMem_tsupport hny] with z hz
        simp [hb, hz]
      have hhz : h y = 0 := image_eq_zero_of_notMem_tsupport hny
      have hdz : dbarDir v h y = 0 :=
        image_eq_zero_of_notMem_tsupport fun h' ↦ hny (tsupport_dbarDir_subset v h h')
      rw [dbarDir_congr hbz, dbarDir_const, hhz, hdz]
      ring
  have hi1 : Integrable (fun y ↦ dbarDir v a y * h y) μ :=
    (continuous_mul_of_tsupport_subset hD (continuousOn_dbarDir_of_contDiffOn hD ha v)
      hh.continuous hts).integrable_of_hasCompactSupport hc.mul_left
  have hi2 : Integrable (fun y ↦ a y * dbarDir v h y) μ :=
    (continuous_mul_of_tsupport_subset hD (ha.continuousOn)
      (continuous_dbarDir' hh) ((tsupport_dbarDir_subset v h).trans hts)).integrable_of_hasCompactSupport
      (hasCompactSupport_dbarDir hc).mul_left
  simp only [hpt] at h0
  rw [integral_add hi1 hi2] at h0
  linear_combination h0

end General

variable {n : ℕ}

theorem isTestFunctionOn_dbarDir {D : Set (ComplexModel n)} {h : ComplexModel n → ℂ}
    (hh : IsTestFunctionOn D h) (v : ComplexModel n) : IsTestFunctionOn D (dbarDir v h) := by
  obtain ⟨h1, h2, h3⟩ := hh
  refine ⟨?_, hasCompactSupport_dbarDir h2, (tsupport_dbarDir_subset v h).trans h3⟩
  rw [contDiff_infty] at h1 ⊢
  intro k
  exact contDiff_dbarDir (h1 (k + 1))

/-- The classical `∂̄` of a `C¹` function on `D` is its weak `∂̄`. -/
theorem weakDbarEq_of_contDiffOn {D : Set (ComplexModel n)} (hD : IsOpen D)
    {a : ComplexModel n → ℂ} (ha : ContDiffOn ℝ 1 a D) :
    WeakDbarEq D a (fun j ↦ dbarDir (coordVec j) a) := by
  intro h hh j
  exact integral_mul_dbarDir_eq_neg_of_contDiffOn hD ha (hh.1.of_le (WithTop.coe_le_coe.mpr le_top)) hh.2.1 hh.2.2 _

/-- The classical `∂̄` of a `C¹` function on `D` is weakly `∂̄`-closed. -/
theorem weakDbarClosed_of_contDiffOn {D : Set (ComplexModel n)} (hD : IsOpen D)
    {a : ComplexModel n → ℂ} (ha : ContDiffOn ℝ 1 a D) :
    WeakDbarClosed D (fun j ↦ dbarDir (coordVec j) a) := by
  intro h hh j k
  have hj := isTestFunctionOn_dbarDir hh (coordVec j)
  have hk := isTestFunctionOn_dbarDir hh (coordVec k)
  have e1 := integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hD ha
    (hj.1.of_le (WithTop.coe_le_coe.mpr le_top)) hj.2.1 hj.2.2 (coordVec k)
  have e2 := integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hD ha
    (hk.1.of_le (WithTop.coe_le_coe.mpr le_top)) hk.2.1 hk.2.2 (coordVec j)
  have hcomm : ∀ x, dbarDir (coordVec k) (dbarDir (coordVec j) h) x =
      dbarDir (coordVec j) (dbarDir (coordVec k) h) x := fun x ↦
    dbarDir_dbarDir_comm (hh.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  simp only [hcomm] at e1
  have hi : ∀ i l : Fin n, Integrable (fun x ↦ dbarDir (coordVec i) a x *
      dbarDir (coordVec l) h x) := fun i l ↦
    (continuous_mul_of_tsupport_subset hD (continuousOn_dbarDir_of_contDiffOn hD ha _)
      (continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top)))
      ((tsupport_dbarDir_subset _ h).trans hh.2.2)).integrable_of_hasCompactSupport
      (hasCompactSupport_dbarDir hh.2.1).mul_left
  rw [integral_sub (hi k j) (hi j k)]
  linear_combination e1 - e2

/-- Integrability of a locally integrable function against a continuous function with compact
support inside the domain. -/
theorem integrable_mul_of_locallyIntegrableOn {D : Set (ComplexModel n)}
    {F h : ComplexModel n → ℂ} (hF : LocallyIntegrableOn F D) (hh : Continuous h)
    (hc : HasCompactSupport h) (hts : tsupport h ⊆ D) :
    Integrable (fun x ↦ F x * h x) := by
  have hK : IntegrableOn F (tsupport h) := hF.integrableOn_compact_subset hts hc
  have h1 : IntegrableOn (fun x ↦ F x * h x) (tsupport h) :=
    hK.mul_continuousOn hh.continuousOn hc
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro x hx
  by_contra hnx
  exact hx (by simp [image_eq_zero_of_notMem_tsupport hnx])

theorem sum_smul_coordVec (v : ComplexModel n) : ∑ j, v j • coordVec j = v := by
  ext i
  simp [coordVec, Pi.single_apply]

/-- Weak `∂̄`-closedness in the coordinate directions gives it in every direction. -/
theorem integral_mul_dbarDir_eq_zero_of_coord {D : Set (ComplexModel n)}
    {F : ComplexModel n → ℂ} (hF : LocallyIntegrableOn F D)
    (hcoord : ∀ h, IsTestFunctionOn D h → ∀ j, ∫ x, F x * dbarDir (coordVec j) h x = 0) :
    ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ D →
      ∀ v : ComplexModel n, ∫ x, F x * dbarDir v g x = 0 := by
  intro g hg hc hts v
  have hpt : ∀ x, F x * dbarDir v g x = ∑ j, conj (v j) * (F x * dbarDir (coordVec j) g x) := by
    intro x
    conv_lhs => rw [← sum_smul_coordVec v]
    rw [dbarDir_sum_dir, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp only [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [integral_const_mul, hcoord g ⟨hg, hc, hts⟩ j, mul_zero]
  · intro j _
    exact (integrable_mul_of_locallyIntegrableOn hF (continuous_dbarDir' (hg.of_le (WithTop.coe_le_coe.mpr le_top)))
      (hasCompactSupport_dbarDir hc) ((tsupport_dbarDir_subset _ g).trans hts)).const_mul _

/-! ### Weighted `L²` -/

theorem aemeasurable_weight {D : Set (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : AEMeasurable w (volume.restrict D)) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (Real.exp (-w x))) (volume.restrict D) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable hw.neg)

theorem aestronglyMeasurable_of_memLp_weightedVolume {D : Set (ComplexModel n)}
    {w : ComplexModel n → ℝ} (hw : AEMeasurable w (volume.restrict D)) {p : ℝ≥0∞}
    {u : ComplexModel n → ℂ} (hu : MemLp u p (weightedVolume D w)) :
    AEStronglyMeasurable u (volume.restrict D) := by
  refine hu.1.mono_ac (withDensity_absolutelyContinuous' (aemeasurable_weight hw) ?_)
  exact Eventually.of_forall fun x ↦ by simp [Real.exp_pos]

/-- `L²(D, e^{-w})` membership as integrability of `|u|² e^{-w}`. -/
theorem memLp_weightedVolume_iff {D : Set (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : AEMeasurable w (volume.restrict D)) {u : ComplexModel n → ℂ}
    (hu : AEStronglyMeasurable u (volume.restrict D)) :
    MemLp u 2 (weightedVolume D w) ↔
      Integrable (fun x ↦ ‖u x‖ ^ 2 * Real.exp (-w x)) (volume.restrict D) := by
  rw [weightedVolume,
    memLp_two_iff_integrable_sq_norm (hu.mono_ac (withDensity_absolutelyContinuous _ _)),
    integrable_withDensity_iff_integrable_smul₀' (aemeasurable_weight hw)
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  ring

theorem integrable_of_memLp_weightedVolume {D : Set (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : AEMeasurable w (volume.restrict D)) {u : ComplexModel n → ℂ}
    (hu : MemLp u 2 (weightedVolume D w)) :
    Integrable (fun x ↦ ‖u x‖ ^ 2 * Real.exp (-w x)) (volume.restrict D) :=
  (memLp_weightedVolume_iff hw (aestronglyMeasurable_of_memLp_weightedVolume hw hu)).mp hu

/-- Weighted `L²` functions with a continuous weight are locally integrable. -/
theorem locallyIntegrableOn_of_memLp_weightedVolume {D : Set (ComplexModel n)} (hD : IsOpen D)
    {w : ComplexModel n → ℝ} (hw : ContinuousOn w D) {u : ComplexModel n → ℂ}
    (hu : MemLp u 2 (weightedVolume D w)) : LocallyIntegrableOn u D := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD x hx
  have hcb : closedBall x (r / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨y, -, hy⟩ := (isCompact_closedBall x (r / 2)).exists_isMinOn
    (nonempty_closedBall.mpr (by linarith)) ((hw.mono hcb).neg.rexp)
  set c := Real.exp (-w y) with hc
  have hcpos : 0 < c := Real.exp_pos _
  refine ⟨ball x (r / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by linarith)), ?_⟩
  have hle : volume.restrict (ball x (r / 2)) ≤ ENNReal.ofReal c⁻¹ • weightedVolume D w := by
    refine Measure.le_iff.mpr fun s hs ↦ ?_
    rw [Measure.restrict_apply hs, Measure.smul_apply, weightedVolume,
      withDensity_apply _ hs, Measure.restrict_restrict hs, smul_eq_mul]
    have h1 : ∫⁻ z in s ∩ ball x (r / 2), ENNReal.ofReal c ≤
        ∫⁻ z in s ∩ D, ENNReal.ofReal (Real.exp (-w z)) := by
      calc ∫⁻ z in s ∩ ball x (r / 2), ENNReal.ofReal c
          ≤ ∫⁻ z in s ∩ ball x (r / 2), ENNReal.ofReal (Real.exp (-w z)) := by
            refine setLIntegral_mono' (hs.inter measurableSet_ball) fun z hz ↦ ?_
            exact ENNReal.ofReal_le_ofReal (hy (ball_subset_closedBall hz.2))
        _ ≤ _ := lintegral_mono_set (inter_subset_inter_right _
            (ball_subset_closedBall.trans hcb))
    rw [setLIntegral_const] at h1
    calc volume (s ∩ ball x (r / 2))
        = ENNReal.ofReal c⁻¹ * (volume (s ∩ ball x (r / 2)) * ENNReal.ofReal c) := by
          rw [mul_comm (volume _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            inv_mul_cancel₀ hcpos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr; rw [mul_comm]; exact h1
  have h2 : MemLp u 2 (volume.restrict (ball x (r / 2))) :=
    hu.of_measure_le_smul ENNReal.ofReal_ne_top hle
  have : IsFiniteMeasure (volume.restrict (ball x (r / 2))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact h2.integrable one_le_two

end

end Hironaka.OTChen
