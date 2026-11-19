import Hironaka.Analytic.WirtingerCalculus
import Hironaka.Analytic.MollifierL2
import Hironaka.Analytic.HolomorphicNormalFamilies
import Hironaka.Analytic.PotentialTheory.BallRotation
import Mathlib.Analysis.Complex.MeanValue

set_option autoImplicit false

/-!
# Weyl's lemma for `∂̄`

A locally integrable function on an open set of `ℂⁿ` whose weak Wirtinger derivatives
`∂̄_v` all vanish agrees almost everywhere with a holomorphic function.

The proof mollifies: mollifications are smooth and, by commuting weak derivatives with
convolution, `∂̄`-closed, hence holomorphic away from the boundary.  The sub-mean-value
inequality for `‖h‖` on balls (from the circle mean value property along complex lines and
rotation invariance of Haar measure) bounds them uniformly by the `L¹` norm; Montel's theorem
gives a locally uniform limit, which is holomorphic and equals the function almost everywhere
by Lebesgue differentiation.  Local representatives are glued by continuity.
-/

noncomputable section

open Set Filter Metric MeasureTheory Complex ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution Real

namespace Hironaka

open CauchyGreen
section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A real-differentiable function whose Wirtinger derivatives `∂̄_v` all vanish at a point is
complex differentiable there. -/
theorem differentiableAt_complex_of_dbarDir_eq_zero [FiniteDimensional ℂ E] {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h : ∀ v, dbarDir v f x = 0) :
    DifferentiableAt ℂ f x := by
  set D := fderiv ℝ f x with hD
  have hI : ∀ v, D (I • v) = I * D v := by
    intro v
    have e := h v
    simp only [dbarDir, div_eq_zero_iff, two_ne_zero, or_false] at e
    linear_combination (-I) * e + D (I • v) * I_sq
  refine (differentiableAt_iff_restrictScalars ℝ hf).2 ⟨
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun c v ↦ ?_
      cont := D.continuous }, ?_⟩
  · have hc : c • v = c.re • v + c.im • (I • v) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [hc, D.map_add, D.map_smul, D.map_smul, hI]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [Complex.real_smul]
    ring
  · ext v
    rfl

/-- Circle mean value inequality along a complex line through the centre of a ball. -/
theorem ofReal_two_pi_mul_enorm_le_lintegral_circle {h : E → ℂ} {a v : E} {R : ℝ}
    (hh : DifferentiableOn ℂ h (ball a R)) (hv : ‖v‖ < R) :
    ENNReal.ofReal (2 * π) * ‖h a‖ₑ ≤
      ∫⁻ t in Ioc 0 (2 * π), ‖h (a + circleMap 0 1 t • v)‖ₑ := by
  set g : ℂ → ℂ := fun z ↦ h (a + z • v) with hg
  have hgd : DifferentiableOn ℂ g (closedBall 0 1) := by
    intro z hz
    have hz' : a + z • v ∈ ball a R := by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      calc ‖z‖ * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
        _ < R := by simpa using hv
    exact ((hh.differentiableAt (isOpen_ball.mem_nhds hz')).comp z
      ((differentiableAt_const a).add (differentiableAt_id.smul_const v))).differentiableWithinAt
  have hdc : DiffContOnCl ℂ g (ball 0 |1|) := by
    rw [abs_one]
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ one_ne_zero]
  have hmean := hdc.circleAverage
  rw [Real.circleAverage_def] at hmean
  have hint : ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 1 θ) = (2 * π : ℝ) • h a := by
    have h2π : (2 * π : ℝ) ≠ 0 := by positivity
    rw [← inv_smul_eq_iff₀ h2π, hmean]
    simp [g]
  calc ENNReal.ofReal (2 * π) * ‖h a‖ₑ = ‖(2 * π : ℝ) • h a‖ₑ := by
        rw [enorm_smul, Real.enorm_of_nonneg (by positivity)]
    _ = ‖∫ θ in Ioc 0 (2 * π), g (circleMap 0 1 θ)‖ₑ := by
        rw [← hint, intervalIntegral.integral_of_le (by positivity)]
    _ ≤ _ := enorm_integral_le_lintegral_enorm _

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℂ E]

/-- **Sub-mean-value inequality** for the modulus of a holomorphic function on a ball, with
respect to any Haar measure. -/
theorem measure_ball_mul_enorm_le_lintegral_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    {h : E → ℂ} (hc : Continuous h) {a : E} {R : ℝ} (hh : DifferentiableOn ℂ h (ball a R)) :
    μ (ball 0 R) * ‖h a‖ₑ ≤ ∫⁻ x in ball a R, ‖h x‖ₑ ∂μ := by
  have hcont : Continuous (fun p : E × ℝ ↦ ‖h (a + circleMap 0 1 p.2 • p.1)‖ₑ) := by
    fun_prop
  have hswap := lintegral_lintegral_swap
    (μ := μ.restrict (ball 0 R)) (ν := volume.restrict (Ioc 0 (2 * π)))
    (f := fun v t ↦ ‖h (a + circleMap 0 1 t • v)‖ₑ) hcont.measurable.aemeasurable
  have hmul : (μ (ball 0 R) * ‖h a‖ₑ) * ENNReal.ofReal (2 * π) ≤
      (∫⁻ x in ball a R, ‖h x‖ₑ ∂μ) * ENNReal.ofReal (2 * π) := by
    calc (μ (ball 0 R) * ‖h a‖ₑ) * ENNReal.ofReal (2 * π)
        = ∫⁻ _v in ball 0 R, ENNReal.ofReal (2 * π) * ‖h a‖ₑ ∂μ := by
          simp only [lintegral_const, Measure.restrict_apply_univ]
          ring
      _ ≤ ∫⁻ v in ball 0 R, (∫⁻ t in Ioc 0 (2 * π), ‖h (a + circleMap 0 1 t • v)‖ₑ) ∂μ :=
          setLIntegral_mono' measurableSet_ball fun v hv ↦
            ofReal_two_pi_mul_enorm_le_lintegral_circle hh (by simpa using hv)
      _ = ∫⁻ t in Ioc 0 (2 * π), ∫⁻ v in ball 0 R, ‖h (a + circleMap 0 1 t • v)‖ₑ ∂μ := hswap
      _ = (∫⁻ x in ball a R, ‖h x‖ₑ ∂μ) * ENNReal.ofReal (2 * π) := by
          simp_rw [lintegral_ball_add_circleMap_smul μ (fun x ↦ ‖h x‖ₑ) a]
          simp
  exact (ENNReal.mul_le_mul_iff_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)))
    ENNReal.ofReal_ne_top).mp hmul

omit [FiniteDimensional ℂ E] in
/-- The weak `∂̄`-equation, tested against one direction, splits into two real directional
derivatives. -/
theorem integral_mul_dbarDir_eq {μ : Measure E} {F : E → ℂ}
    (hF : Integrable F μ) {g : E → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : E) :
    ∫ x, F x * dbarDir v g x ∂μ =
      1 / 2 * ∫ x, F x * fderiv ℝ g x v ∂μ + I / 2 * ∫ x, F x * fderiv ℝ g x (I • v) ∂μ := by
  have hint : ∀ w : E, Integrable (fun x ↦ F x * fderiv ℝ g x w) μ := by
    intro w
    have hcont : Continuous fun x ↦ fderiv ℝ g x w :=
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport fun x ↦ fderiv ℝ g x w :=
      (hgc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℂ ↦ L w) rfl
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
    exact hF.mul_bdd hcont.aestronglyMeasurable (Eventually.of_forall hC)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((hint v).const_mul _) ((hint (I • v)).const_mul _)]
  congr 1
  ext x
  simp only [dbarDir]
  ring

/-- **Mollifications of weakly `∂̄`-closed functions are `∂̄`-closed** at every point whose
closed `rOut`-ball lies in the region where the weak equation holds. -/
theorem dbarDir_bump_convolution_eq_zero_of_weak {μ : Measure E} [μ.IsAddHaarMeasure]
    {V : Set E} (hV : IsOpen V) {F : E → ℂ} (hF : Integrable F μ)
    (hweak : ∀ g : E → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ V →
      ∀ v : E, ∫ x, F x * dbarDir v g x ∂μ = 0)
    (ρ : ContDiffBump (0 : E)) {x : E} (hx : closedBall x ρ.rOut ⊆ V) (v : E) :
    dbarDir v (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] F) x = 0 := by
  have key := sum_fderiv_bump_convolution_eq_of_weak hV (f := fun _ : Fin 2 ↦ F)
    (fun _ ↦ hF.locallyIntegrable) (ζ := 0) locallyIntegrable_zero ![1 / 2, I / 2] ![v, I • v]
    (fun g hg hgc hgV ↦ by
      have h0 := hweak g hg hgc hgV v
      rw [integral_mul_dbarDir_eq hF hg hgc v] at h0
      simpa [Fin.sum_univ_two] using h0) ρ hx
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    convolution_zero, Pi.zero_apply] at key
  simp only [dbarDir]
  linear_combination key

end General

section Model

variable {n : ℕ}

/-- Local form of Weyl's lemma for `∂̄`: on a ball whose triple lies in `U`, a weakly
`∂̄`-closed locally integrable function agrees almost everywhere with a holomorphic
function. -/
theorem exists_differentiableOn_ball_ae_eq_of_weak_dbar {U : Set (ComplexModel n)}
    {F : ComplexModel n → ℂ} (hF : LocallyIntegrableOn F U)
    (hweak : ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∀ v : ComplexModel n, ∫ x, F x * dbarDir v g x = 0)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hB : closedBall x₀ (3 * R) ⊆ U) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball x₀ R) ∧
      ∀ᵐ x ∂(volume.restrict (ball x₀ R)), F x = G x := by
  set K := closedBall x₀ (3 * R) with hK
  set F' := K.indicator F with hF'_def
  have hF' : Integrable F' :=
    (hF.integrableOn_compact_subset hB (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall
  have hweak' : ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ ball x₀ (3 * R) → ∀ v, ∫ x, F' x * dbarDir v g x = 0 := by
    intro g hg hgc hgs v
    rw [← hweak g hg hgc (hgs.trans (ball_subset_closedBall.trans hB)) v]
    congr 1
    ext x
    by_cases hx : x ∈ K
    · simp [F', hx]
    · have hxg : x ∉ tsupport g := fun h ↦ hx (ball_subset_closedBall (hgs h))
      have hd : fderiv ℝ g x = 0 := fderiv_of_notMem_tsupport ℝ hxg
      simp [F', hx, dbarDir, hd]
  let φ : ℕ → ContDiffBump (0 : ComplexModel n) := fun k ↦
    ⟨R / ((k : ℝ) + 2), R / ((k : ℝ) + 1), by positivity, by
      gcongr
      linarith⟩
  have hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) := by
    simpa [φ, div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R
  have h'φ : ∀ k, (φ k).rOut ≤ 2 * (φ k).rIn := by
    intro k
    simp only [φ]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    nlinarith
  have hrOut : ∀ k, (φ k).rOut ≤ R := fun k ↦
    div_le_self hR.le (by linarith [(k : ℕ).cast_nonneg (α := ℝ)])
  set h : ℕ → ComplexModel n → ℂ := fun k ↦ (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] F'
    with h_def
  have hsmooth : ∀ k, ContDiff ℝ ∞ (h k) := fun k ↦
    contDiff_bump_convolution (φ k) hF'.locallyIntegrable
  have hhol : ∀ k, DifferentiableOn ℂ (h k) (ball x₀ (2 * R)) := by
    intro k x hx
    refine (differentiableAt_complex_of_dbarDir_eq_zero
      ((hsmooth k).differentiable (by simp) x) fun v ↦ ?_).differentiableWithinAt
    refine dbarDir_bump_convolution_eq_zero_of_weak isOpen_ball hF' hweak' (φ k) ?_ v
    intro y hy
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hy
    calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ < R + 2 * R := add_lt_add_of_le_of_lt (hy.trans (hrOut k)) hx
      _ = 3 * R := by ring
  set A := ∫⁻ x, ‖F' x‖ₑ with hA_def
  have hA : A ≠ ⊤ := hF'.2.ne
  have hball_pos : volume (ball (0 : ComplexModel n) R) ≠ 0 := (measure_ball_pos volume 0 hR).ne'
  have hball_top : volume (ball (0 : ComplexModel n) R) ≠ ⊤ := measure_ball_lt_top.ne
  set M := (A / volume (ball (0 : ComplexModel n) R)).toReal with hM
  have hbound : ∀ k, ∀ y ∈ ball x₀ R, ‖h k y‖ ≤ M := by
    intro k y hy
    have hsub : ball y R ⊆ ball x₀ (2 * R) := by
      intro z hz
      rw [mem_ball] at hy hz ⊢
      linarith [dist_triangle z y x₀]
    have h1 := measure_ball_mul_enorm_le_lintegral_ball volume (hsmooth k).continuous
      ((hhol k).mono hsub)
    have h2 : ∫⁻ x in ball y R, ‖h k x‖ₑ ≤ A :=
      (setLIntegral_le_lintegral _ _).trans
        (lintegral_enorm_bump_convolution_le (φ k) hF'.aestronglyMeasurable)
    have h3 : ‖h k y‖ₑ ≤ A / volume (ball (0 : ComplexModel n) R) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hball_pos) (Or.inl hball_top), mul_comm]
      exact h1.trans h2
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_ne_top hA hball_pos)).1 h3
  obtain ⟨ψ, G, hψ, hGd, hGt⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded
    (U := ball x₀ R) isOpen_ball h fun x hx ↦ by
      rw [mem_ball] at hx
      have hsub : ball x (R - dist x x₀) ⊆ ball x₀ R := ball_subset_ball' (by linarith)
      exact ⟨R - dist x x₀, by linarith, M, Eventually.of_forall fun k ↦
        ⟨(hhol k).mono (hsub.trans (ball_subset_ball (by linarith))),
          fun y hy ↦ hbound k y (hsub hy)⟩⟩
  refine ⟨G, hGd, ?_⟩
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hφ (Eventually.of_forall h'φ) hF'.locallyIntegrable
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with x hx hxB
  have h1 : Tendsto (fun k ↦ h (ψ k) x) atTop (𝓝 (F' x)) := hx.comp hψ.tendsto_atTop
  have h2 := hGt.tendsto_at hxB
  have hxK : x ∈ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hxB
  have := tendsto_nhds_unique h1 h2
  simpa [F', hxK] using this

/-- **Weyl's lemma for `∂̄`.** A locally integrable function on an open set `U ⊆ ℂⁿ` whose
weak Wirtinger derivatives `∂̄_v` all vanish (tested against smooth compactly supported
functions in `U`) agrees almost everywhere on `U` with a holomorphic function. -/
theorem exists_differentiableOn_ae_eq_of_weak_dbar {U : Set (ComplexModel n)} (hU : IsOpen U)
    {F : ComplexModel n → ℂ} (hF : LocallyIntegrableOn F U)
    (hweak : ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∀ v : ComplexModel n, ∫ x, F x * dbarDir v g x = 0) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G U ∧
      ∀ᵐ x ∂(volume.restrict U), F x = G x := by
  have hloc : ∀ x ∈ U, ∃ R > 0, ball x R ⊆ U ∧ ∃ G : ComplexModel n → ℂ,
      DifferentiableOn ℂ G (ball x R) ∧ ∀ᵐ y ∂(volume.restrict (ball x R)), F y = G y := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
    refine ⟨ε / 4, by positivity, (ball_subset_ball (by linarith)).trans hεU, ?_⟩
    exact exists_differentiableOn_ball_ae_eq_of_weak_dbar hF hweak (by positivity)
      ((closedBall_subset_ball (by linarith)).trans hεU)
  choose! R hR hRU G₀ hG₀d hG₀ae using hloc
  have hagree : ∀ x ∈ U, ∀ y ∈ U,
      EqOn (G₀ x) (G₀ y) (ball x (R x) ∩ ball y (R y)) := by
    intro x hx y hy
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (isOpen_ball.inter isOpen_ball)
      ((hG₀d x hx).continuousOn.mono inter_subset_left)
      ((hG₀d y hy).continuousOn.mono inter_subset_right)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (hG₀ae x hx),
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hG₀ae y hy)] with z hz1 hz2
    rw [← hz1, hz2]
  set G : ComplexModel n → ℂ := fun y ↦ G₀ y y with hG
  have hGeq : ∀ x ∈ U, EqOn G (G₀ x) (ball x (R x)) := by
    intro x hx y hy
    have hyU := hRU x hx hy
    exact hagree y hyU x hx ⟨mem_ball_self (hR y hyU), hy⟩
  refine ⟨G, fun x hx ↦ ?_, ?_⟩
  · have hd := (hG₀d x hx).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hR x hx)))
    have heq : G =ᶠ[𝓝 x] G₀ x :=
      Filter.eventually_of_mem (ball_mem_nhds x (hR x hx)) (hGeq x hx)
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
  · obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : U ↦ ball (x : ComplexModel n) (R x)) fun _ ↦ isOpen_ball
    have hUeq : U = ⋃ x ∈ T, ball (x : ComplexModel n) (R x) := by
      rw [hTU]
      ext y
      simp only [mem_iUnion]
      exact ⟨fun hy ↦ ⟨⟨y, hy⟩, mem_ball_self (hR y hy)⟩, fun ⟨x, hx⟩ ↦ hRU x x.2 hx⟩
    rw [hUeq, ae_restrict_biUnion_iff _ hTc]
    intro x _
    filter_upwards [hG₀ae x x.2, ae_restrict_mem measurableSet_ball] with y h1 h2
    rw [h1, hGeq x x.2 h2]

end Model

end Hironaka
