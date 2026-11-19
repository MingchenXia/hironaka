import Hironaka.Analytic.HolomorphicNormalFamilies

set_option autoImplicit false

/-!
# Limits of weighted L² holomorphic extensions

`exists_differentiableOn_extension_of_weighted_bounds` is the limiting step shared by the
approximation arguments for L² extension theorems.  Let `U i` be an increasing sequence of
open sets of `ℂⁿ`, `w i` increasing weights which are locally bounded below by a positive
constant, and `F i` holomorphic on `U i` with `∫_{U i} |F i|² w i ≤ A < ∞`, all agreeing
with a fixed function `g` along a map `ι`.  Then some `G` holomorphic on `⋃ U i` agrees with
`g` along `ι` and satisfies `∫_{⋃ U i} |G|² sup_i w i ≤ A`.

The weights bound the `F i` in `L²` near every point, the mean-value inequality turns this
into local uniform bounds, Montel's theorem (`Hironaka.HolomorphicNormalFamilies`) extracts a
convergent subsequence, and Fatou's lemma followed by monotone convergence gives the estimate.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

noncomputable section



variable {N : ℕ} [MeasurableSpace (ComplexModel N)] [BorelSpace (ComplexModel N)]

/-- Weighted `L²` bounds with a positive lower bound on the weight near `x` give uniform
bounds near `x`. -/
theorem exists_eventually_norm_le_of_weighted_bounds
    {U : ℕ → Set (ComplexModel N)} (hUo : ∀ i, IsOpen (U i)) (hUm : Monotone U)
    {w : ℕ → ComplexModel N → ℝ≥0∞}
    (hwm : ∀ x ∈ ⋃ i, U i, Monotone fun i => w i x)
    {F : ℕ → ComplexModel N → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) (U i))
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ x in U i, ENNReal.ofReal (‖F i x‖ ^ 2) * w i x ≤ A)
    {x : ComplexModel N} (hx : x ∈ ⋃ i, U i) {r₁ δ : ℝ} (hr₁ : 0 < r₁) (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball x r₁, ENNReal.ofReal δ ≤ w 0 y) :
    ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (F i) (ball x r) ∧ ∀ y ∈ ball x r, ‖F i y‖ ≤ M := by
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hx
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp (hUo i₀) x hi₀
  set r : ℝ := min r₁ r₂ / 2 with hr
  have hrpos : 0 < r := by positivity
  have h2r₁ : 2 * r ≤ r₁ := by rw [hr]; linarith [min_le_left r₁ r₂]
  have h2r₂ : 2 * r ≤ r₂ := by rw [hr]; linarith [min_le_right r₁ r₂]
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel N) r) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ hrpos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set B : ℝ≥0∞ := A / (ENNReal.ofReal δ * V) with hB
  have hBtop : B ≠ ⊤ := ENNReal.div_ne_top hA
    (mul_ne_zero (ENNReal.ofReal_pos.mpr hδ).ne' hV0)
  refine ⟨r, hrpos, Real.sqrt B.toReal, eventually_atTop.mpr ⟨i₀, fun i hi => ?_⟩⟩
  have hsub : ∀ y ∈ ball x r, closedBall y r ⊆ U i := fun y hy z hz => by
    apply hUm hi
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  have hxr : ball x r ⊆ U i := fun y hy =>
    hsub y hy (mem_closedBall_self hrpos.le)
  refine ⟨(hF i).mono hxr, fun y hy => ?_⟩
  have hmv := lintegral_ball_normSq_ge (hUo i) (hF i) hrpos (hsub y hy)
  rw [Measure.addHaar_ball_center] at hmv
  have hyU : ∀ z ∈ ball y r, z ∈ ⋃ i, U i := fun z hz =>
    mem_iUnion.mpr ⟨i, hsub y hy (ball_subset_closedBall hz)⟩
  have hyx : ∀ z ∈ ball y r, z ∈ ball x r₁ := fun z hz => by
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle z y x]
  have hchain : ENNReal.ofReal δ * (V * ENNReal.ofReal (‖F i y‖ ^ 2)) ≤ A := by
    calc ENNReal.ofReal δ * (V * ENNReal.ofReal (‖F i y‖ ^ 2))
        ≤ ENNReal.ofReal δ * ∫⁻ z in ball y r, ENNReal.ofReal (‖F i z‖ ^ 2) := by
          gcongr
      _ = ∫⁻ z in ball y r, ENNReal.ofReal δ * ENNReal.ofReal (‖F i z‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ z in ball y r, ENNReal.ofReal (‖F i z‖ ^ 2) * w i z := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          rw [mul_comm]
          gcongr
          exact (hlow z (hyx z hz)).trans (hwm z (hyU z hz) (Nat.zero_le i))
      _ ≤ ∫⁻ z in U i, ENNReal.ofReal (‖F i z‖ ^ 2) * w i z :=
          lintegral_mono_set (ball_subset_closedBall.trans (hsub y hy))
      _ ≤ A := hbound i
  have hle : ENNReal.ofReal (‖F i y‖ ^ 2) ≤ B := by
    rw [hB, ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero
      (ENNReal.ofReal_pos.mpr hδ).ne' hV0)) (Or.inl (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top hVtop))]
    calc ENNReal.ofReal (‖F i y‖ ^ 2) * (ENNReal.ofReal δ * V)
        = ENNReal.ofReal δ * (V * ENNReal.ofReal (‖F i y‖ ^ 2)) := by ring
      _ ≤ A := hchain
  have hsq : ‖F i y‖ ^ 2 ≤ B.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hBtop).mp hle
  exact Real.le_sqrt_of_sq_le hsq

/-- **Subsequential limits of weighted `L²` holomorphic extensions.**
The returned limit comes with the locally uniform convergence relation which
identifies it as a subsequential limit of the supplied family. -/
theorem exists_subseq_differentiableOn_extension_of_weighted_bounds
    {α : Type*} {ι : α → ComplexModel N} {g : α → ℂ}
    {U : ℕ → Set (ComplexModel N)} (hUo : ∀ i, IsOpen (U i)) (hUm : Monotone U)
    {w : ℕ → ComplexModel N → ℝ≥0∞}
    (hwm : ∀ x ∈ ⋃ i, U i, Monotone fun i => w i x)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict (⋃ i, U i)))
    (hlow : ∀ x ∈ ⋃ i, U i, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ w 0 y)
    {F : ℕ → ComplexModel N → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) (U i))
    (hFg : ∀ i a, ι a ∈ U i → F i (ι a) = g a)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ x in U i, ENNReal.ofReal (‖F i x‖ ^ 2) * w i x ≤ A) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel N → ℂ), StrictMono ψ ∧
      DifferentiableOn ℂ G (⋃ i, U i) ∧
      TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop (⋃ i, U i) ∧
      (∀ a, ι a ∈ ⋃ i, U i → G (ι a) = g a) ∧
      ∫⁻ x in ⋃ i, U i, ENNReal.ofReal (‖G x‖ ^ 2) * ⨆ i, w i x ≤ A := by
  set W : Set (ComplexModel N) := ⋃ i, U i with hW
  have hWo : IsOpen W := isOpen_iUnion hUo
  have hUW : ∀ i, U i ⊆ W := fun i => subset_iUnion U i
  obtain ⟨ψ, G, hψ, hG, hconv⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded hWo F fun x hx => by
    obtain ⟨r₁, hr₁, δ, hδ, hl⟩ := hlow x hx
    exact exists_eventually_norm_le_of_weighted_bounds hUo hUm hwm hF hA hbound hx hr₁ hδ hl
  have hpt : ∀ x ∈ W, Tendsto (fun i => F (ψ i) x) atTop (𝓝 (G x)) := fun x hx =>
    hconv.tendsto_at hx
  refine ⟨ψ, G, hψ, hG, hconv, fun a ha => ?_, ?_⟩
  · obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp ha
    refine tendsto_nhds_unique (hpt _ ha) (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop i₀] with i hi
    exact (hFg (ψ i) a (hUm (hi.trans (hψ.id_le i)) hi₀)).symm
  -- Fatou on each `U i₀`.
  have hfatou : ∀ i₀, ∫⁻ x in U i₀, ENNReal.ofReal (‖G x‖ ^ 2) * w i₀ x ≤ A := by
    intro i₀
    set f : ℕ → ComplexModel N → ℝ≥0∞ := fun k x =>
      ENNReal.ofReal (‖F (ψ (k + i₀)) x‖ ^ 2) * w i₀ x with hf
    have hle_idx : ∀ k, i₀ ≤ ψ (k + i₀) := fun k =>
      (Nat.le_add_left i₀ k).trans (hψ.id_le _)
    have hmeas : ∀ k, AEMeasurable (f k) (volume.restrict (U i₀)) := by
      intro k
      have hc : ContinuousOn (fun x => ENNReal.ofReal (‖F (ψ (k + i₀)) x‖ ^ 2)) (U i₀) :=
        (ENNReal.continuous_ofReal.comp_continuousOn
          (((hF _).continuousOn.mono (hUm (hle_idx k))).norm.pow 2))
      exact (hc.aemeasurable (hUo i₀).measurableSet).mul
        ((hwmeas i₀).mono_measure (Measure.restrict_mono (hUW i₀) le_rfl))
    have hpoint : ∀ x ∈ U i₀, ENNReal.ofReal (‖G x‖ ^ 2) * w i₀ x ≤
        liminf (fun k => f k x) atTop := by
      intro x hx
      by_cases hGx : G x = 0
      · simp [hGx]
      · have ht : Tendsto (fun k => f k x) atTop
            (𝓝 (ENNReal.ofReal (‖G x‖ ^ 2) * w i₀ x)) := by
          have h1 : Tendsto (fun k => F (ψ (k + i₀)) x) atTop (𝓝 (G x)) :=
            (hpt x (hUW i₀ hx)).comp (tendsto_add_atTop_nat i₀)
          have h2 : Tendsto (fun k => ENNReal.ofReal (‖F (ψ (k + i₀)) x‖ ^ 2)) atTop
              (𝓝 (ENNReal.ofReal (‖G x‖ ^ 2))) :=
            ENNReal.tendsto_ofReal ((h1.norm).pow 2)
          exact ENNReal.Tendsto.mul_const h2 (Or.inl (by
            simpa [ENNReal.ofReal_eq_zero, not_le] using hGx))
        exact ht.liminf_eq.ge
    calc ∫⁻ x in U i₀, ENNReal.ofReal (‖G x‖ ^ 2) * w i₀ x
        ≤ ∫⁻ x in U i₀, liminf (fun k => f k x) atTop :=
          setLIntegral_mono' (hUo i₀).measurableSet hpoint
      _ ≤ liminf (fun k => ∫⁻ x in U i₀, f k x) atTop := lintegral_liminf_le' hmeas
      _ ≤ A := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          calc ∫⁻ x in U i₀, f k x
              ≤ ∫⁻ x in U i₀, ENNReal.ofReal (‖F (ψ (k + i₀)) x‖ ^ 2) * w (ψ (k + i₀)) x := by
                refine setLIntegral_mono' (hUo i₀).measurableSet fun x hx => ?_
                exact mul_le_mul_of_nonneg_left (hwm x (hUW i₀ hx) (hle_idx k)) zero_le
            _ ≤ ∫⁻ x in U (ψ (k + i₀)), ENNReal.ofReal (‖F (ψ (k + i₀)) x‖ ^ 2) *
                  w (ψ (k + i₀)) x := lintegral_mono_set (hUm (hle_idx k))
            _ ≤ A := hbound _
  -- Monotone convergence.
  set k : ℕ → ComplexModel N → ℝ≥0∞ := fun i =>
    (U i).indicator fun x => ENNReal.ofReal (‖G x‖ ^ 2) * w i x with hk
  have hkmeas : ∀ i, AEMeasurable (k i) (volume.restrict W) := by
    intro i
    have hc : ContinuousOn (fun x => ENNReal.ofReal (‖G x‖ ^ 2)) W :=
      ENNReal.continuous_ofReal.comp_continuousOn (hG.continuousOn.norm.pow 2)
    exact ((hc.aemeasurable hWo.measurableSet).mul (hwmeas i)).indicator
      (hUo i).measurableSet
  have hkmono : ∀ᵐ x ∂(volume.restrict W), Monotone fun i => k i x := by
    refine ae_restrict_of_forall_mem hWo.measurableSet fun x hx i j hij => ?_
    by_cases hxi : x ∈ U i
    · simp only [hk, indicator_of_mem hxi, indicator_of_mem (hUm hij hxi)]
      exact mul_le_mul_of_nonneg_left (hwm x hx hij) zero_le
    · simp [hk, indicator_of_notMem hxi]
  have hkint : ∀ i, ∫⁻ x in W, k i x ≤ A := by
    intro i
    rw [hk, lintegral_indicator (hUo i).measurableSet,
      Measure.restrict_restrict (hUo i).measurableSet, inter_eq_left.mpr (hUW i)]
    exact hfatou i
  calc ∫⁻ x in W, ENNReal.ofReal (‖G x‖ ^ 2) * ⨆ i, w i x
      ≤ ∫⁻ x in W, ⨆ i, k i x := by
        refine setLIntegral_mono' hWo.measurableSet fun x hx => ?_
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        rw [ENNReal.mul_iSup]
        refine iSup_le fun i => ?_
        refine le_trans ?_ (le_iSup _ (max i j))
        simp only [hk, indicator_of_mem (hUm (le_max_right i j) hj)]
        exact mul_le_mul_of_nonneg_left (hwm x hx (le_max_left i j)) zero_le
    _ = ⨆ i, ∫⁻ x in W, k i x := lintegral_iSup' hkmeas hkmono
    _ ≤ A := iSup_le hkint

/-- Compatibility wrapper which retains the older conclusion after forgetting
the subsequence and its locally uniform convergence witness. -/
theorem exists_differentiableOn_extension_of_weighted_bounds
    {α : Type*} {ι : α → ComplexModel N} {g : α → ℂ}
    {U : ℕ → Set (ComplexModel N)} (hUo : ∀ i, IsOpen (U i)) (hUm : Monotone U)
    {w : ℕ → ComplexModel N → ℝ≥0∞}
    (hwm : ∀ x ∈ ⋃ i, U i, Monotone fun i => w i x)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict (⋃ i, U i)))
    (hlow : ∀ x ∈ ⋃ i, U i, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ w 0 y)
    {F : ℕ → ComplexModel N → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) (U i))
    (hFg : ∀ i a, ι a ∈ U i → F i (ι a) = g a)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ x in U i, ENNReal.ofReal (‖F i x‖ ^ 2) * w i x ≤ A) :
    ∃ G : ComplexModel N → ℂ, DifferentiableOn ℂ G (⋃ i, U i) ∧
      (∀ a, ι a ∈ ⋃ i, U i → G (ι a) = g a) ∧
      ∫⁻ x in ⋃ i, U i, ENNReal.ofReal (‖G x‖ ^ 2) * ⨆ i, w i x ≤ A := by
  obtain ⟨-, G, -, hG, -, hGext, hGint⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds
      hUo hUm hwm hwmeas hlow hF hFg hA hbound
  exact ⟨G, hG, hGext, hGint⟩

end

end Hironaka
