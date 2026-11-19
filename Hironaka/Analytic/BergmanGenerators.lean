import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Analytic.WeightedL2ExtensionLimit
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

/-!
# Finitely many generators dominating a weighted Bergman space

Let `X` be the set of holomorphic functions on a ball `B` around `z` with weighted `L²`
norm `∫_B |f|² e^{-mP} ≤ 1`, the weight being bounded above on `B`.  Some finitely many
`g_1, …, g_N ∈ X` dominate every element of `X` pointwise near `z`, with one constant:

  `|f(y)|² ≤ K Σ_l |g_l(y)|²`  for all `f ∈ X` and `y` near `z`.

The germs at `z` of the elements of `X` generate a finitely generated ideal of the
Noetherian ring of holomorphic germs, so finitely many elements of `X` generate it, and
each single `f ∈ X` is dominated with its own constant on its own ball
(`exists_finite_germ_generators`).  The uniform constant comes from the Baire category
theorem in the Banach space of continuous functions on a closed ball: the restrictions of
`X` form a closed set there (Montel's theorem and Fatou's lemma), covered by the closed
sets of restrictions dominated with constant `j` on the ball of radius `R/(j+1)`; an
interior point and the convexity of `X` give the uniform constant.  This is the
finiteness step of Demailly's Bergman-kernel approximation (Demailly, *Analytic methods
in algebraic geometry*, Theorem 13.2).
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace Hironaka.BergmanGenerators

noncomputable section



variable {n : ℕ}

theorem eventually_differentiableAt_translate {f : ComplexModel n → ℂ} {z : ComplexModel n}
    (hf : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun w => f (w + z)) w := by
  have ht : Tendsto (fun w : ComplexModel n => w + z) (𝓝 0) (𝓝 z) := by
    simpa using (continuous_add_const z).tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually hf] with w hw
  exact hw.comp w ((differentiableAt_id).add_const z)

/-- **Finitely many germ generators.** For any set `S` of functions holomorphic near `z`,
finitely many members of `S` dominate every member of `S` near `z`, with a constant and a
radius depending on that member. -/
theorem exists_finite_germ_generators (S : Set (ComplexModel n → ℂ)) (z : ComplexModel n)
    (hS : ∀ f ∈ S, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ), (∀ l, g l ∈ S) ∧
      ∀ f ∈ S, ∃ r > 0, ∃ K : ℝ, ∀ y ∈ ball z r, ‖f y‖ ^ 2 ≤ K * ∑ l, ‖g l y‖ ^ 2 := by
  classical
  have := isNoetherianRing_holGerm_euclidean n
  let G : S → HolGerm (ComplexModel n) := fun f =>
    HolGerm.mk (fun w => (f : ComplexModel n → ℂ) (w + z))
      (eventually_differentiableAt_translate (hS f f.2))
  have hfg : (Ideal.span (range G)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsT, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (range G)).mp hfg
  let N := s.card
  let v : Fin N → HolGerm (ComplexModel n) := fun i => (s.equivFin.symm i : _)
  have hv : ∀ i, ∃ f : S, G f = v i := fun i => hsT (s.equivFin.symm i).2
  choose p hp using hv
  refine ⟨N, fun l => (p l : ComplexModel n → ℂ), fun l => (p l).2, fun f hf => ?_⟩
  have hrange : (s : Set (HolGerm (ComplexModel n))) = range v := by
    ext x
    constructor
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [v]⟩
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
  have hmem : G ⟨f, hf⟩ ∈ Ideal.span (range v) := by
    rw [← hrange]
    change G ⟨f, hf⟩ ∈ Submodule.span _ _
    rw [← hspan]
    exact Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have ha : ∀ l, ∃ (a : ComplexModel n → ℂ) (ha : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ a w),
      c l = HolGerm.mk a ha := fun l => HolGerm.exists_eq_mk (c l)
  choose a had hac using ha
  let q : Fin N → ComplexModel n → ℂ := fun l w => (p l : ComplexModel n → ℂ) (w + z)
  have hq : ∀ l, ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ (q l) w := fun l =>
    eventually_differentiableAt_translate (hS _ (p l).2)
  have hprod : ∀ l, ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun w => a l w * q l w) w := fun l =>
    eventually_differentiableAt_mul (had l) (hq l)
  have hgerm : (fun w => ∑ l, a l w * q l w) =ᶠ[𝓝 0] fun w => f (w + z) := by
    have h1 := HolGerm.mk_sum Finset.univ (fun l w => a l w * q l w) hprod
    have h2 : HolGerm.mk (fun w => ∑ l, a l w * q l w)
        (eventually_differentiableAt_sum Finset.univ hprod) = G ⟨f, hf⟩ := by
      rw [h1, ← hc]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hac l, ← hp l]
      rfl
    exact HolGerm.mk_eq_mk_iff.mp h2
  set M : ℝ := ∑ l, (‖a l 0‖ + 1) with hM
  have hbd : ∀ l, ∀ᶠ w in 𝓝 (0 : ComplexModel n), ‖a l w‖ ≤ M := fun l => by
    have hcont : ContinuousAt (a l) 0 :=
      continuousAt_zero_of_eventually_differentiableAt (had l)
    have hlt : ∀ᶠ w in 𝓝 (0 : ComplexModel n), ‖a l w‖ < ‖a l 0‖ + 1 :=
      hcont.norm.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hlt] with w hw
    refine hw.le.trans ?_
    exact Finset.single_le_sum (f := fun l => ‖a l 0‖ + 1)
      (fun l _ => by positivity) (Finset.mem_univ l)
  have hall : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      (∑ l, a l w * q l w = f (w + z)) ∧ ∀ l, ‖a l w‖ ≤ M :=
    hgerm.and (eventually_all.mpr hbd)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨r, hr, M ^ 2 * N, fun y hy => ?_⟩
  have hw : y - z ∈ ball (0 : ComplexModel n) r := by
    simpa [mem_ball, dist_eq_norm] using hy
  obtain ⟨heq, hle⟩ := hball _ hw
  simp only [q, sub_add_cancel] at heq
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun l _ => by positivity
  have hnorm : ‖f y‖ ≤ M * ∑ l, ‖(p l : ComplexModel n → ℂ) y‖ := by
    rw [← heq, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hle l) (norm_nonneg _)
  calc ‖f y‖ ^ 2 ≤ (M * ∑ l, ‖(p l : ComplexModel n → ℂ) y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = M ^ 2 * (∑ l, ‖(p l : ComplexModel n → ℂ) y‖) ^ 2 := by ring
    _ ≤ M ^ 2 * (N * ∑ l, ‖(p l : ComplexModel n → ℂ) y‖ ^ 2) := by
        gcongr
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun l => ‖(p l : ComplexModel n → ℂ) y‖)
    _ = M ^ 2 * N * ∑ l, ‖(p l : ComplexModel n → ℂ) y‖ ^ 2 := by ring

section Bergman

variable [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- The unit ball of the weighted Bergman space on `ball z (2R)`. -/
def bergmanUnitBall (z : ComplexModel n) (R : ℝ) (w : ComplexModel n → ℝ≥0∞) :
    Set (ComplexModel n → ℂ) :=
  {f | DifferentiableOn ℂ f (ball z (2 * R)) ∧
    ∫⁻ x in ball z (2 * R), ENNReal.ofReal (‖f x‖ ^ 2) * w x ≤ 1}

variable {z : ComplexModel n} {R : ℝ} {w : ComplexModel n → ℝ≥0∞}

theorem zero_mem_bergmanUnitBall : (0 : ComplexModel n → ℂ) ∈ bergmanUnitBall z R w :=
  ⟨differentiableOn_const 0, by simp⟩

omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
theorem closedBall_subset_ball_two_mul (hR : 0 < R) : closedBall z R ⊆ ball z (2 * R) :=
  closedBall_subset_ball (by linarith)

/-- **Uniform bound on the closed ball of radius `R`** for the weighted unit ball, from the
mean-value inequality and a positive lower bound of the weight. -/
theorem exists_norm_le_of_mem_bergmanUnitBall (hR : 0 < R) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f ∈ bergmanUnitBall z R w, ∀ x ∈ closedBall z R, ‖f x‖ ≤ L := by
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel n) (R / 2)) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set B : ℝ≥0∞ := 1 / (ENNReal.ofReal δ * V) with hB
  have hBtop : B ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top
    (mul_ne_zero (ENNReal.ofReal_pos.mpr hδ).ne' hV0)
  refine ⟨Real.sqrt B.toReal, Real.sqrt_nonneg _, fun f hf x hx => ?_⟩
  have hsub : closedBall x (R / 2) ⊆ ball z (2 * R) := fun y hy => by
    rw [mem_closedBall] at hx hy
    rw [mem_ball]
    linarith [dist_triangle y x z]
  have hmv := lintegral_ball_normSq_ge isOpen_ball hf.1 (by positivity : 0 < R / 2) hsub
  rw [Measure.addHaar_ball_center] at hmv
  have hchain : ENNReal.ofReal δ * (V * ENNReal.ofReal (‖f x‖ ^ 2)) ≤ 1 := by
    calc ENNReal.ofReal δ * (V * ENNReal.ofReal (‖f x‖ ^ 2))
        ≤ ENNReal.ofReal δ * ∫⁻ y in ball x (R / 2), ENNReal.ofReal (‖f y‖ ^ 2) := by
          gcongr
      _ = ∫⁻ y in ball x (R / 2), ENNReal.ofReal δ * ENNReal.ofReal (‖f y‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ y in ball x (R / 2), ENNReal.ofReal (‖f y‖ ^ 2) * w y := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          rw [mul_comm]
          gcongr
          exact hlow y (hsub (ball_subset_closedBall hy))
      _ ≤ ∫⁻ y in ball z (2 * R), ENNReal.ofReal (‖f y‖ ^ 2) * w y :=
          lintegral_mono_set (ball_subset_closedBall.trans hsub)
      _ ≤ 1 := hf.2
  have hle : ENNReal.ofReal (‖f x‖ ^ 2) ≤ B := by
    rw [hB, ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero
      (ENNReal.ofReal_pos.mpr hδ).ne' hV0)) (Or.inl (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top hVtop))]
    calc ENNReal.ofReal (‖f x‖ ^ 2) * (ENNReal.ofReal δ * V)
        = ENNReal.ofReal δ * (V * ENNReal.ofReal (‖f x‖ ^ 2)) := by ring
      _ ≤ 1 := hchain
  exact Real.le_sqrt_of_sq_le ((ENNReal.ofReal_le_iff_le_toReal hBtop).mp hle)

/-- **Sequential compactness of the weighted unit ball** for pointwise convergence on the
ball (Montel's theorem and Fatou's lemma). -/
theorem exists_subseq_tendsto_mem_bergmanUnitBall
    (hw : AEMeasurable w (volume.restrict (ball z (2 * R)))) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y)
    {F : ℕ → ComplexModel n → ℂ} (hF : ∀ i, F i ∈ bergmanUnitBall z R w) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel n → ℂ), StrictMono ψ ∧ G ∈ bergmanUnitBall z R w ∧
      ∀ x ∈ ball z (2 * R), Tendsto (fun i => F (ψ i) x) atTop (𝓝 (G x)) := by
  set U : Set (ComplexModel n) := ball z (2 * R) with hU
  have hUo : IsOpen U := isOpen_ball
  obtain ⟨ψ, G, hψ, hG, hconv⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded
      hUo F fun x hx => by
    obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.mp hUo x hx
    exact exists_eventually_norm_le_of_weighted_bounds (U := fun _ => U) (w := fun _ => w)
      (fun _ => hUo) (fun _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (fun i => (hF i).1)
      ENNReal.one_ne_top (fun i => (hF i).2) (by simpa using hx) hr₁ hδ
      fun y hy => hlow y (hr₁U hy)
  have hpt : ∀ x ∈ U, Tendsto (fun i => F (ψ i) x) atTop (𝓝 (G x)) := fun x hx =>
    hconv.tendsto_at hx
  refine ⟨ψ, G, hψ, ⟨hG, ?_⟩, hpt⟩
  have hmeas : ∀ k, AEMeasurable (fun x => ENNReal.ofReal (‖F (ψ k) x‖ ^ 2) * w x)
      (volume.restrict U) := fun k =>
    ((ENNReal.continuous_ofReal.comp_continuousOn
      ((hF (ψ k)).1.continuousOn.norm.pow 2)).aemeasurable hUo.measurableSet).mul hw
  calc ∫⁻ x in U, ENNReal.ofReal (‖G x‖ ^ 2) * w x
      ≤ ∫⁻ x in U, liminf (fun k => ENNReal.ofReal (‖F (ψ k) x‖ ^ 2) * w x) atTop := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hUo.measurableSet] with x hx
        by_cases hGx : G x = 0
        · simp [hGx]
        · have h2 : Tendsto (fun k => ENNReal.ofReal (‖F (ψ k) x‖ ^ 2)) atTop
              (𝓝 (ENNReal.ofReal (‖G x‖ ^ 2))) :=
            ENNReal.tendsto_ofReal (((hpt x hx).norm).pow 2)
          exact (ENNReal.Tendsto.mul_const h2 (Or.inl (by
            simpa [ENNReal.ofReal_eq_zero, not_le] using hGx))).liminf_eq.ge
    _ ≤ liminf (fun k => ∫⁻ x in U, ENNReal.ofReal (‖F (ψ k) x‖ ^ 2) * w x) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ 1 := liminf_le_of_frequently_le' (Frequently.of_forall fun k => (hF (ψ k)).2)

/-- Pointwise convexity of the weighted density. -/
theorem ofReal_norm_sq_convex_le {a b : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (‖(1 - t : ℂ) * a + (t : ℂ) * b‖ ^ 2) ≤
      ENNReal.ofReal (1 - t) * ENNReal.ofReal (‖a‖ ^ 2) +
        ENNReal.ofReal t * ENNReal.ofReal (‖b‖ ^ 2) := by
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul ht0,
    ← ENNReal.ofReal_add (by have := sq_nonneg ‖a‖; nlinarith)
      (by have := sq_nonneg ‖b‖; nlinarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : ‖(1 - t : ℂ) * a + (t : ℂ) * b‖ ≤ (1 - t) * ‖a‖ + t * ‖b‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, show ((1 - t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg ht0]
  have h0 : 0 ≤ (1 - t) * ‖a‖ + t * ‖b‖ := by
    have := norm_nonneg a; have := norm_nonneg b; nlinarith
  calc ‖(1 - t : ℂ) * a + (t : ℂ) * b‖ ^ 2 ≤ ((1 - t) * ‖a‖ + t * ‖b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 := by
        nlinarith [sq_nonneg (‖a‖ - ‖b‖), mul_nonneg ht0 (sub_nonneg.mpr ht1)]

theorem convex_mem_bergmanUnitBall (hw : AEMeasurable w (volume.restrict (ball z (2 * R))))
    {f g : ComplexModel n → ℂ} (hf : f ∈ bergmanUnitBall z R w) (hg : g ∈ bergmanUnitBall z R w)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun x => (1 - t : ℂ) * f x + (t : ℂ) * g x) ∈ bergmanUnitBall z R w := by
  refine ⟨(hf.1.const_mul _).add (hg.1.const_mul _), ?_⟩
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (1 - t) * (ENNReal.ofReal (‖f x‖ ^ 2) * w x))
      (volume.restrict (ball z (2 * R))) :=
    (((ENNReal.continuous_ofReal.comp_continuousOn
      (hf.1.continuousOn.norm.pow 2)).aemeasurable isOpen_ball.measurableSet).mul hw).const_mul _
  calc ∫⁻ x in ball z (2 * R), ENNReal.ofReal (‖(1 - t : ℂ) * f x + (t : ℂ) * g x‖ ^ 2) * w x
      ≤ ∫⁻ x in ball z (2 * R), (ENNReal.ofReal (1 - t) * (ENNReal.ofReal (‖f x‖ ^ 2) * w x) +
          ENNReal.ofReal t * (ENNReal.ofReal (‖g x‖ ^ 2) * w x)) := by
        refine lintegral_mono fun x => ?_
        calc ENNReal.ofReal (‖(1 - t : ℂ) * f x + (t : ℂ) * g x‖ ^ 2) * w x
            ≤ (ENNReal.ofReal (1 - t) * ENNReal.ofReal (‖f x‖ ^ 2) +
                ENNReal.ofReal t * ENNReal.ofReal (‖g x‖ ^ 2)) * w x := by
              gcongr; exact ofReal_norm_sq_convex_le ht0 ht1
          _ = _ := by ring
    _ = ENNReal.ofReal (1 - t) * (∫⁻ x in ball z (2 * R), ENNReal.ofReal (‖f x‖ ^ 2) * w x) +
          ENNReal.ofReal t * ∫⁻ x in ball z (2 * R), ENNReal.ofReal (‖g x‖ ^ 2) * w x := by
        rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 - t) * 1 + ENNReal.ofReal t * 1 := by gcongr; exacts [hf.2, hg.2]
    _ = 1 := by
        rw [mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) ht0]
        simp

/-- **Uniform domination by finitely many generators** (Baire category). Finitely many
elements of the weighted Bergman unit ball dominate all of its elements on one ball around
`z`, with one constant. -/
theorem exists_uniform_generators (hR : 0 < R)
    (hw : AEMeasurable w (volume.restrict (ball z (2 * R)))) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (r K : ℝ), 0 < r ∧
      (∀ l, g l ∈ bergmanUnitBall z R w) ∧
      ∀ f ∈ bergmanUnitBall z R w, ∀ y ∈ ball z r, ‖f y‖ ^ 2 ≤ K * ∑ l, ‖g l y‖ ^ 2 := by
  classical
  set X := bergmanUnitBall z R w with hX
  have hz2R : z ∈ ball z (2 * R) := mem_ball_self (by linarith)
  obtain ⟨N, g, hgX, hgen⟩ := exists_finite_germ_generators X z fun f hf =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz2R) fun y hy =>
      hf.1.differentiableAt (isOpen_ball.mem_nhds hy)
  obtain ⟨L, hL0, hL⟩ := exists_norm_le_of_mem_bergmanUnitBall hR hδ hlow
  have hTB : closedBall z R ⊆ ball z (2 * R) := closedBall_subset_ball_two_mul hR
  have : CompactSpace (closedBall z R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall z R)
  let ev : ∀ f ∈ X, C(closedBall z R, ℂ) := fun f hf =>
    ⟨fun x => f x, (hf.1.continuousOn.mono hTB).domRestrict⟩
  let S : Set C(closedBall z R, ℂ) := {h | ∃ f ∈ X, ∀ x, h x = f x}
  have hSc : IsClosed S := by
    refine isClosed_of_closure_subset fun h hh => ?_
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hh
    choose F hFX hFu using hu
    obtain ⟨ψ, G, hψ, hGX, hGt⟩ := exists_subseq_tendsto_mem_bergmanUnitBall hw hδ hlow hFX
    refine ⟨G, hGX, fun x => ?_⟩
    have h1 : Tendsto (fun i => u (ψ i) x) atTop (𝓝 (h x)) :=
      ((continuous_eval_const x).tendsto h).comp (hlim.comp hψ.tendsto_atTop)
    have h2 : Tendsto (fun i => u (ψ i) x) atTop (𝓝 (G x)) := by
      simpa only [hFu] using hGt x (hTB x.2)
    exact tendsto_nhds_unique h1 h2
  have : CompleteSpace S := hSc.completeSpace_coe
  have : Nonempty S := ⟨⟨ev 0 zero_mem_bergmanUnitBall, 0, zero_mem_bergmanUnitBall,
    fun _ => rfl⟩⟩
  let A : ℕ → Set S := fun j => {h | ∀ y : closedBall z R,
    (y : ComplexModel n) ∈ ball z (R / (j + 1)) →
      ‖(h : C(closedBall z R, ℂ)) y‖ ^ 2 ≤ (j + 1) * ∑ l, ‖g l y‖ ^ 2}
  have hAc : ∀ j, IsClosed (A j) := by
    intro j
    simp only [A, ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (((continuous_eval_const y).comp
        continuous_subtype_val).norm.pow 2) continuous_const
  have hsum0 : ∀ y : ComplexModel n, 0 ≤ ∑ l, ‖g l y‖ ^ 2 := fun y =>
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have hAU : ⋃ j, A j = univ := by
    refine eq_univ_of_forall fun h => mem_iUnion.mpr ?_
    obtain ⟨f, hfX, hfh⟩ := h.2
    obtain ⟨r, hr, K, hK⟩ := hgen f hfX
    obtain ⟨j, hj⟩ := exists_nat_gt (max K (R / r))
    refine ⟨j, fun y hy => ?_⟩
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    have hyr : (y : ComplexModel n) ∈ ball z r := by
      refine ball_subset_ball ?_ hy
      rw [div_le_iff₀ hj1]
      have h' := (le_max_right K (R / r)).trans hj.le
      rw [div_le_iff₀ hr] at h'
      nlinarith
    rw [hfh y]
    exact (hK y hyr).trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_left K (R / r)]) (hsum0 y))
  obtain ⟨j, h0, hh0⟩ := nonempty_interior_of_iUnion_of_closed hAc hAU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hh0)
  obtain ⟨f0, hf0X, hf0h⟩ := h0.2
  set t : ℝ := ε / (2 * (2 * L + ε)) with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    nlinarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  refine ⟨N, g, R / (j + 1), 4 * (j + 1) / t ^ 2, by positivity, hgX, fun f hf y hy => ?_⟩
  let ft : ComplexModel n → ℂ := fun x => (1 - t : ℂ) * f0 x + (t : ℂ) * f x
  have hftX : ft ∈ X := convex_mem_bergmanUnitBall hw hf0X hf htpos.le ht1
  have hyT : y ∈ closedBall z R := by
    refine ball_subset_closedBall.trans (closedBall_subset_closedBall ?_) hy
    exact div_le_self hR.le (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
  let hft : S := ⟨ev ft hftX, ft, hftX, fun _ => rfl⟩
  have hdist : dist hft h0 < ε := by
    rw [Subtype.dist_eq]
    have hle : dist (ev ft hftX) (h0 : C(closedBall z R, ℂ)) ≤ t * (2 * L) := by
      refine (ContinuousMap.dist_le (by positivity)).mpr fun x => ?_
      rw [hf0h x, dist_eq_norm]
      change ‖(1 - t : ℂ) * f0 x + (t : ℂ) * f x - f0 x‖ ≤ _
      rw [show (1 - t : ℂ) * f0 x + (t : ℂ) * f x - f0 x = (t : ℂ) * (f x - f0 x) by ring,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      linarith [hL f hf x x.2, hL f0 hf0X x x.2]
    refine hle.trans_lt ?_
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have h1 := hball hdist ⟨y, hyT⟩ hy
  have h2 := interior_subset hh0 ⟨y, hyT⟩ hy
  rw [hf0h] at h2
  change ‖ft y‖ ^ 2 ≤ _ at h1
  have htri : t * ‖f y‖ ≤ ‖ft y‖ + ‖f0 y‖ := by
    have heq : (t : ℂ) * f y = ft y - (1 - t : ℂ) * f0 y := by simp only [ft]; ring
    have hn : ‖(t : ℂ) * f y‖ = t * ‖f y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
    rw [← hn, heq]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, show ((1 - t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (f0 y)]
  have hsq : t ^ 2 * ‖f y‖ ^ 2 ≤ 4 * (j + 1) * ∑ l, ‖g l y‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) htri 2
    nlinarith [sq_nonneg (‖ft y‖ - ‖f0 y‖)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

end Bergman

end

end Hironaka.BergmanGenerators
