import Hironaka.Analytic.HiepSliceGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false

/-!
# Slice integrals in `ℂ^{m+1} = ℂ^m × ℂ`

* `lintegral_eq_splitFactor_mul`: integrals over `ℂ^{m+1}` are, up to the positive Haar factor
  `splitFactor m` of the splitting `splitCLE m`, integrals over `ℂ^m × ℂ`.
* `lintegral_le_of_le_indicator_closedBall`: a function bounded by `g(z')` on
  `{|z_{m+1}| ≤ ε}` and vanishing elsewhere has integral at most
  `splitFactor m · vol(D(0, ε)) · ∫ g`.
* `eq_zero_of_lintegral_div_normSq_ne_top`: a continuous `u` with
  `∫ |u|² W / |z_{m+1}|² < ∞` (with `W > 0` continuous) vanishes on the hyperplane
  `{z_{m+1} = 0}`, because `∫_{|u| < ρ} |u|^{-2} = ∞` in `ℂ`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace Hironaka.OTChen

noncomputable section



variable {m : ℕ}

/-- The splitting `ℂ^{m+1} ≃ ℂ^m × ℂ` as a measurable equivalence. -/
def splitEquiv (m : ℕ) : ComplexModel (m + 1) ≃ᵐ ComplexModel m × ℂ :=
  (splitCLE m).toHomeomorph.toMeasurableEquiv

@[simp] theorem splitEquiv_apply (x : ComplexModel (m + 1)) :
    splitEquiv m x = (initCoords x, x (Fin.last m)) := rfl

@[simp] theorem splitEquiv_symm_apply (q : ComplexModel m × ℂ) :
    (splitEquiv m).symm q = sliceMap m q.2 q.1 := rfl

instance isAddHaarMeasure_map_splitEquiv :
    ((volume : Measure (ComplexModel (m + 1))).map (splitEquiv m)).IsAddHaarMeasure :=
  (splitCLE m).isAddHaarMeasure_map volume

/-- The Haar factor of the splitting. -/
def splitFactor (m : ℕ) : ℝ≥0 :=
  ((volume : Measure (ComplexModel (m + 1))).map (splitEquiv m)).addHaarScalarFactor
    ((volume : Measure (ComplexModel m)).prod (volume : Measure ℂ))

theorem splitFactor_pos (m : ℕ) : 0 < splitFactor m :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem map_splitEquiv_volume :
    (volume : Measure (ComplexModel (m + 1))).map (splitEquiv m) =
      (splitFactor m : ℝ≥0∞) • ((volume : Measure (ComplexModel m)).prod (volume : Measure ℂ)) :=
  Measure.isAddLeftInvariant_eq_smul _ _

theorem lintegral_eq_splitFactor_mul (G : ComplexModel (m + 1) → ℝ≥0∞) :
    ∫⁻ z, G z = splitFactor m *
      ∫⁻ q, G (sliceMap m q.2 q.1) ∂((volume : Measure (ComplexModel m)).prod volume) := by
  have h := lintegral_map_equiv (fun q ↦ G ((splitEquiv m).symm q)) (splitEquiv m)
    (μ := (volume : Measure (ComplexModel (m + 1))))
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [← h, map_splitEquiv_volume, lintegral_smul_measure]
  rfl

theorem norm_sq_eq_initCoords (x : ComplexModel (m + 1)) :
    ‖x‖ ^ 2 = ‖initCoords x‖ ^ 2 + ‖x (Fin.last m)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp

theorem initCoords_sub (x y : ComplexModel (m + 1)) :
    initCoords (x - y) = initCoords x - initCoords y := by
  ext i; simp

/-- **Integrals supported near the hyperplane.** -/
theorem lintegral_le_of_le_indicator_closedBall {G : ComplexModel (m + 1) → ℝ≥0∞}
    {g : ComplexModel m → ℝ≥0∞} (hg : AEMeasurable g) {ε : ℝ}
    (hG : ∀ z, G z ≤ (closedBall (0 : ℂ) ε).indicator (fun _ ↦ g (initCoords z))
      (z (Fin.last m))) :
    ∫⁻ z, G z ≤ splitFactor m * (volume (closedBall (0 : ℂ) ε) * ∫⁻ w, g w) := by
  calc ∫⁻ z, G z
      ≤ ∫⁻ z, g (initCoords z) * (closedBall (0 : ℂ) ε).indicator 1 (z (Fin.last m)) := by
        refine lintegral_mono fun z ↦ (hG z).trans_eq ?_
        by_cases hz : z (Fin.last m) ∈ closedBall (0 : ℂ) ε <;> simp [hz]
    _ = splitFactor m * ((∫⁻ w, g w) * volume (closedBall (0 : ℂ) ε)) := by
        rw [lintegral_eq_splitFactor_mul]
        simp only [initCoords_sliceMap, sliceMap_last]
        rw [lintegral_prod_mul (f := g) (g := (closedBall (0 : ℂ) ε).indicator 1) hg
          (aemeasurable_one.indicator measurableSet_closedBall)]
        rw [lintegral_indicator measurableSet_closedBall]
        simp
    _ = _ := by ring

/-- `∫_{|u| < ρ} c |u|^{-2} = ∞` in `ℂ`. -/
theorem lintegral_ball_div_normSq_eq_top {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) :
    ∫⁻ u in ball (0 : ℂ) ρ, ENNReal.ofReal (c / ‖u‖ ^ 2) = ⊤ := by
  by_contra hfin
  set f : ℂ → ℝ≥0∞ := fun u ↦ ENNReal.ofReal (c / ‖u‖ ^ 2) with hf
  set κ : Measure ℂ := (volume.restrict (ball (0 : ℂ) ρ)).withDensity f with hκ
  have hκfin : IsFiniteMeasure κ := isFiniteMeasure_withDensity hfin
  set B : ℕ → Set ℂ := fun k ↦ ball (0 : ℂ) (ρ / ((k : ℝ) + 1)) with hB
  have hBpos : ∀ k : ℕ, 0 < ρ / ((k : ℝ) + 1) := fun k ↦ by positivity
  have hBρ : ∀ k : ℕ, ρ / ((k : ℝ) + 1) ≤ ρ := fun k ↦
    div_le_self hρ.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hanti : Antitone B := by
    intro i j hij
    refine ball_subset_ball (div_le_div_of_nonneg_left hρ.le (by positivity) ?_)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hinter : (⋂ k, B k) = {0} := by
    ext u
    simp only [mem_iInter, hB, mem_ball, dist_zero_right, mem_singleton_iff]
    constructor
    · intro h
      by_contra hu
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      obtain ⟨k, hk⟩ := exists_nat_gt (ρ / ‖u‖)
      have := h k
      rw [lt_div_iff₀ (by positivity)] at this
      rw [div_lt_iff₀ hpos] at hk
      nlinarith
    · rintro rfl k
      simpa using hBpos k
  have hlim := tendsto_measure_iInter_atTop (μ := κ) (fun k ↦ measurableSet_ball.nullMeasurableSet)
    hanti ⟨0, measure_ne_top κ _⟩
  rw [hinter] at hlim
  have h0 : κ {0} = 0 := by
    rw [hκ, withDensity_apply _ (measurableSet_singleton 0)]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact measure_mono_null inter_subset_left (measure_singleton 0)
  rw [h0] at hlim
  have hlow : ∀ k, ENNReal.ofReal (c * Real.pi) ≤ κ (B k) := by
    intro k
    set η := ρ / ((k : ℝ) + 1) with hη
    have hηpos := hBpos k
    rw [hκ, withDensity_apply _ measurableSet_ball,
      Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball (hBρ k))]
    calc ENNReal.ofReal (c * Real.pi)
        = ∫⁻ u in ball (0 : ℂ) η, ENNReal.ofReal (c / η ^ 2) := by
          rw [setLIntegral_const, Complex.volume_ball, ← ENNReal.ofReal_pow hηpos.le,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_mul_cancel₀ _ (pow_ne_zero 2 hηpos.ne')]
      _ ≤ ∫⁻ u in ball (0 : ℂ) η, f u := by
          have hnull : ∀ᵐ u ∂(volume.restrict (ball (0 : ℂ) η)), u ≠ 0 :=
            ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ)))
          refine lintegral_mono_ae ?_
          filter_upwards [hnull, ae_restrict_mem measurableSet_ball] with u hu0 hu
          rw [mem_ball, dist_zero_right] at hu
          refine ENNReal.ofReal_le_ofReal ?_
          have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          exact div_le_div_of_nonneg_left hc.le (by positivity)
            (pow_le_pow_left₀ hpos.le hu.le 2)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (c * Real.pi) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  exact absurd (ge_of_tendsto' hlim hlow) (not_le.mpr hpos)

/-- `∫_{B(p, r)} c |z_{m+1}|^{-2} = ∞` for `p` on the hyperplane. -/
theorem lintegral_ball_div_normSq_last_eq_top {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∫⁻ z in ball p r, ENNReal.ofReal (c / ‖z (Fin.last m)‖ ^ 2) = ⊤ := by
  set B' := ball (initCoords p) (r / 2) with hB'
  set D₀ := ball (0 : ℂ) (r / 2) with hD₀
  set g : ℂ → ℝ≥0∞ := fun u ↦ ENNReal.ofReal (c / ‖u‖ ^ 2) with hg
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.div ((continuous_norm.pow 2).measurable)
  have hsub : ∀ z, B'.indicator 1 (initCoords z) * D₀.indicator g (z (Fin.last m)) ≤
      (ball p r).indicator (fun z ↦ g (z (Fin.last m))) z := by
    intro z
    by_cases h1 : initCoords z ∈ B'
    · by_cases h2 : z (Fin.last m) ∈ D₀
      · have hz : z ∈ ball p r := by
          rw [mem_ball, dist_eq_norm]
          rw [hB', mem_ball, dist_eq_norm] at h1
          rw [hD₀, mem_ball, dist_zero_right] at h2
          have hn := norm_sq_eq_initCoords (z - p)
          rw [initCoords_sub] at hn
          simp only [PiLp.sub_apply, hp, sub_zero] at hn
          have h1' : ‖initCoords z - initCoords p‖ ^ 2 < (r / 2) ^ 2 :=
            pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
          have h2' : ‖z (Fin.last m)‖ ^ 2 < (r / 2) ^ 2 :=
            pow_lt_pow_left₀ h2 (norm_nonneg _) two_ne_zero
          have : ‖z - p‖ ^ 2 < r ^ 2 := by nlinarith
          exact lt_of_pow_lt_pow_left₀ 2 hr.le this
        simp [h1, h2, hz]
      · simp [h2]
    · simp [h1]
  have hB'pos : volume B' ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  refine top_le_iff.mp ?_
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ z, B'.indicator 1 (initCoords z) * D₀.indicator g (z (Fin.last m)) := by
        rw [lintegral_eq_splitFactor_mul]
        simp only [initCoords_sliceMap, sliceMap_last]
        rw [lintegral_prod_mul (f := B'.indicator 1) (g := D₀.indicator g)
          (aemeasurable_one.indicator measurableSet_ball)
          (hgm.indicator measurableSet_ball).aemeasurable,
          lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball,
          lintegral_ball_div_normSq_eq_top (by positivity) hc]
        simp only [Pi.one_apply, setLIntegral_const, one_mul]
        rw [ENNReal.mul_top hB'pos, ENNReal.mul_top]
        exact_mod_cast (splitFactor_pos m).ne'
    _ ≤ ∫⁻ z, (ball p r).indicator (fun z ↦ g (z (Fin.last m))) z := lintegral_mono hsub
    _ = ∫⁻ z in ball p r, g (z (Fin.last m)) := lintegral_indicator measurableSet_ball _

/-- **Vanishing on the hyperplane.**  A continuous `u` with `∫ |u|² W / |z_{m+1}|² < ∞` for a
continuous positive `W` vanishes on the hyperplane. -/
theorem eq_zero_of_lintegral_div_normSq_ne_top {K : Set (ComplexModel (m + 1))} (hK : IsOpen K)
    {u : ComplexModel (m + 1) → ℂ} {W : ComplexModel (m + 1) → ℝ} (hu : ContinuousOn u K)
    (hW : ContinuousOn W K) (hWpos : ∀ z ∈ K, 0 < W z)
    (hfin : ∫⁻ z in K, ENNReal.ofReal (‖u z‖ ^ 2 * W z / ‖z (Fin.last m)‖ ^ 2) ≠ ⊤)
    {p : ComplexModel (m + 1)} (hpK : p ∈ K) (hp : p (Fin.last m) = 0) : u p = 0 := by
  by_contra hup
  set a := ‖u p‖ ^ 2 * W p with ha
  have hapos : 0 < a := mul_pos (by positivity) (hWpos p hpK)
  have hcont : ContinuousAt (fun z ↦ ‖u z‖ ^ 2 * W z) p :=
    ((hu.norm.pow 2).mul hW).continuousAt (hK.mem_nhds hpK)
  have hev : ∀ᶠ z in 𝓝 p, a / 2 < ‖u z‖ ^ 2 * W z ∧ z ∈ K :=
    (hcont.eventually (lt_mem_nhds (by linarith))).and (hK.mem_nhds hpK)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  apply hfin
  refine top_le_iff.mp ?_
  rw [← lintegral_ball_div_normSq_last_eq_top hp hr (half_pos hapos)]
  calc ∫⁻ z in ball p r, ENNReal.ofReal (a / 2 / ‖z (Fin.last m)‖ ^ 2)
      ≤ ∫⁻ z in ball p r, ENNReal.ofReal (‖u z‖ ^ 2 * W z / ‖z (Fin.last m)‖ ^ 2) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz ↦ ?_
        exact ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (hball hz).1.le (by positivity))
    _ ≤ _ := lintegral_mono_set fun z hz ↦ (hball hz).2

end

end Hironaka.OTChen
