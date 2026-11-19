import Hironaka.Analytic.QuantitativeRegularizationCanonicalWeights
import Hironaka.Analytic.QuantitativeRegularizationPoleLimit

set_option autoImplicit false

/-! # Canonical point-pole limits for quantitative regularization -/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace Hironaka.QuantitativeRegularizationCanonicalLimit

noncomputable section



variable {d p : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

omit [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)] in
/-- Continuity of the local potential makes the zeroth canonical weight locally
bounded below by a positive real constant. -/
theorem canonicalWeight_zero_locally_lower_bounded {U : Set (ComplexModel d)}
    (hU : IsOpen U) {φ : ComplexModel d → ℝ} (hφ : ContinuousOn φ U)
    (x : ComplexModel d) :
    ∀ z ∈ U, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball z r,
      ENNReal.ofReal δ ≤
        QuantitativeRegularizationCanonicalWeights.canonicalWeight p φ x 0 y := by
  intro z hz
  have hφAt : ContinuousAt φ z := (hφ z hz).continuousAt (hU.mem_nhds hz)
  have hpole : Continuous (PointPole.polePotential x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0)) :=
    (PointPole.contDiff_polePotential (n := 1)
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos 0) x).continuous
  have hweight : ContinuousAt (PointPole.poleWeight p φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0)) z := by
    change ContinuousAt
      ((φ + (fun _ : ComplexModel d => (p : ℝ)) *
        PointPole.polePotential x
          (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0)) +
        fun y => ‖y‖ ^ 2) z
    exact (hφAt.add (continuousAt_const.mul hpole.continuousAt)).add
      (continuous_norm.pow 2).continuousAt
  have hexp : ContinuousAt (fun y => Real.exp (-PointPole.poleWeight p φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0) y)) z := by
    exact Real.continuous_exp.continuousAt.comp
      (continuous_neg.continuousAt.comp hweight)
  let a : ℝ := Real.exp (-PointPole.poleWeight p φ x
    (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0) z)
  have ha : 0 < a := Real.exp_pos _
  have hevent : ∀ᶠ y in 𝓝 z, a / 2 < Real.exp (-PointPole.poleWeight p φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0) y) :=
    continuousAt_const.eventually_lt hexp (by dsimp [a]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent
  refine ⟨r, hr, a / 2, by linarith, ?_⟩
  intro y hy
  change ENNReal.ofReal (a / 2) ≤ ENNReal.ofReal (Real.exp
    (-PointPole.poleWeight p φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius 0) y))
  exact ENNReal.ofReal_le_ofReal (hball y hy).le

/-- With canonical radii, a uniform weighted `L²` bound produces a strict
subsequence converging locally uniformly to a holomorphic function that
vanishes at the marked point. Monotonicity, measurability, local lower
positivity, and domination by every fixed pole are supplied here. -/
theorem exists_subseq_differentiableOn_vanishing_limit_of_canonical_weighted_bounds
    {U : Set (ComplexModel d)} (hU : IsOpen U) {x : ComplexModel d} (hx : x ∈ U)
    {φ : ComplexModel d → ℝ} (hφ : ContinuousOn φ U)
    {F : ℕ → ComplexModel d → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ z in U, ENNReal.ofReal (‖F i z‖ ^ 2) *
      QuantitativeRegularizationCanonicalWeights.canonicalWeight (d + 1) φ x i z ≤ A)
    (hd : 0 < d) {B R : ℝ}
    (hφupper : ∀ z ∈ U, φ z ≤ B) (hnorm : ∀ z ∈ U, ‖z - x‖ ≤ R) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel d → ℂ), StrictMono ψ ∧
      DifferentiableOn ℂ G U ∧
      TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop U ∧
      G x = 0 ∧
      ∫⁻ z in U, ENNReal.ofReal (‖G z‖ ^ 2) *
        ⨆ i, QuantitativeRegularizationCanonicalWeights.canonicalWeight (d + 1) φ x i z ≤ A := by
  obtain ⟨hwm, hwmeas⟩ :=
    QuantitativeRegularizationCanonicalWeights.canonicalWeight_monotone_and_aemeasurable
      (p := d + 1) hU hφ x
  let c : ℝ := Real.exp (-B - (‖x‖ + R) ^ 2)
  have hc : 0 < c := Real.exp_pos _
  refine Hironaka.QuantitativeRegularizationPoleLimit.exists_subseq_differentiableOn_vanishing_limit_of_pole_dominated_bounds
      hU hx hwm hwmeas
      (canonicalWeight_zero_locally_lower_bounded (p := d + 1) hU hφ x)
      hF hA hbound hd hc ?_
  intro η hη z hz
  simpa only [c, QuantitativeRegularizationCanonicalWeights.canonicalWeight] using
    QuantitativeRegularizationCanonicalRadii.canonicalRadius_inverse_pole_le_iSup_exp_neg_poleWeight
        (p := d + 1) (x := x) (z := z) (A := B) (R := R)
        (hφupper z hz) (hnorm z hz) hη

end

end Hironaka.QuantitativeRegularizationCanonicalLimit
