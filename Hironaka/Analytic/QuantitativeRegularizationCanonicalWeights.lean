import Hironaka.Analytic.QuantitativeRegularizationCanonicalRadii

set_option autoImplicit false

/-! # Monotone measurable canonical point-pole weights -/

open Set MeasureTheory
open scoped ENNReal

namespace Hironaka.QuantitativeRegularizationCanonicalWeights

noncomputable section



variable {d p : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- The nonnegative exponential weight for the canonical point-pole radius. -/
def canonicalWeight (p : ℕ) (φ : ComplexModel d → ℝ) (x : ComplexModel d) (i : ℕ)
    (z : ComplexModel d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-PointPole.poleWeight p φ x
    (QuantitativeRegularizationCanonicalRadii.canonicalRadius i) z))

omit [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)] in
/-- Shrinking canonical radii make the exponential point-pole weights
monotone increasing. -/
theorem canonicalWeight_monotone {φ : ComplexModel d → ℝ}
    (x z : ComplexModel d) : Monotone fun i => canonicalWeight p φ x i z := by
  intro i j hij
  apply ENNReal.ofReal_le_ofReal
  rw [PointPole.exp_neg_poleWeight φ x
    (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos i) z,
    PointPole.exp_neg_poleWeight φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos j) z]
  have hδ : QuantitativeRegularizationCanonicalRadii.canonicalRadius j ≤
      QuantitativeRegularizationCanonicalRadii.canonicalRadius i :=
    QuantitativeRegularizationCanonicalRadii.canonicalRadius_antitone hij
  have hsq : QuantitativeRegularizationCanonicalRadii.canonicalRadius j ^ 2 ≤
      QuantitativeRegularizationCanonicalRadii.canonicalRadius i ^ 2 :=
    (sq_le_sq₀
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos j).le
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos i).le).mpr hδ
  have hbase : 0 < ‖z - x‖ ^ 2 +
      QuantitativeRegularizationCanonicalRadii.canonicalRadius j ^ 2 := by
    nlinarith [sq_nonneg ‖z - x‖,
      sq_pos_of_pos (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos j)]
  have hden : ‖z - x‖ ^ 2 +
      QuantitativeRegularizationCanonicalRadii.canonicalRadius j ^ 2 ≤
      ‖z - x‖ ^ 2 +
      QuantitativeRegularizationCanonicalRadii.canonicalRadius i ^ 2 := by
    linarith
  have hinv : ((‖z - x‖ ^ 2 +
      QuantitativeRegularizationCanonicalRadii.canonicalRadius i ^ 2) ^ p)⁻¹ ≤
      ((‖z - x‖ ^ 2 +
      QuantitativeRegularizationCanonicalRadii.canonicalRadius j ^ 2) ^ p)⁻¹ :=
    inv_anti₀ (pow_pos hbase p) (pow_le_pow_left₀ hbase.le hden p)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le) (Real.exp_pos _).le

/-- On an open set where `φ` is continuous, every canonical weight is almost
everywhere measurable for the restricted volume. -/
theorem canonicalWeight_aemeasurable {U : Set (ComplexModel d)} (hU : IsOpen U)
    {φ : ComplexModel d → ℝ} (hφ : ContinuousOn φ U) (x : ComplexModel d) (i : ℕ) :
    AEMeasurable (canonicalWeight p φ x i) (volume.restrict U) := by
  have hpole : Continuous (PointPole.polePotential x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius i)) :=
    (PointPole.contDiff_polePotential (n := 1)
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos i) x).continuous
  have hweight : ContinuousOn (PointPole.poleWeight p φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius i)) U := by
    change ContinuousOn
      ((φ + (fun _ : ComplexModel d => (p : ℝ)) *
        PointPole.polePotential x
          (QuantitativeRegularizationCanonicalRadii.canonicalRadius i)) +
        fun z => ‖z‖ ^ 2) U
    exact (hφ.add (continuous_const.mul hpole).continuousOn).add
      (continuous_norm.pow 2).continuousOn
  apply ContinuousOn.aemeasurable _ hU.measurableSet
  change ContinuousOn (fun z => ENNReal.ofReal (Real.exp
    (-PointPole.poleWeight p φ x
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius i) z))) U
  exact ENNReal.continuous_ofReal.comp_continuousOn'
    (Real.continuous_exp.comp_continuousOn'
      (continuous_neg.comp_continuousOn' hweight))

/-- The canonical point-pole weights provide the monotonicity and restricted
measurability inputs of the pole-limit bridge. -/
theorem canonicalWeight_monotone_and_aemeasurable {U : Set (ComplexModel d)}
    (hU : IsOpen U) {φ : ComplexModel d → ℝ} (hφ : ContinuousOn φ U)
    (x : ComplexModel d) :
    (∀ z ∈ U, Monotone fun i => canonicalWeight p φ x i z) ∧
      ∀ i, AEMeasurable (canonicalWeight p φ x i) (volume.restrict U) :=
  ⟨fun _ _ => canonicalWeight_monotone x _,
    fun i => canonicalWeight_aemeasurable hU hφ x i⟩

end

end Hironaka.QuantitativeRegularizationCanonicalWeights
