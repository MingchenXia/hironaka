import Hironaka.Resolution.HironakaActualCauchyCoordinateDivision
import Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality
import Hironaka.Resolution.HironakaActualPointExceptionalFibreRadial

/-!
# Actual coordinate retractions and entire Taylor support

The actual germ pullback, not a prescribed formal support predicate, identifies
coordinate independence with the literal formal zero-coordinate projection.
-/

set_option autoImplicit false
open Set Metric

namespace Hironaka.HironakaActualCauchyTaylorSupport

noncomputable section

open HolGerm HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
  HironakaActualTaylorCoordinateNaturality HironakaActualFormalCoordinatePowerDivision
  HironakaActualPointExceptionalFibreRadial HironakaActualCauchyCoordinateDivision

variable {n : ℕ}

/-- The genuine original germ pullback of the actual coordinate retraction. -/
def coordinateKillPullback (i : Fin n) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (HolomorphicTaylorTail.killCoord i)
    (Filter.Eventually.of_forall fun _ => (HolomorphicTaylorTail.killCoord i).differentiableAt)
    (map_zero _)

theorem coordinateKillPullback_coordinate (i j : Fin n) :
    coordinateKillPullback i (coordinateGerm j) =
      if j = i then 0 else coordinateGerm j := by
  unfold coordinateKillPullback coordinateGerm
  rw [compAlgHom_mk]
  by_cases hj : j = i
  · subst j
    rw [if_pos rfl,← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Filter.Eventually.of_forall fun z => by
      simp only [Function.comp_apply,HolomorphicTaylorTail.killCoord_apply_apply,ite_true,Pi.zero_apply]
  · rw [if_neg hj]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Filter.Eventually.of_forall fun z => by
      simp only [Function.comp_apply,HolomorphicTaylorTail.killCoord_apply_apply,if_neg hj]

/-- Coordinate identities determine the SAME whole Taylor pullback algebra map. -/
theorem actualTaylor_coordinateKillPullback (i : Fin n) :
    (actualUnshiftedTaylorAlgHom n).comp (coordinateKillPullback i) =
      (actualPointExceptionalProjection i).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro j
    change actualUnshiftedTaylorAlgHom n (coordinateKillPullback i (coordinateGerm j)) =
      actualPointExceptionalProjection i (actualUnshiftedTaylorAlgHom n (coordinateGerm j))
    rw [coordinateKillPullback_coordinate,actualUnshiftedTaylor_coordinate,
      actualPointExceptionalProjection_X]
    split_ifs <;> simp only [map_zero,actualUnshiftedTaylor_coordinate]
  · intro j
    change actualUnshiftedTaylorAlgHom n (coordinateKillPullback i (coordinateGerm j)) ∈ _
    rw [coordinateKillPullback_coordinate]
    split_ifs
    · rw [map_zero]
      exact Ideal.zero_mem _
    · rw [actualUnshiftedTaylor_coordinate]
      exact Ideal.subset_span ⟨j,mem_univ _,rfl⟩

/-- Whole positive-coordinate Taylor coefficients vanish from an actual original
germ's genuine retraction invariance; no convergence or formal-support premise. -/
theorem coeff_eq_zero_of_coordinateKill_fixed (i : Fin n)
    (g : HolGerm (ComplexModel n)) (hg : coordinateKillPullback i g = g)
    (a : Fin n →₀ ℕ) (ha : a i ≠ 0) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n g) = 0 := by
  have hm := congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ]
      MvPowerSeries (Fin n) ℂ => f g) (actualTaylor_coordinateKillPullback i)
  change actualUnshiftedTaylorAlgHom n (coordinateKillPullback i g) =
    actualPointExceptionalProjection i (actualUnshiftedTaylorAlgHom n g) at hm
  rw [hg] at hm
  have hc := congrArg (MvPowerSeries.coeff a) hm
  rw [coeff_actualPointExceptionalProjection,if_neg ha] at hc
  exact hc

def modelFunction (h : CoordinateSpace n → ℂ) : ComplexModel n → ℂ :=
  h ∘ EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)

theorem modelFunction_holAt {h : CoordinateSpace n → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R)) :
    OkaRelationSheaf.HolAt (modelFunction h) 0 := by
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  have ht : Filter.Tendsto e (nhds (0 : ComplexModel n))
      (nhds (0 : CoordinateSpace n)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually (isOpen_ball.mem_nhds (Metric.mem_ball_self hR))] with z hz
  exact (hh.differentiableAt (isOpen_ball.mem_nhds hz)).comp z e.differentiableAt

def modelGerm {h : CoordinateSpace n → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R)) :
    HolGerm (ComplexModel n) :=
  HolGerm.mk (modelFunction h) (modelFunction_holAt hR hh)

/-- This is the actual Cauchy coefficient germ on the original Euclidean model. -/
def coordinateCoefficientGerm {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (k : ℕ) : HolGerm (ComplexModel n) :=
  modelGerm (hρ.trans hρR) (coordinateCoeff_differentiableOn hρ hρR hh i k)

/-- Genuine representative-function independence fixes the actual original coefficient germ. -/
theorem coordinateCoefficientGerm_fixed {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (k : ℕ) :
    coordinateKillPullback i (coordinateCoefficientGerm hρ hρR hh i k) =
      coordinateCoefficientGerm hρ hρR hh i k := by
  unfold coordinateCoefficientGerm modelGerm coordinateKillPullback
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  refine Filter.Eventually.of_forall fun z => ?_
  change coordinateCoeff h i ρ k
      (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) (HolomorphicTaylorTail.killCoord i z)) =
    coordinateCoeff h i ρ k (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z)
  have he : EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) (HolomorphicTaylorTail.killCoord i z) =
      coordinateInsert i (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,0) := by
    funext j
    change HolomorphicTaylorTail.killCoord i z j = coordinateInsert i
      (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,0) j
    rw [coordinateInsert_apply]
    exact HolomorphicTaylorTail.killCoord_apply_apply i j z
  rw [he,coordinateCoeff_insert]

/-- The actual Cauchy construction produces the whole support conclusion internally. -/
theorem coordinateCoefficientGerm_Taylor_support {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (k : ℕ) (a : Fin n →₀ ℕ) (ha : a i ≠ 0) :
    MvPowerSeries.coeff a
      (actualUnshiftedTaylorAlgHom n (coordinateCoefficientGerm hρ hρR hh i k)) = 0 :=
  coeff_eq_zero_of_coordinateKill_fixed i _
    (coordinateCoefficientGerm_fixed hρ hρR hh i k) a ha

def coordinateLowGerm {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (d : ℕ) : HolGerm (ComplexModel n) :=
  modelGerm (hρ.trans hρR) (coordinateLow_differentiableOn hρ hρR hh i d)

theorem coordinateLowGerm_eq_sum {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (d : ℕ) :
    coordinateLowGerm hρ hρR hh i d =
      ∑ k ∈ Finset.range d, coordinateCoefficientGerm hρ hρR hh i k * coordinateGerm i ^ k := by
  have hc (k : ℕ) := modelFunction_holAt (hρ.trans hρR)
    (coordinateCoeff_differentiableOn hρ hρR hh i k)
  have hz : OkaRelationSheaf.HolAt (fun z : ComplexModel n => z i) 0 :=
    Filter.Eventually.of_forall fun _ =>
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hterm (k : ℕ) : OkaRelationSheaf.HolAt
      (fun z : ComplexModel n => modelFunction (coordinateCoeff h i ρ k) z * z i ^ k) 0 :=
    eventually_differentiableAt_mul (hc k)
      (eventually_differentiableAt_pow hz k)
  change HolGerm.mk (fun z : ComplexModel n =>
      ∑ k ∈ Finset.range d, modelFunction (coordinateCoeff h i ρ k) z * z i ^ k)
    (eventually_differentiableAt_sum (Finset.range d) hterm) = _
  rw [HolGerm.mk_sum (Finset.range d) _ hterm]
  apply Finset.sum_congr rfl
  intro k _hk
  change HolGerm.mk (fun z : ComplexModel n =>
      modelFunction (coordinateCoeff h i ρ k) z * z i ^ k) (hterm k) =
    HolGerm.mk (modelFunction (coordinateCoeff h i ρ k)) (hc k) *
      (HolGerm.mk (fun z => z i) hz) ^ k
  rw [HolGerm.mk_mul _ _ (hc k) (eventually_differentiableAt_pow hz k),
    HolGerm.mk_pow _ hz k]

theorem coordinate_modelGerm_difference {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (d : ℕ) :
    modelGerm (hρ.trans hρR) hh - coordinateLowGerm hρ hρR hh i d =
      coordinateGerm i ^ d * modelGerm (hρ.trans hρR)
        (coordinateQuot_differentiableOn hρ hρR hh i d) := by
  unfold coordinateLowGerm modelGerm coordinateGerm
  rw [← HolGerm.mk_sub,← HolGerm.mk_pow,← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  have ht : Filter.Tendsto e (nhds (0 : ComplexModel n))
      (nhds (0 : CoordinateSpace n)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually
    (isOpen_ball.mem_nhds (Metric.mem_ball_self (hρ.trans hρR)))] with z hz
  have he := coordinate_division_identity hρ hρR hh i d hz
  change h (e z) - coordinateLow h i ρ d (e z) = z i ^ d * coordinateQuot h i ρ d (e z)
  change h (e z) = coordinateQuot h i ρ d (e z) * z i ^ d + coordinateLow h i ρ d (e z) at he
  linear_combination he

private theorem coeff_coordinateLowGerm_eq_zero_of_ge
    {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (d : ℕ) (a : Fin n →₀ ℕ) (ha : d ≤ a i) :
    MvPowerSeries.coeff a
      (actualUnshiftedTaylorAlgHom n (coordinateLowGerm hρ hρR hh i d)) = 0 := by
  rw [coordinateLowGerm_eq_sum,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate,MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_mul_monomial]
  split_ifs with hle
  · have hpos : (a - Finsupp.single i k) i ≠ 0 := by
      have hklt : k < d := Finset.mem_range.mp hk
      simp only [Finsupp.tsub_apply,Finsupp.single_eq_same]
      omega
    rw [coordinateCoefficientGerm_Taylor_support hρ hρR hh i k _ hpos,zero_mul]
  · rfl

/-- The ENTIRE original Taylor mask is produced from the real Cauchy operator,
its finite analytic coefficient functions, and its actual germ division identity. -/
theorem coeff_coordinateLowGerm {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (d : ℕ) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a
      (actualUnshiftedTaylorAlgHom n (coordinateLowGerm hρ hρR hh i d)) =
      if a i < d then MvPowerSeries.coeff a
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 := by
  by_cases ha : a i < d
  · rw [if_pos ha]
    have hdiv : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) ^ d ∣
        actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh) -
          actualUnshiftedTaylorAlgHom n (coordinateLowGerm hρ hρR hh i d) := by
      refine ⟨actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR)
        (coordinateQuot_differentiableOn hρ hρR hh i d)),?_⟩
      have hm := congrArg (actualUnshiftedTaylorAlgHom n)
        (coordinate_modelGerm_difference hρ hρR hh i d)
      simpa only [map_sub,map_mul,map_pow,actualUnshiftedTaylor_coordinate] using hm
    have hz := (MvPowerSeries.X_pow_dvd_iff.mp hdiv) a ha
    rw [map_sub,sub_eq_zero] at hz
    exact hz.symm
  · rw [if_neg ha]
    exact coeff_coordinateLowGerm_eq_zero_of_ge hρ hρR hh i d a (Nat.le_of_not_gt ha)

/-- Every whole coefficient of the actual analytic quotient is the literal
shifted coefficient of the actual input germ. -/
theorem coeff_coordinateQuotGerm {h : CoordinateSpace n → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (i : Fin n) (d : ℕ) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
        (modelGerm (hρ.trans hρR) (coordinateQuot_differentiableOn hρ hρR hh i d))) =
      MvPowerSeries.coeff (a + Finsupp.single i d)
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) := by
  have hm := congrArg (actualUnshiftedTaylorAlgHom n)
    (coordinate_modelGerm_difference hρ hρR hh i d)
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single i d + a)) hm
  simp only [map_sub,map_mul,map_pow,actualUnshiftedTaylor_coordinate,
    MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_add_monomial_mul,one_mul] at hc
  have ha : d ≤ (Finsupp.single i d + a) i := by simp
  rw [coeff_coordinateLowGerm_eq_zero_of_ge hρ hρR hh i d _ ha,sub_zero] at hc
  simpa only [add_comm] using hc.symm

end

end Hironaka.HironakaActualCauchyTaylorSupport
