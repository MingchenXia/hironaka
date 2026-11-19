import Hironaka.Resolution.HironakaActualCauchyMonomialDivision

/-!
# Actual whole Taylor coefficient bounds and uniform analytic limits

The actual finite Cauchy quotients produce the coefficient functional bound.
The support of a genuine uniform holomorphic limit then follows coefficientwise,
without a supplied commutation rule between an analytic sum and a formal series.
-/

set_option autoImplicit false
open Set Metric Filter
open scoped Topology

namespace Hironaka.HironakaActualCauchyCoefficientLimits

noncomputable section

open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision

variable {n : ℕ}

/-- The actual original Hadamard decomposition determines the genuine coefficient at zero. -/
theorem actualTaylor_coeff_zero (g : HolGerm (ComplexModel n)) :
    MvPowerSeries.coeff 0 (actualUnshiftedTaylorAlgHom n g) = HolGerm.eval g := by
  obtain ⟨H,hH⟩ := exists_coordinate_decomposition g
  have hc : actualUnshiftedTaylorAlgHom n (HolGerm.constHom (HolGerm.eval g)) =
      MvPowerSeries.C (HolGerm.eval g) := (actualUnshiftedTaylorAlgHom n).commutes _
  change MvPowerSeries.constantCoeff (actualUnshiftedTaylorAlgHom n g) = _
  conv_lhs => rw [hH,map_add,map_sum,hc,map_add,map_sum]
  simp only [map_mul,actualUnshiftedTaylor_coordinate,MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C,zero_mul,Finset.sum_const_zero,add_zero]

theorem actualTaylor_coeff_eq_wordQuot_zero {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {h : CoordinateSpace n → ℂ} (hh : DifferentiableOn ℂ h (ball 0 R))
    (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) =
      wordQuot ρ (wordOfExponent a) h 0 := by
  have hc := coeff_wordQuotGerm hρ hρR (wordOfExponent a) hh 0
  rw [zero_add,wordExponent_wordOfExponent,actualTaylor_coeff_zero] at hc
  change HolGerm.eval (HolGerm.mk (modelFunction (wordQuot ρ (wordOfExponent a) h)) _) = _ at hc
  rw [HolGerm.eval_mk] at hc
  simpa only [modelFunction,Function.comp_apply,map_zero] using hc.symm

/-- A constant for each true original Taylor coefficient is internally produced by actual Cauchy division. -/
theorem exists_actualTaylorCoefficient_bound {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (a : Fin n →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (h : CoordinateSpace n → ℂ)
      (hh : DifferentiableOn ℂ h (ball 0 R)),
      (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
        ‖MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh))‖ ≤ C * M := by
  obtain ⟨C,hC,hq⟩ := exists_wordQuot_bound hρ hρR (wordOfExponent a)
  refine ⟨C,hC,?_⟩
  intro M h hh hM
  rw [actualTaylor_coeff_eq_wordQuot_zero hρ hρR hh a]
  exact hq M h hh hM 0 (mem_ball_self (hρ.trans hρR))

private theorem modelGerm_sub {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.sub hg) = modelGerm hR hf - modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z - modelFunction g z) _ = _
  exact HolGerm.mk_sub _ _ _ _

/-- Forbidden whole Taylor coefficients stay zero under genuine uniform holomorphic limits. -/
theorem coeff_eq_zero_of_uniform_limit {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {f : ℕ → CoordinateSpace n → ℂ} {g : CoordinateSpace n → ℂ}
    (hf : ∀ N, DifferentiableOn ℂ (f N) (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hlim : TendstoUniformlyOn f g atTop (ball (0 : CoordinateSpace n) R))
    (a : Fin n →₀ ℕ)
    (hzero : ∀ N, MvPowerSeries.coeff a
      (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) (hf N))) = 0) :
    MvPowerSeries.coeff a
      (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hg)) = 0 := by
  by_contra hne
  obtain ⟨C,hC,hbound⟩ := exists_actualTaylorCoefficient_bound hρ hρR a
  let u := ‖MvPowerSeries.coeff a
    (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hg))‖
  have hu : 0 < u := norm_pos_iff.mpr hne
  let δ := u / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hu (by positivity)
  obtain ⟨N,hN⟩ := ((Metric.tendstoUniformlyOn_iff.mp hlim) δ hδ).exists
  have hnorm : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖g z - f N z‖ ≤ δ := by
    intro z hz
    have hlt : ‖g z - f N z‖ < δ := by simpa only [dist_eq_norm] using hN z hz
    exact hlt.le
  have hb := hbound δ (fun z => g z - f N z) (hg.sub (hf N)) hnorm
  rw [modelGerm_sub (hρ.trans hρR) hg (hf N),map_sub,map_sub,hzero N,sub_zero] at hb
  have hlt : C * δ < u := by
    dsimp only [δ]
    rw [← mul_div_assoc,div_lt_iff₀ (show 0 < 2 * (C + 1) by positivity)]
    have hCu : 0 ≤ C * u := mul_nonneg hC hu.le
    nlinarith
  exact (not_lt_of_ge hb) hlt

end

end Hironaka.HironakaActualCauchyCoefficientLimits
