import Hironaka.Resolution.HironakaActualCauchyTaylorSupport

/-!
# Concrete Cauchy quotients and monomial cone projectors

Every operator is a finite composition of actual coordinate Cauchy quotients.
Its same-domain bound and its entire original Taylor mask are conclusions.
No bounded-operator or formal-convergence input is used.
-/

set_option autoImplicit false
open Set Metric

namespace Hironaka.HironakaActualCauchyMonomialDivision

noncomputable section

open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport

variable {n : ℕ}

abbrev CoordinateWord (n : ℕ) := List (Fin n × ℕ)

def wordExponent : CoordinateWord n → Fin n →₀ ℕ
  | [] => 0
  | (i,d) :: w => Finsupp.single i d + wordExponent w

def wordDegree : CoordinateWord n → ℕ
  | [] => 0
  | (_,d) :: w => d + wordDegree w

def wordOfExponent (a : Fin n →₀ ℕ) : CoordinateWord n :=
  List.ofFn fun i => (i,a i)

private theorem wordExponent_eq_sum (w : CoordinateWord n) :
    wordExponent w = (w.map fun p => Finsupp.single p.1 p.2).sum := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    simp only [wordExponent,List.map_cons,List.sum_cons,ih]

theorem wordExponent_wordOfExponent (a : Fin n →₀ ℕ) :
    wordExponent (wordOfExponent a) = a := by
  rw [wordExponent_eq_sum]
  simp only [wordOfExponent,List.map_ofFn,List.sum_ofFn]
  ext i
  simp

def wordMonomial : CoordinateWord n → CoordinateSpace n → ℂ
  | [],_ => 1
  | (i,d) :: w,z => z i ^ d * wordMonomial w z

/-- The quotient is genuinely produced by iterating the actual Cauchy operator. -/
def wordQuot (ρ : ℝ) : CoordinateWord n →
    (CoordinateSpace n → ℂ) → CoordinateSpace n → ℂ
  | [],h => h
  | (i,d) :: w,h => wordQuot ρ w (coordinateQuot h i ρ d)

def wordProjection (ρ : ℝ) (w : CoordinateWord n)
    (h : CoordinateSpace n → ℂ) (z : CoordinateSpace n) : ℂ :=
  wordMonomial w z * wordQuot ρ w h z

theorem wordMonomial_differentiable (w : CoordinateWord n) :
    Differentiable ℂ (wordMonomial w) := by
  induction w with
  | nil => exact differentiable_const _
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    exact ((ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable.pow d).mul ih

theorem wordQuot_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (wordQuot ρ w h) (ball 0 R) := by
  induction w generalizing h with
  | nil => exact hh
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    exact ih (coordinateQuot_differentiableOn hρ hρR hh i d)

theorem wordProjection_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (wordProjection ρ w h) (ball 0 R) :=
  (wordMonomial_differentiable w).differentiableOn.mul
    (wordQuot_differentiableOn hρ hρR w hh)

/-- The finite Cauchy composition has a produced constant, independent of h and M. -/
theorem exists_wordQuot_bound {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : CoordinateWord n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (h : CoordinateSpace n → ℂ),
      DifferentiableOn ℂ h (ball 0 R) →
      (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
      ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖wordQuot ρ w h z‖ ≤ C * M := by
  induction w with
  | nil =>
    refine ⟨1,zero_le_one,?_⟩
    intro M h _hh hM z hz
    simpa only [wordQuot,one_mul] using hM z hz
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    obtain ⟨Cw,hCw,hw⟩ := ih
    obtain ⟨Cq,Ct,hCq,_hCt,_hCtEq,hq⟩ := exists_coordinate_division_bounds i d hρ hρR
    refine ⟨Cw * Cq,mul_nonneg hCw hCq,?_⟩
    intro M h hh hM z hz
    have hhq := coordinateQuot_differentiableOn hρ hρR hh i d
    have hMq : ∀ x ∈ ball (0 : CoordinateSpace n) R,
        ‖coordinateQuot h i ρ d x‖ ≤ Cq * M := fun x hx => (hq M h hh hM x hx).1
    simpa only [wordQuot,mul_assoc] using hw (Cq * M) _ hhq hMq z hz

theorem wordMonomial_norm_le (w : CoordinateWord n) {R : ℝ} (hR : 0 < R)
    {z : CoordinateSpace n} (hz : z ∈ ball 0 R) :
    ‖wordMonomial w z‖ ≤ R ^ wordDegree w := by
  induction w with
  | nil => simp only [wordMonomial,wordDegree,norm_one,pow_zero,le_refl]
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    have hzi : ‖z i‖ ≤ R := (norm_le_pi_norm z i).trans (mem_ball_zero_iff.mp hz).le
    simp only [wordMonomial,wordDegree,norm_mul,norm_pow,pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzi d) ih
      (norm_nonneg _) (pow_nonneg hR.le d)

theorem exists_wordProjection_bound {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : CoordinateWord n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (h : CoordinateSpace n → ℂ),
      DifferentiableOn ℂ h (ball 0 R) →
      (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
      ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖wordProjection ρ w h z‖ ≤ C * M := by
  obtain ⟨Cq,hCq,hq⟩ := exists_wordQuot_bound hρ hρR w
  refine ⟨R ^ wordDegree w * Cq,mul_nonneg (pow_nonneg (hρ.trans hρR).le _) hCq,?_⟩
  intro M h hh hM z hz
  change ‖wordMonomial w z * wordQuot ρ w h z‖ ≤ _
  rw [norm_mul,mul_assoc]
  exact mul_le_mul (wordMonomial_norm_le w (hρ.trans hρR) hz) (hq M h hh hM z hz)
    (norm_nonneg _) (pow_nonneg (hρ.trans hρR).le _)

/-- The actual quotient's ENTIRE Taylor series has the literal finite-word shift. -/
theorem coeff_wordQuotGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
        (modelGerm (hρ.trans hρR) (wordQuot_differentiableOn hρ hρR w hh))) =
      MvPowerSeries.coeff (a + wordExponent w)
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) := by
  induction w generalizing h a with
  | nil => simp only [wordQuot,wordExponent,add_zero]
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    change MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
      (modelGerm (hρ.trans hρR) (wordQuot_differentiableOn hρ hρR w
        (coordinateQuot_differentiableOn hρ hρR hh i d)))) = _
    rw [ih (coordinateQuot_differentiableOn hρ hρR hh i d),
      coeff_coordinateQuotGerm hρ hρR hh i d]
    congr 1
    simp only [wordExponent,add_assoc,add_comm (wordExponent w) (Finsupp.single i d)]

private theorem modelGerm_mul {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.mul hg) = modelGerm hR hf * modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z * modelFunction g z) _ = _
  exact HolGerm.mk_mul _ _ _ _

theorem actualTaylor_wordMonomial {R : ℝ} (hR : 0 < R) (w : CoordinateWord n) :
    actualUnshiftedTaylorAlgHom n
        (modelGerm hR (wordMonomial_differentiable w).differentiableOn) =
      MvPowerSeries.monomial (wordExponent w) 1 := by
  induction w with
  | nil =>
    change actualUnshiftedTaylorAlgHom n (HolGerm.mk (1 : ComplexModel n → ℂ) _) = _
    rw [HolGerm.mk_one,map_one]
    exact MvPowerSeries.monomial_zero_one.symm
  | cons p w ih =>
    rcases p with ⟨i,d⟩
    have hz : modelGerm hR
        ((ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable.differentiableOn.pow d) =
        coordinateGerm i ^ d := by
      change HolGerm.mk (fun z : ComplexModel n => z i ^ d) _ =
        (HolGerm.mk (fun z : ComplexModel n => z i) _) ^ d
      exact HolGerm.mk_pow _ _ _
    change actualUnshiftedTaylorAlgHom n (modelGerm hR
      (((ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable.differentiableOn.pow d).mul
        (wordMonomial_differentiable w).differentiableOn)) = _
    rw [modelGerm_mul hR
      ((ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable.differentiableOn.pow d)
      (wordMonomial_differentiable w).differentiableOn,
      hz,map_mul,map_pow,actualUnshiftedTaylor_coordinate,
      MvPowerSeries.X_pow_eq,ih,MvPowerSeries.monomial_mul_monomial,one_mul]
    rfl

/-- Concrete analytic monomial cone projection, with the whole support produced. -/
theorem coeff_wordProjectionGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
        (modelGerm (hρ.trans hρR) (wordProjection_differentiableOn hρ hρR w hh))) =
      if wordExponent w ≤ a then MvPowerSeries.coeff a
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 := by
  change MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
    (modelGerm (hρ.trans hρR)
      ((wordMonomial_differentiable w).differentiableOn.mul
        (wordQuot_differentiableOn hρ hρR w hh)))) = _
  rw [modelGerm_mul (hρ.trans hρR) (wordMonomial_differentiable w).differentiableOn
    (wordQuot_differentiableOn hρ hρR w hh),map_mul,actualTaylor_wordMonomial,
    MvPowerSeries.coeff_monomial_mul]
  split_ifs with ha
  · rw [one_mul,coeff_wordQuotGerm hρ hρR w hh,tsub_add_cancel_of_le ha]
  · rfl

end

end Hironaka.HironakaActualCauchyMonomialDivision
