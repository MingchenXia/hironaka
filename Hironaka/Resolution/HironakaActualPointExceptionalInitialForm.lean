/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration

/-! True centre-power precision becomes whole exceptional precision; point normalization retains the actual homogeneous polynomial. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointExceptionalInitialForm
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
variable {n : ℕ}

/-- Actual whole centre-power precision becomes true exceptional-power precision after normalization. -/
theorem actualNormalizedFormalMember_sub_mem_exceptional_power (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) (d r : ℕ)
    (F G : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d)
    (hG : G ∈ actualFormalCoordinateIdeal n A ^ d)
    (hFG : F-G ∈ actualFormalCoordinateIdeal n A ^ (d+r)) :
    actualNormalizedFormalMember A e he b d F hF-actualNormalizedFormalMember A e he b d G hG ∈
      (Ideal.span {MvPowerSeries.X e} : Ideal (MvPowerSeries (Fin n) ℂ)) ^ r := by
  let H := actualNormalizedFormalMember A e he b (d+r) (F-G) hFG
  have hprod : (MvPowerSeries.X e)^d*
      (actualNormalizedFormalMember A e he b d F hF-actualNormalizedFormalMember A e he b d G hG)=
        (MvPowerSeries.X e)^(d+r)*H := by
    rw [mul_sub,actualNormalizedFormalMember_spec,actualNormalizedFormalMember_spec,← map_sub]
    exact (actualNormalizedFormalMember_spec A e he b (d+r) (F-G) hFG).symm
  have hcancel : actualNormalizedFormalMember A e he b d F hF-
      actualNormalizedFormalMember A e he b d G hG=(MvPowerSeries.X e)^r*H := by
    apply mul_left_cancel₀ (pow_ne_zero d (actualFormalExceptional_ne_zero e))
    rw [← mul_assoc,← pow_add]
    exact hprod
  rw [hcancel,Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem point_weight_eq_degree (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) a=Finsupp.degree a := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,Finsupp.degree_eq_sum]

/-- The actual degree-d component and the entire remainder retain the true point-power memberships. -/
theorem actual_point_homogeneous_component_and_remainder (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ d) :
    MvPowerSeries.homogeneousComponent d F ∈ actualFormalCoordinateIdeal n Set.univ ^ d ∧
      F-MvPowerSeries.homogeneousComponent d F ∈ actualFormalCoordinateIdeal n Set.univ ^ (d+1) := by
  constructor
  · apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ d _).mpr
    intro a ha
    rw [point_weight_eq_degree] at ha
    rw [MvPowerSeries.coeff_homogeneousComponent,if_neg (Nat.ne_of_lt ha)]
  · apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ (d+1) _).mpr
    intro a ha
    rw [point_weight_eq_degree] at ha
    rw [map_sub,MvPowerSeries.coeff_homogeneousComponent]
    split_ifs with hd
    · exact sub_self _
    · have hlt : Finsupp.weight (actualCoordinateWeight Set.univ) a<d := by
        rw [point_weight_eq_degree]
        omega
      rw [(mem_actualFormalCoordinateIdeal_pow_iff Set.univ d F).mp hF a hlt,sub_zero]

/-- The literal actual polynomial retaining the entire degree-d homogeneous component. -/
def actualPointHomogeneousPolynomial (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  MvPowerSeries.truncTotal (d+1) (MvPowerSeries.homogeneousComponent d F)

/-- The genuine polynomial inclusion equals the entire original homogeneous component. -/
theorem actualPointHomogeneousPolynomial_coe (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    (actualPointHomogeneousPolynomial d F : MvPowerSeries (Fin n) ℂ)=MvPowerSeries.homogeneousComponent d F := by
  apply MvPowerSeries.ext
  intro a
  rw [actualPointHomogeneousPolynomial,MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with ha
  · rfl
  · symm
    rw [MvPowerSeries.coeff_homogeneousComponent,if_neg (by omega)]

/-- The WHOLE exceptional restriction of an actual point-normalized member retains precisely the true degree-d polynomial. -/
theorem actual_point_normalized_member_congr_homogeneous_polynomial (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ d) :
    ∃ hP : (actualPointHomogeneousPolynomial d F : MvPowerSeries (Fin n) ℂ) ∈
        actualFormalCoordinateIdeal n Set.univ ^ d,
      actualNormalizedFormalMember Set.univ e (mem_univ e) b d F hF-
        actualNormalizedFormalMember Set.univ e (mem_univ e) b d
          (actualPointHomogeneousPolynomial d F) hP ∈ Ideal.span {MvPowerSeries.X e} := by
  have h := actual_point_homogeneous_component_and_remainder d F hF
  have hP : (actualPointHomogeneousPolynomial d F : MvPowerSeries (Fin n) ℂ) ∈
      actualFormalCoordinateIdeal n Set.univ ^ d := by
    rw [actualPointHomogeneousPolynomial_coe]
    exact h.1
  refine ⟨hP,?_⟩
  have hdiff : F-(actualPointHomogeneousPolynomial d F : MvPowerSeries (Fin n) ℂ) ∈
      actualFormalCoordinateIdeal n Set.univ ^ (d+1) := by
    rw [actualPointHomogeneousPolynomial_coe]
    exact h.2
  simpa only [pow_one] using actualNormalizedFormalMember_sub_mem_exceptional_power
    Set.univ e (mem_univ e) b d 1 F (actualPointHomogeneousPolynomial d F) hF hP hdiff

end
end Hironaka.HironakaActualPointExceptionalInitialForm
