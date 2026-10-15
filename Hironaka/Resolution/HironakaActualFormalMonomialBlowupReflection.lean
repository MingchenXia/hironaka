/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration

/-! True monomial blowup coefficient embedding and reflection of the entire original center-power filtration. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalMonomialBlowupReflection
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
variable {n : ℕ}

/-- The literal exponent map of the genuine zero-direction blowup chart. -/
def actualMonomialBlowupExponent (A : Set (Fin n)) (e : Fin n) :
    (Fin n →₀ ℕ) →+ (Fin n →₀ ℕ) where
  toFun a := a+Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) a)
  map_zero' := by simp
  map_add' a b := by simp only [map_add,Finsupp.single_add]; abel

/-- The true weight outside the exceptional coordinate is unchanged by the actual exponent insertion. -/
theorem actualMonomialBlowupExponent_other_weight (A : Set (Fin n)) (e : Fin n) (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight (A\{e})) (actualMonomialBlowupExponent A e a)=
      Finsupp.weight (actualCoordinateWeight (A\{e})) a := by
  change Finsupp.weight _ (a+Finsupp.single e _)=_
  simp [actualCoordinateWeight,Finsupp.weight_single]

/-- Every original exponent is genuinely recovered from its literal actual chart exponent. -/
theorem actualMonomialBlowupExponent_injective (A : Set (Fin n)) (e : Fin n) :
    Function.Injective (actualMonomialBlowupExponent A e) := by
  intro a b h
  have hw : Finsupp.weight (actualCoordinateWeight (A\{e})) a=
      Finsupp.weight (actualCoordinateWeight (A\{e})) b := by
    rw [← actualMonomialBlowupExponent_other_weight A e a,h,actualMonomialBlowupExponent_other_weight]
  ext i
  have hi := congrArg (fun c : Fin n →₀ ℕ => c i) h
  change a i+(Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) a)) i=
    b i+(Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) b)) i at hi
  rw [hw] at hi
  exact Nat.add_right_cancel hi

/-- The exceptional exponent is exactly the GENUINE selected-center weight of the original exponent. -/
theorem actualMonomialBlowupExponent_exceptional (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (a : Fin n →₀ ℕ) :
    actualMonomialBlowupExponent A e a e=Finsupp.weight (actualCoordinateWeight A) a := by
  change a e+(Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) a)) e=_
  rw [Finsupp.single_eq_same,Finsupp.weight_eq_sum,Finsupp.weight_eq_sum]
  have hs : (∑ i : Fin n, a i*actualCoordinateWeight A i)=
      (∑ i : Fin n, a i*actualCoordinateWeight (A\{e}) i)+a e := by
    calc
      _=∑ i : Fin n, (a i*actualCoordinateWeight (A\{e}) i+(if i=e then a e else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hie : i=e
        · subst i; simp [actualCoordinateWeight,he]
        · by_cases hi : i ∈ A <;> simp [actualCoordinateWeight,hi,hie]
      _=_ := by rw [Finset.sum_add_distrib]; simp
  simpa only [smul_eq_mul,add_comm] using hs.symm

/-- Literal genuine zero-direction coordinates before any formal coefficient reindexing. -/
theorem actualFormalBlowup_zero_coordinates (A : Set (Fin n)) (e : Fin n)
    (i : Fin n) :
    actualFormalBlowupCoordinates A e (fun _ => 0) i=
      MvPowerSeries.X i*(MvPowerSeries.X e)^actualCoordinateWeight (A\{e}) i := by
  by_cases hi : i ∈ A
  · by_cases hie : i=e
    · subst i; simp [actualFormalBlowupCoordinates,actualCoordinateWeight,hi]
    · simp [actualFormalBlowupCoordinates,actualCoordinateWeight,hi,hie,mul_comm]
  · simp [actualFormalBlowupCoordinates,actualCoordinateWeight,hi]

/-- The TRUE finite product of the SAME actual chart coordinates is the literal monomial at the true chart exponent. -/
theorem actualFormalBlowup_zero_coordinate_product (A : Set (Fin n)) (e : Fin n)
    (a : Fin n →₀ ℕ) :
    a.prod (fun i k => actualFormalBlowupCoordinates A e (fun _ => 0) i ^ k)=
      MvPowerSeries.monomial (actualMonomialBlowupExponent A e a) (1 : ℂ) := by
  simp_rw [actualFormalBlowup_zero_coordinates,mul_pow]
  rw [Finsupp.prod_mul,← MvPowerSeries.monomial_one_eq]
  have hp : a.prod (fun i k => ((MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ) ^
      actualCoordinateWeight (A\{e}) i)^k)=
        (MvPowerSeries.X e)^Finsupp.weight (actualCoordinateWeight (A\{e})) a := by
    simp_rw [← pow_mul]
    change (∏ i ∈ a.support, (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ) ^
      (actualCoordinateWeight (A\{e}) i*a i))=_
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finsupp.weight_apply,Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [smul_eq_mul,mul_comm]
  rw [hp,MvPowerSeries.X_pow_eq,MvPowerSeries.monomial_mul_monomial,one_mul]
  rfl

/-- EVERY original coefficient survives at its true blown-up exponent, for the actual genuine substitution. -/
theorem actualFormalBlowup_zero_coefficient (A : Set (Fin n)) (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (actualMonomialBlowupExponent A e a)
      (actualFormalBlowup A e (fun _ => 0) F)=MvPowerSeries.coeff a F := by
  rw [actualFormalBlowup,MvPowerSeries.substAlgHom_apply,MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A e (fun _ => 0))) F _]
  rw [finsum_eq_single _ a]
  · rw [actualFormalBlowup_zero_coordinate_product,MvPowerSeries.coeff_monomial_same]
    simp
  · intro b hb
    rw [actualFormalBlowup_zero_coordinate_product,MvPowerSeries.coeff_monomial,if_neg]
    · simp
    · intro h
      exact hb (actualMonomialBlowupExponent_injective A e h.symm)

/-- Genuine coefficient reflection makes the SAME actual zero-direction formal chart map injective. -/
theorem actualFormalBlowup_zero_injective (A : Set (Fin n)) (e : Fin n) :
    Function.Injective (actualFormalBlowup A e (fun _ => 0)) := by
  intro F G h
  apply MvPowerSeries.ext
  intro a
  rw [← actualFormalBlowup_zero_coefficient A e F a,h,actualFormalBlowup_zero_coefficient]

/-- BOTH whole selected-center power directions are derived from the ACTUAL chart coefficient embedding. -/
theorem mem_coordinate_power_iff_blowup_zero_exceptional_dvd (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F ∈ actualFormalCoordinateIdeal n A ^ d ↔
      (MvPowerSeries.X e)^d ∣ actualFormalBlowup A e (fun _ => 0) F := by
  constructor
  · intro hF
    obtain ⟨G,hG⟩ := actualFormalBlowup_divisible A e he (fun _ => 0) d F hF
    exact ⟨G,hG.symm⟩
  · intro hF
    apply (mem_actualFormalCoordinateIdeal_pow_iff A d F).mpr
    intro a ha
    have hc := MvPowerSeries.X_pow_dvd_iff.mp hF (actualMonomialBlowupExponent A e a)
      (by rwa [actualMonomialBlowupExponent_exceptional A e he])
    rwa [actualFormalBlowup_zero_coefficient] at hc

/-- The genuine inverse image of the WHOLE actual exceptional principal power is exactly the true center power. -/
theorem comap_exceptional_power_blowup_zero (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (d : ℕ) :
    Ideal.comap (actualFormalBlowup A e (fun _ => 0)).toRingHom
      (Ideal.span {(MvPowerSeries.X e)^d})=actualFormalCoordinateIdeal n A ^ d := by
  ext F
  change actualFormalBlowup A e (fun _ => 0) F ∈ Ideal.span {(MvPowerSeries.X e)^d} ↔
    F ∈ actualFormalCoordinateIdeal n A ^ d
  exact Ideal.mem_span_singleton.trans
    (mem_coordinate_power_iff_blowup_zero_exceptional_dvd A e he d F).symm

/-- A genuine nonzero original member has a true nonzero normalized quotient in the actual monomial chart. -/
theorem actualNormalizedFormalMember_zero_direction_ne_zero (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) (hne : F ≠ 0) :
    actualNormalizedFormalMember A e he (fun _ => 0) d F hF ≠ 0 := by
  intro h
  have hs := actualNormalizedFormalMember_spec A e he (fun _ => 0) d F hF
  rw [h,mul_zero] at hs
  apply hne
  apply actualFormalBlowup_zero_injective A e
  simpa using hs.symm

end
end Hironaka.HironakaActualFormalMonomialBlowupReflection
