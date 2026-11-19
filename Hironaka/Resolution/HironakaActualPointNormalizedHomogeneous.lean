import Hironaka.Resolution.HironakaActualPointNormalizedExponents
import Hironaka.Resolution.HironakaActualPointExceptionalFibreRadial

/-! Actual whole normalization fixes the SAME homogeneous head independent of the exceptional variable. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointNormalizedHomogeneous
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualPointNormalizedExponents
  HironakaActualPointExceptionalFibreRadial
variable {n : ℕ}

/-- Zero actual partial differentiation kills every actual positive-coordinate coefficient. -/
theorem coeff_eq_zero_of_pderiv_eq_zero_of_pos (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (hD : MvPowerSeries.pderiv ℂ e F=0)
    (β : Fin n →₀ ℕ) (hβ : 0 < β e) : MvPowerSeries.coeff β F=0 := by
  let c := β-Finsupp.single e 1
  have hs : Finsupp.single e 1 ≤ β := by
    intro i
    by_cases hi : i=e
    · subst i
      simpa only [Finsupp.single_eq_same] using Nat.succ_le_iff.mpr hβ
    · simp only [Finsupp.single_eq_of_ne hi,zero_le]
  have hc : c+Finsupp.single e 1=β := tsub_add_cancel_of_le hs
  have hz := congrArg (MvPowerSeries.coeff c) hD
  rw [MvPowerSeries.coeff_pderiv,hc,map_zero] at hz
  have hnat : (c e : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (c e)
  exact (mul_eq_zero.mp hz).resolve_right hnat

/-- The literal exceptional projection fixes every entire series with zero actual exceptional partial. -/
theorem actualPointExceptionalProjection_eq_self_of_pderiv_eq_zero (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (hD : MvPowerSeries.pderiv ℂ e F=0) :
    actualPointExceptionalProjection e F=F := by
  apply MvPowerSeries.ext
  intro β
  rw [coeff_actualPointExceptionalProjection]
  by_cases hβ : β e=0
  · rw [if_pos hβ]
  · rw [if_neg hβ]
    exact (coeff_eq_zero_of_pderiv_eq_zero_of_pos e F hD β (Nat.pos_of_ne_zero hβ)).symm

/-- Actual normalization fixes the SAME whole transverse homogeneous head. -/
theorem actualNormalizedFormalMember_zero_eq_of_homogeneous_independent
    (e : Fin n) (μ : ℕ) (H : MvPowerSeries (Fin n) ℂ)
    (hH : H.IsHomogeneous μ) (hD : MvPowerSeries.pderiv ℂ e H=0)
    (hpow : H ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ H hpow=H := by
  have hdegree (β : Fin n →₀ ℕ) (hβ : MvPowerSeries.coeff β H ≠ 0) :
      normalExponentDegree β=μ := by
    simpa only [normalExponentDegree,Finsupp.weight_eq_sum,Pi.one_apply,smul_eq_mul,mul_one] using hH hβ
  have hindependent (β : Fin n →₀ ℕ) (hβ : MvPowerSeries.coeff β H ≠ 0) : β e=0 := by
    by_contra hne
    exact hβ (coeff_eq_zero_of_pderiv_eq_zero_of_pos e H hD β (Nat.pos_of_ne_zero hne))
  have hexponent (β : Fin n →₀ ℕ) (hβ : MvPowerSeries.coeff β H ≠ 0) :
      actualPointNormalizedExponent e μ β=β := by
    simp only [actualPointNormalizedExponent,hdegree β hβ,Nat.sub_self,Finsupp.single_zero,add_zero]
    ext i
    by_cases hi : i=e
    · subst i
      simp only [Finsupp.erase_same,hindependent β hβ]
    · simp only [Finsupp.erase_ne hi]
  apply MvPowerSeries.ext
  intro γ
  by_cases hγ : MvPowerSeries.coeff γ
      (actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ H hpow)=0
  · rw [hγ]
    symm
    by_contra hne
    have hcoef := actualNormalizedFormalMember_zero_coefficient e μ H hpow γ
      (le_of_eq (hdegree γ hne).symm)
    rw [hexponent γ hne,hγ] at hcoef
    exact hne hcoef.symm
  · obtain ⟨β,⟨hβγ,hcoeff⟩,_hunique⟩ :=
      exists_unique_original_exponent_of_normalized_coefficient_ne_zero e μ H hpow γ hγ
    have hβ : MvPowerSeries.coeff β.val H ≠ 0 := by rwa [hcoeff]
    have hβeq : β.val=γ := (hexponent β.val hβ).symm.trans hβγ
    simpa only [hβeq] using hcoeff.symm

end
end Hironaka.HironakaActualPointNormalizedHomogeneous
