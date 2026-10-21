import TranscendentalNakamaye.Pending.HironakaActualDirectionalNormalJet

/-!
# Whole actual point quotient coefficients and literal source bands

For a prescribed actual source numerator F in its true point power and ANY
genuine quotient e^wH=π_bF, an exact finite recursion identifies every pivot
coefficient of H with the literal dehomogeneous source band P_(w+r)(F).
Actual current point powers supply all lower source-band vanishings, while
an actual homogeneous factor identifies its whole pivot projection with
the literal source band. No family substitution, supplied coefficient dictionary or diagram-inclusion
certificate is input. The power and factor corollaries retain their explicitly
stated actual point-power memberships and factorizations.
These are finite actual dictionaries for a later arbitrary-direction order
converse; no full HS/relative/history closure is inferred.
Blueprint: `hironaka-actual-point-normalized-coefficient-bands-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace TranscendentalNakamaye.Pending.HironakaActualPointNormalizedCoefficientBands
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
  HironakaActualExceptionalFilteredDivision HironakaRelativeNormalMonomialBasis
variable {n : ℕ}
local notation "R" => MvPowerSeries (Fin n) ℂ
local notation "P" => MvPolynomial (Fin n) ℂ
local notation "𝔪" => actualFormalCoordinateIdeal n univ

private theorem dehom_pivot_free (e : Fin n) (b : Fin n → ℂ) (f : P)
    (α : Fin n →₀ ℕ) (hα : α∈(actualPointDehomogenization e b f).support) : α e=0 := by
  apply MvPolynomial.mem_support_notMem_vars_zero hα
  intro he
  change e∈(MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i) f).vars at he
  rw [MvPolynomial.aeval_eq_bind₁] at he
  obtain ⟨i,_hi,hvar⟩ := MvPolynomial.mem_vars_bind₁ _ _ he
  by_cases hie : i=e
  · simp [hie] at hvar
  · have hx : e∈(MvPolynomial.C (b i)+MvPolynomial.X i).vars := by simpa [hie] using hvar
    have heq : e=i := by simpa using MvPolynomial.vars_add_subset (MvPolynomial.C (b i)) (MvPolynomial.X i) hx
    exact hie heq.symm

private theorem dehom_coefficient_zero (e : Fin n) (b : Fin n → ℂ) (f : P)
    (α : Fin n →₀ ℕ) (hα : α e≠0) :
    MvPolynomial.coeff α (actualPointDehomogenization e b f)=0 := by
  by_contra hc
  exact hα (dehom_pivot_free e b f α (MvPolynomial.mem_support_iff.mpr hc))

private theorem normalized_point_split (e : Fin n) (b : Fin n → ℂ) (w : ℕ)
    (F H : R) (hF : F∈𝔪^w) (hH : (MvPowerSeries.X e)^w*H=actualFormalBlowup univ e b F) :
    ∃ Q : R,(MvPowerSeries.X e)^(w+1)*Q=actualFormalBlowup univ e b
      (F-MvPowerSeries.homogeneousComponent w F) ∧
      H=(actualPointDehomogenization e b (actualPointHomogeneousPolynomial w F) : R)+MvPowerSeries.X e*Q := by
  have hR := (actual_point_homogeneous_component_and_remainder w F hF).2
  let Q := actualNormalizedFormalMember univ e (mem_univ e) b (w+1)
    (F-MvPowerSeries.homogeneousComponent w F) hR
  have hQ := actualNormalizedFormalMember_spec univ e (mem_univ e) b (w+1)
    (F-MvPowerSeries.homogeneousComponent w F) hR
  refine ⟨Q,hQ,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero w (actualFormalExceptional_ne_zero e))
  rw [mul_add,←mul_assoc,←pow_succ]
  rw [hH,hQ,←actualFormalBlowup_homogeneous_polynomial e b _ w
    (actualPointHomogeneousPolynomial_isHomogeneous w F),actualPointHomogeneousPolynomial_coe,map_sub]
  ring

private theorem high_source_polynomial_sub_component (d w : ℕ) (hd : w<d) (F : R) :
    actualPointHomogeneousPolynomial d (F-MvPowerSeries.homogeneousComponent w F)=actualPointHomogeneousPolynomial d F := by
  apply (MvPolynomial.coe_injective (Fin n) ℂ)
  rw [actualPointHomogeneousPolynomial_coe,actualPointHomogeneousPolynomial_coe]
  apply MvPowerSeries.ext
  intro α
  simp only [MvPowerSeries.coeff_homogeneousComponent,map_sub]
  split_ifs <;> simp_all

/-- Every pivot coefficient of the SAME genuine point-normalized quotient is
the literal dehomogeneous coefficient of its original homogeneous source band. -/
theorem normalized_point_coefficient_band (e : Fin n) (b : Fin n → ℂ) (w : ℕ)
    (F H : R) (hF : F∈𝔪^w) (hH : (MvPowerSeries.X e)^w*H=actualFormalBlowup univ e b F)
    (r : ℕ) (γ : Fin n →₀ ℕ) (hγ : γ e=0) :
    MvPowerSeries.coeff (γ+Finsupp.single e r) H=
      MvPolynomial.coeff γ (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (w+r) F)) := by
  induction r generalizing w F H with
  | zero =>
    obtain ⟨Q,_hQ,hSplit⟩ := normalized_point_split e b w F H hF hH
    rw [hSplit,map_add,Finsupp.single_zero,add_zero,MvPolynomial.coeff_coe]
    have hz : MvPowerSeries.coeff γ (MvPowerSeries.X e*Q)=0 := by
      rw [MvPowerSeries.X,MvPowerSeries.coeff_monomial_mul,if_neg]
      intro hh
      have hi := hh e
      simp only [Finsupp.single_eq_same,hγ] at hi
      omega
    rw [hz,add_zero,Nat.add_zero]
  | succ r ih =>
    obtain ⟨Q,hQ,hSplit⟩ := normalized_point_split e b w F H hF hH
    rw [hSplit,map_add,MvPolynomial.coeff_coe]
    have hz : MvPolynomial.coeff (γ+Finsupp.single e (r+1))
        (actualPointDehomogenization e b (actualPointHomogeneousPolynomial w F))=0 := by
      apply dehom_coefficient_zero
      simp [hγ]
    have he : γ+Finsupp.single e (r+1)=Finsupp.single e 1+(γ+Finsupp.single e r) := by
      ext i
      by_cases hi : i=e <;> simp [hi]
      omega
    rw [hz,zero_add,he,MvPowerSeries.X,MvPowerSeries.coeff_add_monomial_mul,one_mul]
    have hR := (actual_point_homogeneous_component_and_remainder w F hF).2
    rw [ih (w+1) (F-MvPowerSeries.homogeneousComponent w F) Q hR hQ,
      high_source_polynomial_sub_component ((w+1)+r) w (by omega)]
    congr 3
    omega


private theorem point_weight_degree (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) α=α.degree := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,Finsupp.degree_eq_sum]

/-- Actual current point powers force every lower literal dehomogeneous source
band to vanish, for the SAME actual numerator and quotient. -/
theorem dehom_band_coefficients_zero_of_current_power (e : Fin n) (b : Fin n → ℂ)
    (w : ℕ) (F H : R) (hF : F∈𝔪^w)
    (hH : (MvPowerSeries.X e)^w*H=actualFormalBlowup univ e b F)
    (q r : ℕ) (hHr : H∈𝔪^q) (hrq : r≤q) :
    ∀ γ : Fin n →₀ ℕ,γ.degree<q-r → MvPolynomial.coeff γ
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (w+r) F))=0 := by
  intro γ hγ
  by_cases he : γ e=0
  · rw [←normalized_point_coefficient_band e b w F H hF hH r γ he]
    apply (mem_actualFormalCoordinateIdeal_pow_iff univ q H).mp hHr
    rw [point_weight_degree,map_add,Finsupp.degree_single]
    omega
  · exact dehom_coefficient_zero e b _ γ he

/-- A genuine homogeneous current factor has the WHOLE literal projected
source band; neither a coefficient dictionary nor an order certificate is input. -/
theorem projected_current_factor_eq_source_band (e : Fin n) (b : Fin n → ℂ)
    (w : ℕ) (F H : R) (hF : F∈𝔪^w)
    (hH : (MvPowerSeries.X e)^w*H=actualFormalBlowup univ e b F)
    (q r : ℕ) (hrq : r≤q) (L : R)
    (hFactor : MvPowerSeries.homogeneousComponent q H=(MvPowerSeries.X e)^r*L) :
    pivotZeroProjection e L=(MvPolynomial.homogeneousComponent (q-r)
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (w+r) F)) : R) := by
  apply MvPowerSeries.ext
  intro γ
  rw [pivotZeroProjection_coefficient,MvPolynomial.coeff_coe,MvPolynomial.coeff_homogeneousComponent]
  by_cases he : γ e=0
  · rw [if_pos he]
    have hs := congrArg (MvPowerSeries.coeff (Finsupp.single e r+γ)) hFactor
    rw [MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_add_monomial_mul,one_mul,
      MvPowerSeries.coeff_homogeneousComponent] at hs
    have hd : (Finsupp.single e r+γ).degree=r+γ.degree := by rw [map_add,Finsupp.degree_single]
    rw [hd] at hs
    by_cases hγ : γ.degree=q-r
    · rw [if_pos hγ]
      have ht : r+γ.degree=q := by omega
      rw [if_pos ht] at hs
      rw [←hs,add_comm]
      exact normalized_point_coefficient_band e b w F H hF hH r γ he
    · rw [if_neg hγ]
      have ht : r+γ.degree≠q := by omega
      rw [if_neg ht] at hs
      exact hs.symm
  · rw [if_neg he]
    split_ifs
    · exact (dehom_coefficient_zero e b _ γ he).symm
    · rfl

end
end TranscendentalNakamaye.Pending.HironakaActualPointNormalizedCoefficientBands

