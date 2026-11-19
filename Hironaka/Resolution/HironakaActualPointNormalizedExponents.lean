import Hironaka.Resolution.HironakaActualFormalMonomialBlowupReflection

/-! Literal normalized exponents, coefficient preservation, and the exact nonzero support image. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointNormalizedExponents
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalMonomialBlowupReflection
variable {n : ℕ}

private theorem exponent_split (e : Fin n) (α : Fin n →₀ ℕ) :
    Finsupp.single e (α e)+α.erase e=α := by
  ext i
  by_cases hi : i=e
  · subst i
    simp
  · simp [hi]

private theorem degree_split (e : Fin n) (α : Fin n →₀ ℕ) :
    normalExponentDegree α=α e+normalExponentDegree (α.erase e) := by
  have h := (congrArg normalExponentDegree (exponent_split e α)).symm
  simpa [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib] using h

private theorem point_weight_eq_degree (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) α=normalExponentDegree α := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]

/-- The true normalized point exponent uses erasure before the nonnegative total-degree difference. -/
def actualPointNormalizedExponent (e : Fin n) (μ : ℕ) (β : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  β.erase e+Finsupp.single e (normalExponentDegree β-μ)

/-- The actual exceptional exponent is the source total degree minus the normalization degree. -/
theorem actualPointNormalizedExponent_exceptional (e : Fin n) (μ : ℕ) (β : Fin n →₀ ℕ) :
    actualPointNormalizedExponent e μ β e=normalExponentDegree β-μ := by
  simp [actualPointNormalizedExponent]

/-- Every actual nonexceptional exponent is unchanged. -/
theorem actualPointNormalizedExponent_other (e : Fin n) (μ : ℕ) (β : Fin n →₀ ℕ)
    (i : Fin n) (hi : i ≠ e) : actualPointNormalizedExponent e μ β i=β i := by
  simp [actualPointNormalizedExponent,hi]

/-- The exact normalized exponent map is injective on its genuine degree-bounded source domain. -/
theorem actualPointNormalizedExponent_injective (e : Fin n) (μ : ℕ) :
    Function.Injective (fun β : {β : Fin n →₀ ℕ // μ ≤ normalExponentDegree β} =>
      actualPointNormalizedExponent e μ β.val) := by
  intro β γ h
  have he := congrArg (fun δ : Fin n →₀ ℕ => δ e) h
  rw [actualPointNormalizedExponent_exceptional,actualPointNormalizedExponent_exceptional] at he
  have hdeg : normalExponentDegree β.val=normalExponentDegree γ.val := by
    have hb := β.property
    have hg := γ.property
    omega
  have herase : β.val.erase e=γ.val.erase e := by
    ext i
    by_cases hi : i=e
    · subst i
      simp
    · have hi' := congrArg (fun δ : Fin n →₀ ℕ => δ i) h
      simpa only [Finsupp.erase_ne hi,actualPointNormalizedExponent_other e μ β.val i hi,
        actualPointNormalizedExponent_other e μ γ.val i hi] using hi'
  have hother := congrArg normalExponentDegree herase
  have hβ := degree_split e β.val
  have hγ := degree_split e γ.val
  have hex : β.val e=γ.val e := by omega
  apply Subtype.ext
  ext i
  by_cases hi : i=e
  · simpa only [hi] using hex
  · have hh := congrArg (fun δ : Fin n →₀ ℕ => δ i) herase
    simpa only [Finsupp.erase_ne hi] using hh

/-- Multiplying by the actual exceptional normalization factor gives the true monomial blowup exponent. -/
theorem actualPointNormalizedExponent_add_exceptional (e : Fin n) (μ : ℕ)
    (β : Fin n →₀ ℕ) (hβ : μ ≤ normalExponentDegree β) :
    Finsupp.single e μ+actualPointNormalizedExponent e μ β=
      actualMonomialBlowupExponent Set.univ e β := by
  ext i
  by_cases hi : i=e
  · subst i
    rw [Finsupp.add_apply,Finsupp.single_eq_same,actualPointNormalizedExponent_exceptional,
      actualMonomialBlowupExponent_exceptional Set.univ e (mem_univ e),point_weight_eq_degree]
    omega
  · simp [actualPointNormalizedExponent,actualMonomialBlowupExponent,hi]

/-- The actual whole zero-chart substitution has coefficient zero off its genuine monomial exponent image. -/
theorem actualFormalBlowup_zero_coefficient_outside_image
    (A : Set (Fin n)) (e : Fin n) (F : MvPowerSeries (Fin n) ℂ) (η : Fin n →₀ ℕ)
    (hη : η ∉ range (actualMonomialBlowupExponent A e)) :
    MvPowerSeries.coeff η (actualFormalBlowup A e (fun _ => 0) F)=0 := by
  rw [actualFormalBlowup,MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalBlowupCoordinates_constant_zero A e (fun _ => 0))) F η]
  apply finsum_eq_zero_of_forall_eq_zero
  intro β
  have hne : η ≠ actualMonomialBlowupExponent A e β := by
    intro h
    exact hη ⟨β,h.symm⟩
  rw [actualFormalBlowup_zero_coordinate_product,MvPowerSeries.coeff_monomial_ne hne,smul_zero]

/-- The true normalized coefficient at its exact image exponent is the unchanged original coefficient. -/
theorem actualNormalizedFormalMember_zero_coefficient (e : Fin n) (μ : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ)
    (β : Fin n →₀ ℕ) (hβ : μ ≤ normalExponentDegree β) :
    MvPowerSeries.coeff (actualPointNormalizedExponent e μ β)
      (actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ F hF)=
        MvPowerSeries.coeff β F := by
  have h := congrArg
    (MvPowerSeries.coeff (Finsupp.single e μ+actualPointNormalizedExponent e μ β))
    (actualNormalizedFormalMember_spec Set.univ e (mem_univ e) (fun _ => 0) μ F hF)
  rw [MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_add_monomial_mul,one_mul,
    actualPointNormalizedExponent_add_exceptional e μ β hβ,
    actualFormalBlowup_zero_coefficient] at h
  exact h

/-- Every nonzero actual normalized coefficient has a UNIQUE true original preimage and coefficient. -/
theorem exists_unique_original_exponent_of_normalized_coefficient_ne_zero
    (e : Fin n) (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) (γ : Fin n →₀ ℕ)
    (hγ : MvPowerSeries.coeff γ
      (actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ F hF) ≠ 0) :
    ∃! β : {β : Fin n →₀ ℕ // μ ≤ normalExponentDegree β},
      actualPointNormalizedExponent e μ β.val=γ ∧
      MvPowerSeries.coeff β.val F=MvPowerSeries.coeff γ
        (actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ F hF) := by
  let η := Finsupp.single e μ+γ
  have hprod := congrArg (MvPowerSeries.coeff η)
    (actualNormalizedFormalMember_spec Set.univ e (mem_univ e) (fun _ => 0) μ F hF)
  change MvPowerSeries.coeff (Finsupp.single e μ+γ)
      ((MvPowerSeries.X e)^μ *
        actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ F hF)=
    MvPowerSeries.coeff η (actualFormalBlowup Set.univ e (fun _ => 0) F) at hprod
  rw [MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_add_monomial_mul,one_mul] at hprod
  have himage : η ∈ range (actualMonomialBlowupExponent Set.univ e) := by
    by_contra hnot
    have hz := actualFormalBlowup_zero_coefficient_outside_image Set.univ e F η hnot
    exact hγ (hprod.trans hz)
  obtain ⟨β,hβ⟩ := himage
  have hdeg : normalExponentDegree β=μ+γ e := by
    have hh := congrArg (fun δ : Fin n →₀ ℕ => δ e) hβ
    rw [actualMonomialBlowupExponent_exceptional Set.univ e (mem_univ e),point_weight_eq_degree] at hh
    simpa only [η,Finsupp.add_apply,Finsupp.single_eq_same] using hh
  have hβdeg : μ ≤ normalExponentDegree β := by omega
  have hnorm : actualPointNormalizedExponent e μ β=γ := by
    have hh := (actualPointNormalizedExponent_add_exceptional e μ β hβdeg).trans hβ
    exact add_left_cancel hh
  refine ⟨⟨β,hβdeg⟩,⟨hnorm,?_⟩,?_⟩
  · simpa only [hnorm] using (actualNormalizedFormalMember_zero_coefficient e μ F hF β hβdeg).symm
  · intro β' hβ'
    apply actualPointNormalizedExponent_injective e μ
    exact hβ'.1.trans hnorm.symm

end
end Hironaka.HironakaActualPointNormalizedExponents
