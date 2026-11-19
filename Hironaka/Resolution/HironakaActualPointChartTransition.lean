import Hironaka.Resolution.HironakaActualPointUnitCoordinateChange
import Hironaka.Resolution.HironakaActualFormalStrictGenerators
import Hironaka.Resolution.HironakaActualOriginalFormalHSTransfer
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Genuine point-chart transition substitutions and SAME-member covariance.
The algebra-map direction is from the f-chart ring into the e-chart ring. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointChartTransition
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualOriginalFormalHSTransfer
  HironakaActualPointUnitCoordinateChange HironakaRelativeNormalMonomialBasis
variable {n : ℕ}

/-- Actual transverse coordinates, with the exceptional coordinate omitted. -/
def actualPointChartTransverse (e i : Fin n) : MvPowerSeries (Fin n) ℂ :=
  if i=e then 0 else MvPowerSeries.X i

/-- The genuine chart-overlap denominator has constant coefficient v_f. -/
def actualPointChartPivotUnit (e f : Fin n) (v : Fin n → ℂ) : MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.C (v f)+actualPointChartTransverse e f

/-- The actual projective direction normalized at the new nonzero pivot. -/
def actualPointChartNormalizedDirection (f : Fin n) (v : Fin n → ℂ) : Fin n → ℂ := fun i => v i/v f

/-- The actual reciprocal point-chart coordinate formulas, before any inverse assumption. -/
def actualPointChartTransitionCoordinates (e f : Fin n) (v : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries (Fin n) ℂ :=
  if i=f then MvPowerSeries.X e*actualPointChartPivotUnit e f v else
    (MvPowerSeries.C (v i)+actualPointChartTransverse e i)*(actualPointChartPivotUnit e f v)⁻¹-
      MvPowerSeries.C (v i/v f)

private theorem transverse_constant (e i : Fin n) :
    MvPowerSeries.constantCoeff (actualPointChartTransverse e i)=0 := by
  by_cases hi : i=e <;> simp [actualPointChartTransverse,hi]

private theorem pivot_constant (e f : Fin n) (v : Fin n → ℂ) :
    MvPowerSeries.constantCoeff (actualPointChartPivotUnit e f v)=v f := by
  simp [actualPointChartPivotUnit,transverse_constant]

private theorem pivot_mul_inv (e f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    actualPointChartPivotUnit e f v*(actualPointChartPivotUnit e f v)⁻¹=1 :=
  MvPowerSeries.mul_inv_cancel _ (by rwa [pivot_constant])

private theorem pivot_inv_mul (e f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    (actualPointChartPivotUnit e f v)⁻¹*actualPointChartPivotUnit e f v=1 := by
  rw [mul_comm,pivot_mul_inv e f v hf]

private theorem pivot_isUnit (e f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    IsUnit (actualPointChartPivotUnit e f v) :=
  IsUnit.of_mul_eq_one _ (pivot_mul_inv e f v hf)

private theorem transition_constant_zero (e f : Fin n) (v : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.constantCoeff (actualPointChartTransitionCoordinates e f v i)=0 := by
  by_cases hi : i=f
  · simp [actualPointChartTransitionCoordinates,hi]
  · simp [actualPointChartTransitionCoordinates,hi,pivot_constant,transverse_constant,
      div_eq_mul_inv]

/-- The actual centred formal substitution is internally supplied by its zero constant coordinates. -/
def actualPointChartTransitionHom (e f : Fin n) (v : Fin n → ℂ) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (transition_constant_zero e f v))

private theorem transition_X (e f : Fin n) (v : Fin n → ℂ) (i : Fin n) :
    actualPointChartTransitionHom e f v (MvPowerSeries.X i)=actualPointChartTransitionCoordinates e f v i :=
  MvPowerSeries.substAlgHom_X _ i

private theorem transition_C (e f : Fin n) (v : Fin n → ℂ) (c : ℂ) :
    actualPointChartTransitionHom e f v (MvPowerSeries.C c)=MvPowerSeries.C c :=
  (actualPointChartTransitionHom e f v).commutes c

private theorem normalized_at_pivot (f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    actualPointChartNormalizedDirection f v f=1 := div_self hf

private theorem normalized_at_old_pivot (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) :
    actualPointChartNormalizedDirection f v e=(v f)⁻¹ := by simp [actualPointChartNormalizedDirection,he,one_div]

private theorem normalized_twice (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    actualPointChartNormalizedDirection e (actualPointChartNormalizedDirection f v)=v := by
  funext i
  dsimp [actualPointChartNormalizedDirection]
  rw [he]
  field_simp [hf]

private theorem transition_base_plus_transverse (e f : Fin n) (v : Fin n → ℂ)
    (hf : v f ≠ 0) (i : Fin n) :
    actualPointChartTransitionHom e f v
      (MvPowerSeries.C (actualPointChartNormalizedDirection f v i)+actualPointChartTransverse f i)=
      (MvPowerSeries.C (v i)+actualPointChartTransverse e i)*(actualPointChartPivotUnit e f v)⁻¹ := by
  by_cases hi : i=f
  · subst i
    rw [normalized_at_pivot f v hf]
    simp only [actualPointChartTransverse,ite_true,add_zero,map_one]
    exact (pivot_mul_inv e f v hf).symm
  · rw [actualPointChartTransverse,if_neg hi,map_add,transition_C,transition_X,
      actualPointChartTransitionCoordinates,if_neg hi]
    dsimp only [actualPointChartNormalizedDirection]
    abel

private theorem transition_inverse_pivot (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) :
    actualPointChartTransitionHom e f v
      (actualPointChartPivotUnit f e (actualPointChartNormalizedDirection f v))=(actualPointChartPivotUnit e f v)⁻¹ := by
  rw [actualPointChartPivotUnit,transition_base_plus_transverse e f v hf e]
  simp [actualPointChartTransverse,he]

private theorem transition_inverse_pivot_inv (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) :
    actualPointChartTransitionHom e f v
      ((actualPointChartPivotUnit f e (actualPointChartNormalizedDirection f v))⁻¹)=actualPointChartPivotUnit e f v := by
  have hwe : actualPointChartNormalizedDirection f v e ≠ 0 := by rw [normalized_at_old_pivot e f v he]; exact inv_ne_zero hf
  have h := congrArg (actualPointChartTransitionHom e f v)
    (pivot_mul_inv f e (actualPointChartNormalizedDirection f v) hwe)
  rw [map_mul,transition_inverse_pivot e f v he hf,map_one] at h
  calc
    _=(actualPointChartPivotUnit e f v*(actualPointChartPivotUnit e f v)⁻¹)*
        actualPointChartTransitionHom e f v ((actualPointChartPivotUnit f e (actualPointChartNormalizedDirection f v))⁻¹) := by
      rw [pivot_mul_inv e f v hf,one_mul]
    _=_ := by rw [mul_assoc,h,mul_one]

private theorem transition_inverse_coordinate (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (i : Fin n) :
    actualPointChartTransitionHom e f v
      (actualPointChartTransitionCoordinates f e (actualPointChartNormalizedDirection f v) i)=MvPowerSeries.X i := by
  by_cases hi : i=e
  · subst i
    rw [actualPointChartTransitionCoordinates,if_pos rfl,map_mul,transition_X,
      actualPointChartTransitionCoordinates,if_pos rfl,transition_inverse_pivot e f v he hf]
    rw [mul_assoc,pivot_mul_inv e f v hf,mul_one]
  · rw [actualPointChartTransitionCoordinates,if_neg hi,map_sub,map_mul,
      transition_base_plus_transverse e f v hf i,transition_inverse_pivot_inv e f v he hf,transition_C]
    have hw : actualPointChartNormalizedDirection f v i/actualPointChartNormalizedDirection f v e=v i := by
      exact congrFun (normalized_twice e f v he hf) i
    rw [hw,mul_assoc,pivot_inv_mul e f v hf,mul_one]
    simp [actualPointChartTransverse,hi]

private theorem transition_inverse_apply (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (F : MvPowerSeries (Fin n) ℂ) :
    actualPointChartTransitionHom e f v
      (actualPointChartTransitionHom f e (actualPointChartNormalizedDirection f v) F)=F := by
  dsimp only [actualPointChartTransitionHom]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply,MvPowerSeries.substAlgHom_apply]
  have hcoord : (fun i => MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (transition_constant_zero e f v)) (actualPointChartTransitionCoordinates f e (actualPointChartNormalizedDirection f v) i))=
      MvPowerSeries.X := by
    funext i
    exact transition_inverse_coordinate e f v he hf i
  rw [hcoord,MvPowerSeries.subst_self]
  rfl

/-- The actual formal chart algebra equivalence is constructed from both genuine inverse substitutions. -/
def actualPointChartTransitionAlgEquiv (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) : MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun := actualPointChartTransitionHom e f v
  invFun := actualPointChartTransitionHom f e (actualPointChartNormalizedDirection f v)
  left_inv F := by
    have hwe : actualPointChartNormalizedDirection f v e ≠ 0 := by rw [normalized_at_old_pivot e f v he]; exact inv_ne_zero hf
    simpa only [normalized_twice e f v he hf] using transition_inverse_apply f e
      (actualPointChartNormalizedDirection f v) (normalized_at_pivot f v hf) hwe F
  right_inv := transition_inverse_apply e f v he hf
  map_mul' := (actualPointChartTransitionHom e f v).map_mul
  map_add' := (actualPointChartTransitionHom e f v).map_add
  commutes' := (actualPointChartTransitionHom e f v).commutes

/-- The equal-pivot boundary acts literally as the identity on every actual formal series. -/
theorem actualPointChartTransition_same_pivot (e : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (F : MvPowerSeries (Fin n) ℂ) : actualPointChartTransitionHom e e v F=F := by
  have hc : actualPointChartTransitionCoordinates e e v=MvPowerSeries.X := by
    funext i
    by_cases hi : i=e <;>
      simp [actualPointChartTransitionCoordinates,actualPointChartPivotUnit,actualPointChartTransverse,he,hi]
  simp only [actualPointChartTransitionHom,hc,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_self]
  rfl

private theorem blowup_coordinate_uniform (e : Fin n) (v : Fin n → ℂ) (he : v e=1) (i : Fin n) :
    actualFormalBlowupCoordinates Set.univ e v i=
      MvPowerSeries.X e*(MvPowerSeries.C (v i)+actualPointChartTransverse e i) := by
  by_cases hi : i=e <;>
    simp [actualFormalBlowupCoordinates,actualPointChartTransverse,hi,he]

private theorem transition_blowup_coordinate (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (i : Fin n) :
    actualPointChartTransitionHom e f v
      (actualFormalBlowupCoordinates Set.univ f (actualPointChartNormalizedDirection f v) i)=
      actualFormalBlowupCoordinates Set.univ e v i := by
  rw [blowup_coordinate_uniform f _ (normalized_at_pivot f v hf),map_mul,transition_X,
    actualPointChartTransitionCoordinates,if_pos rfl,transition_base_plus_transverse e f v hf,
    blowup_coordinate_uniform e v he]
  calc
    _=MvPowerSeries.X e*(MvPowerSeries.C (v i)+actualPointChartTransverse e i)*
        (actualPointChartPivotUnit e f v*(actualPointChartPivotUnit e f v)⁻¹) := by ring
    _=_ := by rw [pivot_mul_inv e f v hf,mul_one]

/-- Every SAME original formal numerator commutes with the genuine point chart transition. -/
theorem actualPointChartTransition_blowup (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (F : MvPowerSeries (Fin n) ℂ) :
    actualPointChartTransitionHom e f v (actualFormalBlowup Set.univ f (actualPointChartNormalizedDirection f v) F)=
      actualFormalBlowup Set.univ e v F := by
  dsimp only [actualPointChartTransitionHom,actualFormalBlowup]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
  have hc : (fun i => MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (transition_constant_zero e f v)) (actualFormalBlowupCoordinates Set.univ f (actualPointChartNormalizedDirection f v) i))=
      actualFormalBlowupCoordinates Set.univ e v := by
    funext i
    exact transition_blowup_coordinate e f v he hf i
  simp only [MvPowerSeries.substAlgHom_apply] at hc ⊢
  exact congrArg (fun coord => MvPowerSeries.subst coord F) hc

/-- SAME original member and SAME normalizing power differ by the displayed actual unit power. -/
theorem actualPointChartTransition_normalized_member (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) :
    actualPointChartPivotUnit e f v ^ μ * actualPointChartTransitionHom e f v
      (actualNormalizedFormalMember Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v) μ F hF)=
      actualNormalizedFormalMember Set.univ e (mem_univ e) v μ F hF := by
  apply actualNormalizedFormalMember_unique
  have h := congrArg (actualPointChartTransitionHom e f v)
    (actualNormalizedFormalMember_spec Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v) μ F hF)
  rw [map_mul,map_pow,transition_X,actualPointChartTransitionCoordinates,if_pos rfl,
    actualPointChartTransition_blowup e f v he hf] at h
  rw [mul_pow] at h
  simpa only [mul_assoc] using h

private theorem transition_variables_le (e f : Fin n) (v : Fin n → ℂ) :
    Ideal.map (actualPointChartTransitionHom e f v).toRingHom (genuineFormalVariables n) ≤
      genuineFormalVariables n := by
  rw [genuineFormalVariables,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G,⟨i,rfl⟩,rfl⟩
  change actualPointChartTransitionHom e f v (MvPowerSeries.X i) ∈ genuineFormalVariables n
  rw [transition_X]
  have h : actualPointChartTransitionCoordinates e f v i ∈ genuineFormalVariables n ^ 1 := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n 1 _).mpr
    intro α hα
    have hd : α.degree=0 := by
      have hd' : α.degree < 1 := by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα
      omega
    have hz : α=0 := (Finsupp.degree_eq_zero_iff α).mp hd
    subst α
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,transition_constant_zero]
  simpa only [pow_one] using h

private theorem transition_comp_inverse_ringHom (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) :
    (actualPointChartTransitionHom e f v).toRingHom.comp
      (actualPointChartTransitionHom f e (actualPointChartNormalizedDirection f v)).toRingHom=
        RingHom.id (MvPowerSeries (Fin n) ℂ) := by
  apply RingHom.ext
  intro F
  exact transition_inverse_apply e f v he hf F

/-- The actual chart equivalence preserves the entire genuine variable ideal. -/
theorem map_genuineFormalVariables_point_chart_transition (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualPointChartTransitionHom e f v).toRingHom (genuineFormalVariables n)=
      genuineFormalVariables n := by
  apply le_antisymm (transition_variables_le e f v)
  have h := Ideal.map_mono (f := (actualPointChartTransitionHom e f v).toRingHom)
    (transition_variables_le f e (actualPointChartNormalizedDirection f v))
  rw [Ideal.map_map,transition_comp_inverse_ringHom e f v he hf,Ideal.map_id] at h
  exact h

/-- Every actual total-order lower bound is reflected by the SAME chart map. -/
theorem mem_genuineFormalVariables_power_iff_point_chart_transition
    (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    actualPointChartTransitionHom e f v F ∈ genuineFormalVariables n ^ q ↔
      F ∈ genuineFormalVariables n ^ q := by
  have hmap : Ideal.map (actualPointChartTransitionHom e f v).toRingHom (genuineFormalVariables n ^ q)=
      genuineFormalVariables n ^ q := by
    rw [Ideal.map_pow,map_genuineFormalVariables_point_chart_transition e f v he hf]
  constructor
  · intro hF
    rw [← hmap] at hF
    obtain ⟨G,hG,hEq⟩ := (Ideal.mem_map_iff_of_surjective _
      (actualPointChartTransitionAlgEquiv e f v he hf).surjective).mp hF
    have heq : G=F := (actualPointChartTransitionAlgEquiv e f v he hf).injective hEq
    rwa [heq] at hG
  · intro hF
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hF

private theorem map_strict_transition_le (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualPointChartTransitionHom e f v).toRingHom
      (actualFormalStrictTransform K Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v)) ≤
        actualFormalStrictTransform K Set.univ e (mem_univ e) v := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal K Set.univ f (mem_univ f)
    (actualPointChartNormalizedDirection f v),actualNormalizedOriginalMemberIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro G ⟨H,⟨μ,F,hFK,hF,rfl⟩,rfl⟩
  apply (Ideal.unit_mul_mem_iff_mem _ ((pivot_isUnit e f v hf).pow μ)).mp
  change actualPointChartPivotUnit e f v ^ μ * actualPointChartTransitionHom e f v
    (actualNormalizedFormalMember Set.univ f (mem_univ f)
      (actualPointChartNormalizedDirection f v) μ F hF) ∈
    actualFormalStrictTransform K Set.univ e (mem_univ e) v
  rw [actualPointChartTransition_normalized_member e f v he hf]
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  exact Ideal.subset_span ⟨μ,F,hFK,hF,rfl⟩

/-- BOTH entire strict-ideal directions preserve the SAME original ideal and all its normalized members. -/
theorem map_actual_point_strict_chart_transition (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualPointChartTransitionHom e f v).toRingHom
      (actualFormalStrictTransform K Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v))=
        actualFormalStrictTransform K Set.univ e (mem_univ e) v := by
  apply le_antisymm (map_strict_transition_le K e f v he hf)
  have hwe : actualPointChartNormalizedDirection f v e ≠ 0 := by rw [normalized_at_old_pivot e f v he]; exact inv_ne_zero hf
  have hrev := map_strict_transition_le K f e (actualPointChartNormalizedDirection f v)
    (normalized_at_pivot f v hf) hwe
  rw [normalized_twice e f v he hf] at hrev
  have h := Ideal.map_mono (f := (actualPointChartTransitionHom e f v).toRingHom) hrev
  rw [Ideal.map_map,transition_comp_inverse_ringHom e f v he hf,Ideal.map_id] at h
  exact h

/-- Actual whole-jet quotient equivalences preserve every genuine strict HS value. -/
theorem genuineFormalHilbertSamuelValue_map_formalAlgEquiv
    (E : MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
    (hE : Ideal.map E.toRingEquiv.toRingHom (genuineFormalVariables n)=genuineFormalVariables n)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n I ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.map E.toRingEquiv.toRingHom I) ℓ := by
  have ht : Ideal.map E.toRingEquiv.toRingHom I ⊔ genuineFormalVariables n ^ (ℓ+1)=
      Ideal.map E.toRingEquiv.toRingHom (I ⊔ genuineFormalVariables n ^ (ℓ+1)) := by
    rw [Ideal.map_sup,Ideal.map_pow,hE]
  exact (Ideal.quotientEquivAlg _ _ E ht).toLinearEquiv.finrank_eq

/-- Actual whole-jet quotient equivalences preserve every genuine strict HS value. -/
theorem genuineFormalHilbertSamuelValue_point_chart_transition
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v)) ℓ=
        genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K Set.univ e (mem_univ e) v) ℓ := by
  let E := actualPointChartTransitionAlgEquiv e f v he hf
  have hmap : (actualFormalStrictTransform K Set.univ e (mem_univ e) v) ⊔ genuineFormalVariables n ^ (ℓ+1)=
      Ideal.map E.toRingEquiv.toRingHom
        ((actualFormalStrictTransform K Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v)) ⊔
          genuineFormalVariables n ^ (ℓ+1)) := by
    change _=Ideal.map (actualPointChartTransitionHom e f v).toRingHom _
    rw [Ideal.map_sup,Ideal.map_pow,map_actual_point_strict_chart_transition K e f v he hf,
      map_genuineFormalVariables_point_chart_transition e f v he hf]
  exact (Ideal.quotientEquivAlg _ _ E hmap).toLinearEquiv.finrank_eq

/-- Every total-order lower bound for these literal normalized members transfers both ways. -/
theorem normalized_member_mem_power_iff_chart_transition (e f : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (hf : v f ≠ 0) (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) (q : ℕ) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) v μ F hF ∈ genuineFormalVariables n ^ q ↔
      actualNormalizedFormalMember Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v) μ F hF ∈
        genuineFormalVariables n ^ q := by
  have hunit := Ideal.unit_mul_mem_iff_mem (genuineFormalVariables n ^ q)
    (x := actualPointChartTransitionHom e f v
      (actualNormalizedFormalMember Set.univ f (mem_univ f) (actualPointChartNormalizedDirection f v) μ F hF))
    ((pivot_isUnit e f v hf).pow μ)
  rw [actualPointChartTransition_normalized_member e f v he hf] at hunit
  exact hunit.trans (mem_genuineFormalVariables_power_iff_point_chart_transition e f v he hf q _)

private theorem actual_base_exceptional (e : Fin n) (b : Fin n → ℂ) :
    actualPointUnitBasePoint e b e=1 := by simp [actualPointUnitBasePoint_apply]

/-- The actual e,b point-chart transition; its only overlap premise is the literal v_f≠0. -/
def actualPointOriginalChartTransition (e : Fin n) (b : Fin n → ℂ) (f : Fin n)
    (hf : actualPointUnitBasePoint e b f ≠ 0) :
    MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  actualPointChartTransitionAlgEquiv e f (actualPointUnitBasePoint e b)
    (actual_base_exceptional e b) hf

private theorem actual_base_blowup_eq (e : Fin n) (b : Fin n → ℂ) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalBlowup Set.univ e (actualPointUnitBasePoint e b) F=actualFormalBlowup Set.univ e b F := by
  have hc : actualFormalBlowupCoordinates Set.univ e (actualPointUnitBasePoint e b)=
      actualFormalBlowupCoordinates Set.univ e b := by
    funext i
    by_cases hi : i=e <;> simp [actualFormalBlowupCoordinates,actualPointUnitBasePoint_apply,hi]
  simp only [actualFormalBlowup,hc]

private theorem actual_base_normalized_eq (e : Fin n) (b : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) (actualPointUnitBasePoint e b) μ F hF=
      actualNormalizedFormalMember Set.univ e (mem_univ e) b μ F hF := by
  apply actualNormalizedFormalMember_unique
  rw [← actual_base_blowup_eq e b F]
  exact actualNormalizedFormalMember_spec Set.univ e (mem_univ e) (actualPointUnitBasePoint e b) μ F hF

private theorem actual_base_strict_eq (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (b : Fin n → ℂ) :
    actualFormalStrictTransform K Set.univ e (mem_univ e) (actualPointUnitBasePoint e b)=
      actualFormalStrictTransform K Set.univ e (mem_univ e) b := by
  unfold actualFormalStrictTransform
  apply congrArg Ideal.span
  ext G
  constructor
  · rintro ⟨F,hFK,hne,rfl⟩
    exact ⟨F,hFK,hne,actual_base_normalized_eq e b _ F _⟩
  · rintro ⟨F,hFK,hne,rfl⟩
    exact ⟨F,hFK,hne,(actual_base_normalized_eq e b _ F _).symm⟩

/-- The whole actual strict ideal is transported between the literal original charts. -/
theorem map_actual_point_original_strict_chart_transition
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (f : Fin n) (hf : actualPointUnitBasePoint e b f ≠ 0) :
    Ideal.map (actualPointOriginalChartTransition e b f hf).toRingEquiv.toRingHom
      (actualFormalStrictTransform K Set.univ f (mem_univ f)
        (fun i => actualPointUnitBasePoint e b i/actualPointUnitBasePoint e b f))=
      actualFormalStrictTransform K Set.univ e (mem_univ e) b := by
  rw [← actual_base_strict_eq K e b]
  exact map_actual_point_strict_chart_transition K e f (actualPointUnitBasePoint e b)
    (actual_base_exceptional e b) hf

/-- Every genuine original strict HS order agrees in the two actual overlapping charts. -/
theorem genuineFormalHilbertSamuelValue_original_point_chart_transition
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (f : Fin n) (hf : actualPointUnitBasePoint e b f ≠ 0) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K Set.univ f (mem_univ f)
        (fun i => actualPointUnitBasePoint e b i/actualPointUnitBasePoint e b f)) ℓ=
      genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ := by
  rw [← actual_base_strict_eq K e b]
  exact genuineFormalHilbertSamuelValue_point_chart_transition K e f (actualPointUnitBasePoint e b)
    (actual_base_exceptional e b) hf ℓ

/-- Literal original e,b normalization, with the SAME F and its actual unit factor. -/
theorem actualPointOriginalChartTransition_normalized_member
    (e : Fin n) (b : Fin n → ℂ) (f : Fin n) (hf : actualPointUnitBasePoint e b f ≠ 0)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) :
    actualPointChartPivotUnit e f (actualPointUnitBasePoint e b)^μ * actualPointOriginalChartTransition e b f hf
      (actualNormalizedFormalMember Set.univ f (mem_univ f)
        (fun i => actualPointUnitBasePoint e b i/actualPointUnitBasePoint e b f) μ F hF)=
      actualNormalizedFormalMember Set.univ e (mem_univ e) b μ F hF := by
  rw [← actual_base_normalized_eq e b μ F hF]
  exact actualPointChartTransition_normalized_member e f (actualPointUnitBasePoint e b)
    (actual_base_exceptional e b) hf μ F hF

/-- The same genuine total-order bound transfers directly between the literal original parameters. -/
theorem actualPointOriginalChartTransition_normalized_mem_power_iff
    (e : Fin n) (b : Fin n → ℂ) (f : Fin n) (hf : actualPointUnitBasePoint e b f ≠ 0)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) (q : ℕ) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) b μ F hF ∈ genuineFormalVariables n ^ q ↔
      actualNormalizedFormalMember Set.univ f (mem_univ f)
        (fun i => actualPointUnitBasePoint e b i/actualPointUnitBasePoint e b f) μ F hF ∈
          genuineFormalVariables n ^ q := by
  rw [← actual_base_normalized_eq e b μ F hF]
  exact normalized_member_mem_power_iff_chart_transition e f (actualPointUnitBasePoint e b)
    (actual_base_exceptional e b) hf μ F hF q

end
end Hironaka.HironakaActualPointChartTransition
