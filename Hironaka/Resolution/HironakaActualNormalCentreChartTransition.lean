import Hironaka.Resolution.HironakaActualPointChartTransition

/-! Actual normal-centre chart transitions fix EVERY tangent variable.
The algebra-map direction is from the f-chart ring into the e-chart ring. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalCentreChartTransition
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualOriginalFormalHSTransfer
  HironakaRelativeNormalMonomialBasis
variable {n : ℕ}

/-- Actual chart transverse coordinates omit only the selected exceptional variable. -/
def actualNormalChartTransverse (e i : Fin n) : MvPowerSeries (Fin n) ℂ :=
  if i=e then 0 else MvPowerSeries.X i

/-- The actual overlap denominator has nonzero constant coefficient v_f on the overlap. -/
def actualNormalChartPivotUnit (e f : Fin n) (v : Fin n → ℂ) : MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.C (v f)+actualNormalChartTransverse e f

/-- The same original normal direction normalized at the new nonzero pivot. -/
def actualNormalChartNormalizedDirection (f : Fin n) (v : Fin n → ℂ) : Fin n → ℂ :=
  fun i => v i/v f

/-- Normal coordinates undergo the real reciprocal transition; EVERY tangent variable remains X_i. -/
def actualNormalChartTransitionCoordinates (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (i : Fin n) : MvPowerSeries (Fin n) ℂ :=
  if i ∈ A then
    if i=f then MvPowerSeries.X e*actualNormalChartPivotUnit e f v else
      (MvPowerSeries.C (v i)+actualNormalChartTransverse e i)*(actualNormalChartPivotUnit e f v)⁻¹-
        MvPowerSeries.C (v i/v f)
  else MvPowerSeries.X i

private theorem transverse_constant (e i : Fin n) :
    MvPowerSeries.constantCoeff (actualNormalChartTransverse e i)=0 := by
  by_cases hi : i=e <;> simp [actualNormalChartTransverse,hi]

private theorem pivot_constant (e f : Fin n) (v : Fin n → ℂ) :
    MvPowerSeries.constantCoeff (actualNormalChartPivotUnit e f v)=v f := by
  simp [actualNormalChartPivotUnit,transverse_constant]

private theorem pivot_mul_inv (e f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    actualNormalChartPivotUnit e f v*(actualNormalChartPivotUnit e f v)⁻¹=1 :=
  MvPowerSeries.mul_inv_cancel _ (by rwa [pivot_constant])

private theorem pivot_inv_mul (e f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    (actualNormalChartPivotUnit e f v)⁻¹*actualNormalChartPivotUnit e f v=1 := by
  rw [mul_comm,pivot_mul_inv e f v hf]

private theorem pivot_isUnit (e f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    IsUnit (actualNormalChartPivotUnit e f v) :=
  IsUnit.of_mul_eq_one _ (pivot_mul_inv e f v hf)

private theorem transition_constant_zero (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.constantCoeff (actualNormalChartTransitionCoordinates A e f v i)=0 := by
  by_cases hiA : i ∈ A
  · by_cases hi : i=f
    · subst i
      simp [actualNormalChartTransitionCoordinates,hiA]
    · simp [actualNormalChartTransitionCoordinates,hiA,hi,pivot_constant,transverse_constant,
        div_eq_mul_inv]
  · simp [actualNormalChartTransitionCoordinates,hiA]

/-- The actual zero-constant coordinate functions construct the genuine entire formal algebra map. -/
def actualNormalChartTransitionHom (A : Set (Fin n)) (e f : Fin n) (v : Fin n → ℂ) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (transition_constant_zero A e f v))

/-- The actual variable rule, including both normal and tangent cases. -/
theorem actualNormalChartTransition_X (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (i : Fin n) :
    actualNormalChartTransitionHom A e f v (MvPowerSeries.X i)=
      actualNormalChartTransitionCoordinates A e f v i :=
  MvPowerSeries.substAlgHom_X _ i

/-- Unlike the point transition, this actual transition fixes each tangent variable individually. -/
theorem actualNormalChartTransition_tangent (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (i : Fin n) (hi : i ∉ A) :
    actualNormalChartTransitionHom A e f v (MvPowerSeries.X i)=MvPowerSeries.X i := by
  rw [actualNormalChartTransition_X,actualNormalChartTransitionCoordinates,if_neg hi]

private theorem transition_C (A : Set (Fin n)) (e f : Fin n) (v : Fin n → ℂ) (c : ℂ) :
    actualNormalChartTransitionHom A e f v (MvPowerSeries.C c)=MvPowerSeries.C c :=
  (actualNormalChartTransitionHom A e f v).commutes c

private theorem normalized_at_pivot (f : Fin n) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    actualNormalChartNormalizedDirection f v f=1 := div_self hf

private theorem normalized_at_old_pivot (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) :
    actualNormalChartNormalizedDirection f v e=(v f)⁻¹ := by
  simp [actualNormalChartNormalizedDirection,he,one_div]

private theorem normalized_twice (e f : Fin n) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    actualNormalChartNormalizedDirection e (actualNormalChartNormalizedDirection f v)=v := by
  funext i
  dsimp [actualNormalChartNormalizedDirection]
  rw [he]
  field_simp [hf]

private theorem transition_base_plus_transverse (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (hf : v f ≠ 0) (i : Fin n) (hiA : i ∈ A) :
    actualNormalChartTransitionHom A e f v
      (MvPowerSeries.C (actualNormalChartNormalizedDirection f v i)+actualNormalChartTransverse f i)=
      (MvPowerSeries.C (v i)+actualNormalChartTransverse e i)*(actualNormalChartPivotUnit e f v)⁻¹ := by
  by_cases hi : i=f
  · subst i
    rw [normalized_at_pivot f v hf]
    simp only [actualNormalChartTransverse,ite_true,add_zero,map_one]
    exact (pivot_mul_inv e f v hf).symm
  · rw [actualNormalChartTransverse,if_neg hi,map_add,transition_C,actualNormalChartTransition_X,
      actualNormalChartTransitionCoordinates,if_pos hiA,if_neg hi]
    dsimp only [actualNormalChartNormalizedDirection]
    abel

private theorem transition_inverse_pivot (A : Set (Fin n)) (e f : Fin n) (heA : e ∈ A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    actualNormalChartTransitionHom A e f v
      (actualNormalChartPivotUnit f e (actualNormalChartNormalizedDirection f v))=
        (actualNormalChartPivotUnit e f v)⁻¹ := by
  rw [actualNormalChartPivotUnit,transition_base_plus_transverse A e f v hf e heA]
  simp [actualNormalChartTransverse,he]

private theorem transition_inverse_pivot_inv (A : Set (Fin n)) (e f : Fin n) (heA : e ∈ A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    actualNormalChartTransitionHom A e f v
      ((actualNormalChartPivotUnit f e (actualNormalChartNormalizedDirection f v))⁻¹)=
        actualNormalChartPivotUnit e f v := by
  have hwe : actualNormalChartNormalizedDirection f v e ≠ 0 := by
    rw [normalized_at_old_pivot e f v he]
    exact inv_ne_zero hf
  have h := congrArg (actualNormalChartTransitionHom A e f v)
    (pivot_mul_inv f e (actualNormalChartNormalizedDirection f v) hwe)
  rw [map_mul,transition_inverse_pivot A e f heA v he hf,map_one] at h
  calc
    _=(actualNormalChartPivotUnit e f v*(actualNormalChartPivotUnit e f v)⁻¹)*
        actualNormalChartTransitionHom A e f v
          ((actualNormalChartPivotUnit f e (actualNormalChartNormalizedDirection f v))⁻¹) := by
      rw [pivot_mul_inv e f v hf,one_mul]
    _=_ := by rw [mul_assoc,h,mul_one]

private theorem transition_inverse_coordinate (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) (i : Fin n) :
    actualNormalChartTransitionHom A e f v
      (actualNormalChartTransitionCoordinates A f e (actualNormalChartNormalizedDirection f v) i)=
        MvPowerSeries.X i := by
  by_cases hiA : i ∈ A
  · rw [actualNormalChartTransitionCoordinates,if_pos hiA]
    by_cases hi : i=e
    · subst i
      rw [if_pos rfl,map_mul,actualNormalChartTransition_X,
        actualNormalChartTransitionCoordinates,if_pos hfA,if_pos rfl,
        transition_inverse_pivot A e f heA v he hf]
      rw [mul_assoc,pivot_mul_inv e f v hf,mul_one]
    · rw [if_neg hi,map_sub,map_mul,
        transition_base_plus_transverse A e f v hf i hiA,
        transition_inverse_pivot_inv A e f heA v he hf,transition_C]
      have hw : actualNormalChartNormalizedDirection f v i/actualNormalChartNormalizedDirection f v e=v i :=
        congrFun (normalized_twice e f v he hf) i
      rw [hw,mul_assoc,pivot_inv_mul e f v hf,mul_one]
      simp [actualNormalChartTransverse,hi]
  · rw [actualNormalChartTransitionCoordinates,if_neg hiA,
      actualNormalChartTransition_tangent A e f v i hiA]

private theorem transition_inverse_apply (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualNormalChartTransitionHom A e f v
      (actualNormalChartTransitionHom A f e (actualNormalChartNormalizedDirection f v) F)=F := by
  dsimp only [actualNormalChartTransitionHom]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply,MvPowerSeries.substAlgHom_apply]
  have hcoord : (fun i => MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (transition_constant_zero A e f v))
        (actualNormalChartTransitionCoordinates A f e (actualNormalChartNormalizedDirection f v) i))=
      MvPowerSeries.X := by
    funext i
    exact transition_inverse_coordinate A e f heA hfA v he hf i
  rw [hcoord,MvPowerSeries.subst_self]
  rfl

/-- The actual inverse NORMAL-centre substitutions construct a genuine entire formal algebra equivalence. -/
def actualNormalChartTransitionAlgEquiv (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun := actualNormalChartTransitionHom A e f v
  invFun := actualNormalChartTransitionHom A f e (actualNormalChartNormalizedDirection f v)
  left_inv F := by
    have hwe : actualNormalChartNormalizedDirection f v e ≠ 0 := by
      rw [normalized_at_old_pivot e f v he]
      exact inv_ne_zero hf
    simpa only [normalized_twice e f v he hf] using transition_inverse_apply A f e hfA heA
      (actualNormalChartNormalizedDirection f v) (normalized_at_pivot f v hf) hwe F
  right_inv := transition_inverse_apply A e f heA hfA v he hf
  map_mul' := (actualNormalChartTransitionHom A e f v).map_mul
  map_add' := (actualNormalChartTransitionHom A e f v).map_add
  commutes' := (actualNormalChartTransitionHom A e f v).commutes

/-- Equal pivots give the literal identity, including all unchanged tangent variables. -/
theorem actualNormalChartTransition_same_pivot (A : Set (Fin n)) (e : Fin n) (v : Fin n → ℂ)
    (he : v e=1) (F : MvPowerSeries (Fin n) ℂ) : actualNormalChartTransitionHom A e e v F=F := by
  have hc : actualNormalChartTransitionCoordinates A e e v=MvPowerSeries.X := by
    funext i
    by_cases hiA : i ∈ A
    · by_cases hi : i=e <;>
        simp [actualNormalChartTransitionCoordinates,actualNormalChartPivotUnit,
          actualNormalChartTransverse,he,hiA,hi]
    · simp [actualNormalChartTransitionCoordinates,hiA]
  simp only [actualNormalChartTransitionHom,hc,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_self]
  rfl

private theorem blowup_coordinate_normal (A : Set (Fin n)) (e : Fin n)
    (v : Fin n → ℂ) (he : v e=1) (i : Fin n) (hiA : i ∈ A) :
    actualFormalBlowupCoordinates A e v i=
      MvPowerSeries.X e*(MvPowerSeries.C (v i)+actualNormalChartTransverse e i) := by
  by_cases hi : i=e <;>
    simp [actualFormalBlowupCoordinates,actualNormalChartTransverse,hiA,hi,he]

private theorem transition_blowup_coordinate (A : Set (Fin n)) (e f : Fin n)
    (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) (i : Fin n) :
    actualNormalChartTransitionHom A e f v
      (actualFormalBlowupCoordinates A f (actualNormalChartNormalizedDirection f v) i)=
        actualFormalBlowupCoordinates A e v i := by
  by_cases hiA : i ∈ A
  · rw [blowup_coordinate_normal A f _ (normalized_at_pivot f v hf) i hiA,map_mul,
      actualNormalChartTransition_X,actualNormalChartTransitionCoordinates,if_pos hfA,if_pos rfl,
      transition_base_plus_transverse A e f v hf i hiA,blowup_coordinate_normal A e v he i hiA]
    calc
      _=MvPowerSeries.X e*(MvPowerSeries.C (v i)+actualNormalChartTransverse e i)*
          (actualNormalChartPivotUnit e f v*(actualNormalChartPivotUnit e f v)⁻¹) := by ring
      _=_ := by rw [pivot_mul_inv e f v hf,mul_one]
  · rw [actualFormalBlowupCoordinates,if_neg hiA,
      actualNormalChartTransition_tangent A e f v i hiA,actualFormalBlowupCoordinates,if_neg hiA]

/-- The SAME arbitrary original entire formal numerator commutes with the real general-centre chart map. -/
theorem actualNormalChartTransition_blowup (A : Set (Fin n)) (e f : Fin n)
    (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualNormalChartTransitionHom A e f v
      (actualFormalBlowup A f (actualNormalChartNormalizedDirection f v) F)=
        actualFormalBlowup A e v F := by
  dsimp only [actualNormalChartTransitionHom,actualFormalBlowup]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
  have hc : (fun i => MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (transition_constant_zero A e f v))
        (actualFormalBlowupCoordinates A f (actualNormalChartNormalizedDirection f v) i))=
      actualFormalBlowupCoordinates A e v := by
    funext i
    exact transition_blowup_coordinate A e f hfA v he hf i
  simp only [MvPowerSeries.substAlgHom_apply] at hc ⊢
  exact congrArg (fun coord => MvPowerSeries.subst coord F) hc

/-- The SAME original member and centre exponent have exactly the true overlap unit-power covariance. -/
theorem actualNormalChartTransition_normalized_member (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualNormalChartPivotUnit e f v ^ μ * actualNormalChartTransitionHom A e f v
      (actualNormalizedFormalMember A f hfA (actualNormalChartNormalizedDirection f v) μ F hF)=
      actualNormalizedFormalMember A e heA v μ F hF := by
  apply actualNormalizedFormalMember_unique
  have h := congrArg (actualNormalChartTransitionHom A e f v)
    (actualNormalizedFormalMember_spec A f hfA (actualNormalChartNormalizedDirection f v) μ F hF)
  rw [map_mul,map_pow,actualNormalChartTransition_X,actualNormalChartTransitionCoordinates,
    if_pos hfA,if_pos rfl,actualNormalChartTransition_blowup A e f hfA v he hf] at h
  rw [mul_pow] at h
  simpa only [mul_assoc] using h

private theorem normal_coordinate_fraction (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (hf : v f ≠ 0) (i : Fin n) (hiA : i ∈ A) (hif : i ≠ f) :
    actualNormalChartTransitionCoordinates A e f v i=
      (actualNormalChartTransverse e i-MvPowerSeries.C (v i/v f)*actualNormalChartTransverse e f)*
        (actualNormalChartPivotUnit e f v)⁻¹ := by
  rw [actualNormalChartTransitionCoordinates,if_pos hiA,if_neg hif]
  have hc : (MvPowerSeries.C (v i/v f) : MvPowerSeries (Fin n) ℂ)*MvPowerSeries.C (v f)=
      MvPowerSeries.C (v i) := by
    rw [← map_mul,div_mul_cancel₀ _ hf]
  calc
    _=((MvPowerSeries.C (v i)+actualNormalChartTransverse e i)-
        MvPowerSeries.C (v i/v f)*actualNormalChartPivotUnit e f v)*
          (actualNormalChartPivotUnit e f v)⁻¹ := by
      rw [sub_mul,mul_assoc,pivot_mul_inv e f v hf,mul_one]
    _=_ := by
      rw [actualNormalChartPivotUnit,mul_add,hc]
      congr 1
      abel

private theorem transverse_mem_centre (A : Set (Fin n)) (e i : Fin n) (hiA : i ∈ A) :
    actualNormalChartTransverse e i ∈ actualFormalCoordinateIdeal n A := by
  by_cases hi : i=e
  · rw [actualNormalChartTransverse,if_pos hi]
    exact Ideal.zero_mem _
  · rw [actualNormalChartTransverse,if_neg hi]
    exact Ideal.subset_span ⟨i,hiA,rfl⟩

private theorem transition_centre_le (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (hf : v f ≠ 0) :
    Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom (actualFormalCoordinateIdeal n A) ≤
      actualFormalCoordinateIdeal n A := by
  rw [actualFormalCoordinateIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G,⟨i,hiA,rfl⟩,rfl⟩
  change actualNormalChartTransitionHom A e f v (MvPowerSeries.X i) ∈ actualFormalCoordinateIdeal n A
  rw [actualNormalChartTransition_X]
  by_cases hif : i=f
  · rw [actualNormalChartTransitionCoordinates,if_pos hiA,if_pos hif]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e,heA,rfl⟩)
  · rw [normal_coordinate_fraction A e f v hf i hiA hif]
    exact Ideal.mul_mem_right _ _ ((actualFormalCoordinateIdeal n A).sub_mem
      (transverse_mem_centre A e i hiA)
      (Ideal.mul_mem_left _ _ (transverse_mem_centre A e f hfA)))

private theorem transition_variables_le (A : Set (Fin n)) (e f : Fin n) (v : Fin n → ℂ) :
    Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom (genuineFormalVariables n) ≤
      genuineFormalVariables n := by
  rw [genuineFormalVariables,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G,⟨i,rfl⟩,rfl⟩
  change actualNormalChartTransitionHom A e f v (MvPowerSeries.X i) ∈ genuineFormalVariables n
  rw [actualNormalChartTransition_X]
  have h : actualNormalChartTransitionCoordinates A e f v i ∈ genuineFormalVariables n ^ 1 := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n 1 _).mpr
    intro α hα
    have hd : α.degree=0 := by
      have hd' : α.degree < 1 := by
        simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα
      omega
    have hz : α=0 := (Finsupp.degree_eq_zero_iff α).mp hd
    subst α
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,transition_constant_zero]
  simpa only [pow_one] using h

private theorem transition_comp_inverse_ringHom (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    (actualNormalChartTransitionHom A e f v).toRingHom.comp
      (actualNormalChartTransitionHom A f e (actualNormalChartNormalizedDirection f v)).toRingHom=
        RingHom.id (MvPowerSeries (Fin n) ℂ) := by
  apply RingHom.ext
  intro F
  exact transition_inverse_apply A e f heA hfA v he hf F

/-- BOTH whole selected-centre ideal directions come from the actual inverse normal transitions. -/
theorem map_coordinateIdeal_normal_chart_transition (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom (actualFormalCoordinateIdeal n A)=
      actualFormalCoordinateIdeal n A := by
  apply le_antisymm (transition_centre_le A e f heA hfA v hf)
  have hwe : actualNormalChartNormalizedDirection f v e ≠ 0 := by
    rw [normalized_at_old_pivot e f v he]
    exact inv_ne_zero hf
  have h := Ideal.map_mono (f := (actualNormalChartTransitionHom A e f v).toRingHom)
    (transition_centre_le A f e hfA heA (actualNormalChartNormalizedDirection f v) hwe)
  rw [Ideal.map_map,transition_comp_inverse_ringHom A e f heA hfA v he hf,Ideal.map_id] at h
  exact h

/-- The SAME actual chart map preserves and reflects all entire selected-centre powers. -/
theorem mem_coordinate_power_iff_normal_chart_transition (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    actualNormalChartTransitionHom A e f v F ∈ actualFormalCoordinateIdeal n A ^ q ↔
      F ∈ actualFormalCoordinateIdeal n A ^ q := by
  have hmap : Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom
      (actualFormalCoordinateIdeal n A ^ q)=actualFormalCoordinateIdeal n A ^ q := by
    rw [Ideal.map_pow,map_coordinateIdeal_normal_chart_transition A e f heA hfA v he hf]
  constructor
  · intro hF
    rw [← hmap] at hF
    obtain ⟨G,hG,hEq⟩ := (Ideal.mem_map_iff_of_surjective _
      (actualNormalChartTransitionAlgEquiv A e f heA hfA v he hf).surjective).mp hF
    have heq : G=F := (actualNormalChartTransitionAlgEquiv A e f heA hfA v he hf).injective hEq
    rwa [heq] at hG
  · intro hF
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hF

/-- The entire maximal ideal is unchanged, with all tangent coordinates still fixed individually. -/
theorem map_genuineFormalVariables_normal_chart_transition (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom (genuineFormalVariables n)=
      genuineFormalVariables n := by
  apply le_antisymm (transition_variables_le A e f v)
  have h := Ideal.map_mono (f := (actualNormalChartTransitionHom A e f v).toRingHom)
    (transition_variables_le A f e (actualNormalChartNormalizedDirection f v))
  rw [Ideal.map_map,transition_comp_inverse_ringHom A e f heA hfA v he hf,Ideal.map_id] at h
  exact h

/-- Every genuine total-order lower bound is reflected by this same actual normal-centre transition. -/
theorem mem_genuineFormalVariables_power_iff_normal_chart_transition (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    actualNormalChartTransitionHom A e f v F ∈ genuineFormalVariables n ^ q ↔
      F ∈ genuineFormalVariables n ^ q := by
  have hmap : Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom
      (genuineFormalVariables n ^ q)=genuineFormalVariables n ^ q := by
    rw [Ideal.map_pow,map_genuineFormalVariables_normal_chart_transition A e f heA hfA v he hf]
  constructor
  · intro hF
    rw [← hmap] at hF
    obtain ⟨G,hG,hEq⟩ := (Ideal.mem_map_iff_of_surjective _
      (actualNormalChartTransitionAlgEquiv A e f heA hfA v he hf).surjective).mp hF
    have heq : G=F := (actualNormalChartTransitionAlgEquiv A e f heA hfA v he hf).injective hEq
    rwa [heq] at hG
  · intro hF
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hF

private theorem map_strict_transition_le (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (A : Set (Fin n)) (e f : Fin n) (heA : e ∈ A) (hfA : f ∈ A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom
      (actualFormalStrictTransform K A f hfA (actualNormalChartNormalizedDirection f v)) ≤
        actualFormalStrictTransform K A e heA v := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal K A f hfA
    (actualNormalChartNormalizedDirection f v),actualNormalizedOriginalMemberIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro G ⟨H,⟨μ,F,hFK,hF,rfl⟩,rfl⟩
  apply (Ideal.unit_mul_mem_iff_mem _ ((pivot_isUnit e f v hf).pow μ)).mp
  change actualNormalChartPivotUnit e f v ^ μ * actualNormalChartTransitionHom A e f v
    (actualNormalizedFormalMember A f hfA (actualNormalChartNormalizedDirection f v) μ F hF) ∈
      actualFormalStrictTransform K A e heA v
  rw [actualNormalChartTransition_normalized_member A e f heA hfA v he hf]
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  exact Ideal.subset_span ⟨μ,F,hFK,hF,rfl⟩

/-- BOTH whole strict-ideal directions retain the original ideal and ALL of its normalized original members. -/
theorem map_actual_normal_strict_chart_transition (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (A : Set (Fin n)) (e f : Fin n) (heA : e ∈ A) (hfA : f ∈ A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) :
    Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom
      (actualFormalStrictTransform K A f hfA (actualNormalChartNormalizedDirection f v))=
        actualFormalStrictTransform K A e heA v := by
  apply le_antisymm (map_strict_transition_le K A e f heA hfA v he hf)
  have hwe : actualNormalChartNormalizedDirection f v e ≠ 0 := by
    rw [normalized_at_old_pivot e f v he]
    exact inv_ne_zero hf
  have hrev := map_strict_transition_le K A f e hfA heA (actualNormalChartNormalizedDirection f v)
    (normalized_at_pivot f v hf) hwe
  rw [normalized_twice e f v he hf] at hrev
  have h := Ideal.map_mono (f := (actualNormalChartTransitionHom A e f v).toRingHom) hrev
  rw [Ideal.map_map,transition_comp_inverse_ringHom A e f heA hfA v he hf,Ideal.map_id] at h
  exact h

/-- Every genuine whole strict HS value agrees in the two actual general-centre charts. -/
theorem genuineFormalHilbertSamuelValue_normal_chart_transition
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K A f hfA (actualNormalChartNormalizedDirection f v)) ℓ=
        genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e heA v) ℓ := by
  let E := actualNormalChartTransitionAlgEquiv A e f heA hfA v he hf
  have hmap : actualFormalStrictTransform K A e heA v ⊔ genuineFormalVariables n ^ (ℓ+1)=
      Ideal.map E.toRingEquiv.toRingHom
        (actualFormalStrictTransform K A f hfA (actualNormalChartNormalizedDirection f v) ⊔
          genuineFormalVariables n ^ (ℓ+1)) := by
    change _=Ideal.map (actualNormalChartTransitionHom A e f v).toRingHom _
    rw [Ideal.map_sup,Ideal.map_pow,map_actual_normal_strict_chart_transition K A e f heA hfA v he hf,
      map_genuineFormalVariables_normal_chart_transition A e f heA hfA v he hf]
  exact (Ideal.quotientEquivAlg _ _ E hmap).toLinearEquiv.finrank_eq

/-- Genuine overlap units and the SAME chart map transfer all lower total-order bounds for the SAME original member. -/
theorem normalized_member_mem_power_iff_normal_chart_transition (A : Set (Fin n)) (e f : Fin n)
    (heA : e ∈ A) (hfA : f ∈ A) (v : Fin n → ℂ) (he : v e=1) (hf : v f ≠ 0)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) (q : ℕ) :
    actualNormalizedFormalMember A e heA v μ F hF ∈ genuineFormalVariables n ^ q ↔
      actualNormalizedFormalMember A f hfA (actualNormalChartNormalizedDirection f v) μ F hF ∈
        genuineFormalVariables n ^ q := by
  have hunit := Ideal.unit_mul_mem_iff_mem (genuineFormalVariables n ^ q)
    (x := actualNormalChartTransitionHom A e f v
      (actualNormalizedFormalMember A f hfA (actualNormalChartNormalizedDirection f v) μ F hF))
    ((pivot_isUnit e f v hf).pow μ)
  rw [actualNormalChartTransition_normalized_member A e f heA hfA v he hf] at hunit
  exact hunit.trans
    (mem_genuineFormalVariables_power_iff_normal_chart_transition A e f heA hfA v he hf q _)

end
end Hironaka.HironakaActualNormalCentreChartTransition
