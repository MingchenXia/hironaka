import Hironaka.Resolution.HironakaActualPointExceptionalFibre
import Hironaka.Resolution.HironakaActualPointNormalizedBennett
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-! The whole exceptional cone, its literal projection, and the actual radial HS comparison. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointExceptionalFibreRadial
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualHomogeneousInitialHS
  HironakaActualFiniteInitialGeneration HironakaActualPointExceptionalInitialForm
  HironakaActualPointDehomogenizedInitial HironakaActualPointExceptionalFibre
  HironakaActualPointInitialIdealInclusion HironakaActualPointNormalizedBennett
  HironakaActualCoefficientPresentationCentrePower HironakaActualUnshiftedInitialHSTransfer
variable {n : ℕ}

private def exceptionalComplementEmbedding (e : Fin n) : {i : Fin n // i ≠ e} ↪ Fin n :=
  ⟨Subtype.val,Subtype.val_injective⟩

private theorem exceptional_not_mem_complement (e : Fin n) :
    e ∉ range (exceptionalComplementEmbedding e) := by
  rintro ⟨i,hi⟩
  exact i.property hi

/-- The literal formal projection setting exactly the exceptional variable to zero. -/
def actualPointExceptionalProjection (e : Fin n) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  (MvPowerSeries.rename (exceptionalComplementEmbedding e)).comp
    (MvPowerSeries.killCompl (exceptionalComplementEmbedding e))

/-- Every actual formal coefficient is retained or killed according to the exceptional exponent. -/
theorem coeff_actualPointExceptionalProjection (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (actualPointExceptionalProjection e F)=
      if α e=0 then MvPowerSeries.coeff α F else 0 := by
  by_cases hα : α e=0
  · rw [if_pos hα]
    let β := α.subtypeDomain (fun i => i ≠ e)
    have hβ : Finsupp.embDomain (exceptionalComplementEmbedding e) β=α := by
      ext i
      by_cases hi : i=e
      · subst i
        rw [Finsupp.embDomain_of_notMem_range _ _ _ (exceptional_not_mem_complement e)]
        exact hα.symm
      · change Finsupp.embDomain (exceptionalComplementEmbedding e) β
          (exceptionalComplementEmbedding e ⟨i,hi⟩)=α i
        rw [Finsupp.embDomain_apply_self]
        rfl
    change MvPowerSeries.coeff α
      (MvPowerSeries.rename (exceptionalComplementEmbedding e)
        (MvPowerSeries.killCompl (exceptionalComplementEmbedding e) F))=MvPowerSeries.coeff α F
    rw [← hβ,MvPowerSeries.coeff_embDomain_rename,MvPowerSeries.coeff_killCompl]
  · rw [if_neg hα]
    change MvPowerSeries.coeff α
      (MvPowerSeries.rename (exceptionalComplementEmbedding e)
        (MvPowerSeries.killCompl (exceptionalComplementEmbedding e) F))=0
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨β,hβ⟩
    have hz : (Finsupp.mapDomain (exceptionalComplementEmbedding e) β) e=0 := by
      rw [← Finsupp.embDomain_eq_mapDomain]
      exact Finsupp.embDomain_of_notMem_range _ _ _ (exceptional_not_mem_complement e)
    exact hα ((congrArg (fun γ : Fin n →₀ ℕ => γ e) hβ).symm.trans hz)

/-- The actual projection fixes the original coefficient field. -/
theorem actualPointExceptionalProjection_C (e : Fin n) (c : ℂ) :
    actualPointExceptionalProjection e (MvPowerSeries.C c)=MvPowerSeries.C c :=
  (actualPointExceptionalProjection e).commutes c

/-- The actual projection kills precisely the exceptional coordinate and fixes the others. -/
theorem actualPointExceptionalProjection_X (e i : Fin n) :
    actualPointExceptionalProjection e (MvPowerSeries.X i)=
      if i=e then 0 else MvPowerSeries.X i := by
  by_cases hi : i=e
  · subst i
    change MvPowerSeries.rename (exceptionalComplementEmbedding e)
      (MvPowerSeries.killCompl (exceptionalComplementEmbedding e) (MvPowerSeries.X e))=ite (e=e) 0 _
    rw [MvPowerSeries.killCompl_X_eq_zero (exceptional_not_mem_complement e),map_zero,if_pos rfl]
  · rw [if_neg hi]
    change MvPowerSeries.rename (exceptionalComplementEmbedding e)
      (MvPowerSeries.killCompl (exceptionalComplementEmbedding e)
        (MvPowerSeries.X (exceptionalComplementEmbedding e ⟨i,hi⟩)))=MvPowerSeries.X i
    rw [MvPowerSeries.killCompl_X,MvPowerSeries.rename_X]
    rfl

/-- Every finite actual dehomogenized polynomial is fixed by the same whole formal projection. -/
theorem actualPointExceptionalProjection_dehomogenization (e : Fin n) (b : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    actualPointExceptionalProjection e (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ)=
      (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ) := by
  have hm : (actualPointExceptionalProjection e).comp
      (MvPolynomial.aeval (fun i => if i=e then (1 : MvPowerSeries (Fin n) ℂ)
        else MvPowerSeries.C (b i)+MvPowerSeries.X i))=
      MvPolynomial.aeval (fun i => if i=e then (1 : MvPowerSeries (Fin n) ℂ)
        else MvPowerSeries.C (b i)+MvPowerSeries.X i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]
    by_cases hi : i=e
    · simp only [if_pos hi,map_one]
    · simp only [if_neg hi,map_add,actualPointExceptionalProjection_C,
        actualPointExceptionalProjection_X]
  simpa only [actualPointDehomogenization_coe,AlgHom.comp_apply] using DFunLike.congr_fun hm P

/-- Each unchanged dehomogenized polynomial is genuinely independent of the exceptional variable. -/
theorem pderiv_actualPointDehomogenization_eq_zero (e : Fin n) (b : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ e (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ)=0 := by
  apply MvPowerSeries.ext
  intro α
  rw [MvPowerSeries.coeff_pderiv,map_zero]
  have hcoeff : MvPowerSeries.coeff (α+Finsupp.single e 1)
      (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ)=0 := by
    calc
      _=MvPowerSeries.coeff (α+Finsupp.single e 1)
          (actualPointExceptionalProjection e
            (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ)) :=
        congrArg (MvPowerSeries.coeff (α+Finsupp.single e 1))
          (actualPointExceptionalProjection_dehomogenization e b P).symm
      _=0 := by
        rw [coeff_actualPointExceptionalProjection,if_neg]
        simp only [Finsupp.add_apply,Finsupp.single_eq_same]
        omega
  rw [hcoeff,zero_mul]

private theorem map_span_eq_of_fixed {R : Type*} [CommRing R] (σ : R →+* R)
    (S : Set R) (h : ∀ x ∈ S, σ x=x) : Ideal.map σ (Ideal.span S)=Ideal.span S := by
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    rwa [h y hy]
  · intro hx
    exact ⟨x,hx,h x hx⟩

/-- The entire actual dehomogenized cone is fixed under the literal exceptional projection. -/
theorem map_actualDehomogenizedPointInitialConeIdeal_projection
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (actualPointExceptionalProjection e).toRingHom
      (actualDehomogenizedPointInitialConeIdeal I e b)=actualDehomogenizedPointInitialConeIdeal I e b := by
  rw [actualDehomogenizedPointInitialConeIdeal,actualPointInitialConePolynomialIdeal,Ideal.map_span]
  apply map_span_eq_of_fixed
  rintro F ⟨P,_hP,rfl⟩
  exact actualPointExceptionalProjection_dehomogenization e b P

private theorem map_exceptional_ideal_projection (e : Fin n) :
    Ideal.map (actualPointExceptionalProjection e).toRingHom
      (Ideal.span {MvPowerSeries.X e})=⊥ := by
  rw [Ideal.map_span,Set.image_singleton]
  change Ideal.span {actualPointExceptionalProjection e (MvPowerSeries.X e)}=⊥
  rw [actualPointExceptionalProjection_X,if_pos rfl,Ideal.span_singleton_zero]

/-- The existing finite original initial polynomials' entire formal dehomogenized ideal. -/
def actualFinitePointDehomogenizedFormalIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (b : Fin n → ℂ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex I =>
    (actualPointDehomogenization e b (actualInitialVertexPolynomial I a) : MvPowerSeries (Fin n) ℂ))

private theorem map_finite_dehomogenized_projection
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (actualPointExceptionalProjection e).toRingHom
      (actualFinitePointDehomogenizedFormalIdeal I e b)=actualFinitePointDehomogenizedFormalIdeal I e b := by
  rw [actualFinitePointDehomogenizedFormalIdeal]
  apply map_span_eq_of_fixed
  rintro F ⟨a,rfl⟩
  exact actualPointExceptionalProjection_dehomogenization e b (actualInitialVertexPolynomial I a)

private theorem point_weight_eq_normal_degree (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) a=normalExponentDegree a := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]

private theorem actualVertexSeries_mem_point_power
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices MonomialOrder.degLex I) :
    actualVertexSeries MonomialOrder.degLex I a ∈ actualFormalCoordinateIdeal n Set.univ ^
      Finsupp.weight (actualCoordinateWeight Set.univ) a.val := by
  rw [point_weight_eq_normal_degree]
  simpa only [actualFormalCoordinateIdeal,Set.image_univ,genuineFormalVariables]
    using actualVertexSeries_mem_degree_power I a

private theorem span_range_sup_eq_of_sub_mem {ι R : Type*} [CommRing R]
    (F G : ι → R) (E : Ideal R) (h : ∀ i, F i-G i ∈ E) :
    Ideal.span (range F) ⊔ E=Ideal.span (range G) ⊔ E := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro f ⟨i,rfl⟩
    have hsum := (Ideal.span (range G) ⊔ E).add_mem
      (Ideal.mem_sup_right (h i)) (Ideal.mem_sup_left (Ideal.subset_span ⟨i,rfl⟩))
    simpa only [SetLike.mem_coe,sub_add_cancel] using hsum
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    have hneg : G i-F i ∈ E := by simpa only [neg_sub] using E.neg_mem (h i)
    have hsum := (Ideal.span (range F) ⊔ E).add_mem
      (Ideal.mem_sup_right hneg) (Ideal.mem_sup_left (Ideal.subset_span ⟨i,rfl⟩))
    simpa only [SetLike.mem_coe,sub_add_cancel] using hsum

/-- The same entire strict fibre is generated by the existing genuine finite initial polynomials. -/
theorem actual_point_strict_exceptional_fibre_eq_finite_initial
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    actualFormalStrictTransform I Set.univ e (mem_univ e) b ⊔ Ideal.span {MvPowerSeries.X e} =
      actualFinitePointDehomogenizedFormalIdeal I e b ⊔ Ideal.span {MvPowerSeries.X e} := by
  rw [actualFormalStrictTransform_eq_vertex_span MonomialOrder.degLex I Set.univ e (mem_univ e) b
    (actualVertexSeries_mem_point_power I),actualFinitePointDehomogenizedFormalIdeal]
  apply span_range_sup_eq_of_sub_mem
  intro a
  have hP : actualPointHomogeneousPolynomial
      (Finsupp.weight (actualCoordinateWeight Set.univ) a.val)
      (actualVertexSeries MonomialOrder.degLex I a)=actualInitialVertexPolynomial I a := by
    apply MvPolynomial.coe_injective
    rw [actualPointHomogeneousPolynomial_coe,actualInitialVertexPolynomial_coe,
      actualHomogeneousInitialForm,actualHomogeneousInitialDegree,
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose_spec.1,point_weight_eq_normal_degree]
  have h := actual_point_normalized_member_congr_dehomogenization e b _
    (actualVertexSeries MonomialOrder.degLex I a) (actualVertexSeries_mem_point_power I a)
  rwa [hP] at h

/-- Applying the actual projection upgrades fibre equality to equality of the two entire cone models. -/
theorem actualDehomogenizedPointInitialConeIdeal_eq_finite
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    actualDehomogenizedPointInitialConeIdeal I e b=actualFinitePointDehomogenizedFormalIdeal I e b := by
  have h := (actual_point_strict_exceptional_fibre_eq_dehomogenized_initial_cone I e b).symm.trans
    (actual_point_strict_exceptional_fibre_eq_finite_initial I e b)
  have hm := congrArg (Ideal.map (actualPointExceptionalProjection e).toRingHom) h
  simpa only [Ideal.map_sup,map_actualDehomogenizedPointInitialConeIdeal_projection,
    map_finite_dehomogenized_projection,map_exceptional_ideal_projection,sup_bot_eq] using hm

/-- The actual exceptional partial preserves the entire unchanged dehomogenized cone ideal. -/
theorem pderiv_mem_actualDehomogenizedPointInitialConeIdeal
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualDehomogenizedPointInitialConeIdeal I e b) :
    MvPowerSeries.pderiv ℂ e F ∈ actualDehomogenizedPointInitialConeIdeal I e b := by
  rw [actualDehomogenizedPointInitialConeIdeal_eq_finite,actualFinitePointDehomogenizedFormalIdeal] at hF
  obtain ⟨c,hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hF
  rw [← hc]
  change MvPowerSeries.pderiv ℂ e
    (∑ a ∈ c.support, c a * (actualPointDehomogenization e b
      (actualInitialVertexPolynomial I a) : MvPowerSeries (Fin n) ℂ)) ∈ _
  rw [map_sum]
  apply Ideal.sum_mem
  intro a _
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,pderiv_actualPointDehomogenization_eq_zero,
    mul_zero,zero_add]
  apply Ideal.mul_mem_right
  rw [actualDehomogenizedPointInitialConeIdeal_eq_finite]
  exact Ideal.subset_span ⟨a,rfl⟩

private theorem actualTaylor_polynomial_eval (P : MvPolynomial (Fin n) ℂ) :
    actualUnshiftedTaylorAlgHom n
      (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n)) P)=
        (P : MvPowerSeries (Fin n) ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C,MvPolynomial.coe_C]
      exact (actualUnshiftedTaylorAlgHom n).commutes c
  | add P Q hP hQ =>
      simpa only [map_add,MvPolynomial.coe_add] using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
      simp only [map_mul,MvPolynomial.aeval_X,hP,actualUnshiftedTaylor_coordinate,
        MvPolynomial.coe_mul,MvPolynomial.coe_X]

/-- The literal Taylor extension of the existing analytic finite ideal is the entire source cone image. -/
theorem actualDehomogenizedInitialIdeal_formal_extension_whole_cone
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (actualDehomogenizedInitialIdeal I e b)=actualDehomogenizedPointInitialConeIdeal I e b := by
  rw [actualDehomogenizedPointInitialConeIdeal_eq_finite,actualDehomogenizedInitialIdeal,
    actualFinitePointDehomogenizedFormalIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact actualTaylor_polynomial_eval (actualPointDehomogenization e b (actualInitialVertexPolynomial I a))

/-- The whole exceptional cone's genuine all-order HS bound uses the actual radial coordinate equivalence. -/
theorem genuineFormalHilbertSamuelValue_actualDehomogenizedPointInitialConeIdeal_le
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n (actualDehomogenizedPointInitialConeIdeal I e b) ℓ ≤
      genuineFormalHilbertSamuelValue n I ℓ := by
  calc
    _=hilbertSamuelValue (actualDehomogenizedInitialIdeal I e b) ℓ := by
      rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
        actualDehomogenizedInitialIdeal_formal_extension_whole_cone]
    _=hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal I
        (HironakaActualPointUnitCoordinateChange.actualPointUnitBasePoint e b)) ℓ :=
      hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated I e b ℓ
    _≤genuineFormalHilbertSamuelValue n I ℓ :=
      hilbertSamuelValue_actual_unshifted_translated_initial_le I _ ℓ

end
end Hironaka.HironakaActualPointExceptionalFibreRadial
