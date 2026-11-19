import Hironaka.Resolution.HironakaActualPointDehomogenizedInitial
import Hironaka.Resolution.HironakaActualPointCentreStrictGenerators
import Hironaka.Resolution.HironakaActualCoefficientReducedStrictGenerators
import Hironaka.Resolution.HironakaActualFiniteInitialGeneration
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The entire exceptional fibre of the genuine point strict ideal, for every direction. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointExceptionalFibre
noncomputable section
open HironakaActualOriginalFormalHSTransfer HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalStrictGenerators
  HironakaActualCoefficientReducedStrictGenerators HironakaActualPointCentreStrictGenerators
  HironakaActualHomogeneousInitialHS HironakaActualFiniteInitialGeneration
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
variable {n : ℕ}

private theorem point_weight_eq_degree (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) a=Finsupp.degree a := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,Finsupp.degree_eq_sum]

private theorem point_coordinate_ideal_eq_variables :
    actualFormalCoordinateIdeal n Set.univ=genuineFormalVariables n := by
  simp only [actualFormalCoordinateIdeal,Set.image_univ,genuineFormalVariables]

/-- The whole polynomial initial cone, defined using every actual filtered original member. -/
def actualPointInitialConePolynomialIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span {P | ∃ (q : ℕ) (F : MvPowerSeries (Fin n) ℂ),
    F ∈ I ∧ F ∈ actualFormalCoordinateIdeal n Set.univ ^ q ∧
      P=actualPointHomogeneousPolynomial q F}

/-- The literal whole polynomial cone is homogeneous under the genuine polynomial grading. -/
theorem actualPointInitialConePolynomialIdeal_homogeneous
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    letI := MvPolynomial.gradedAlgebra (σ := Fin n) (R := ℂ)
    (actualPointInitialConePolynomialIdeal I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
  let := MvPolynomial.gradedAlgebra (σ := Fin n) (R := ℂ)
  rw [actualPointInitialConePolynomialIdeal]
  apply Ideal.homogeneous_span
  rintro P ⟨q,F,_hFI,_hF,rfl⟩
  exact ⟨q,actualPointHomogeneousPolynomial_isHomogeneous q F⟩

/-- Both whole ideal inclusions identify the cone's formal extension with the actual initial ideal. -/
theorem map_actualPointInitialConePolynomialIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom
      (actualPointInitialConePolynomialIdeal I)=actualHomogeneousInitialIdeal I := by
  apply le_antisymm
  · rw [actualPointInitialConePolynomialIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro G ⟨P,⟨q,F,hFI,hF,rfl⟩,rfl⟩
    change (actualPointHomogeneousPolynomial q F : MvPowerSeries (Fin n) ℂ) ∈ _
    rw [actualPointHomogeneousPolynomial_coe,actualHomogeneousInitialIdeal_eq_initial_vertex_span]
    apply actualFormalMember_component_mem_initial_vertex_span I q F hFI
    rwa [← point_coordinate_ideal_eq_variables]
  · apply Ideal.span_le.mpr
    rintro G ⟨F,rfl⟩
    change actualHomogeneousInitialForm F.val F.property.2 ∈ _
    let q := actualHomogeneousInitialDegree F.val F.property.2
    have hF : F.val ∈ actualFormalCoordinateIdeal n Set.univ ^ q := by
      apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ q F.val).mpr
      intro a ha
      apply MvPowerSeries.coeff_of_lt_order
      rw [← actualHomogeneousInitialDegree_eq_order F.val F.property.2]
      have ha' : Finsupp.degree a < q := by rwa [point_weight_eq_degree] at ha
      exact_mod_cast ha'
    have hP : actualPointHomogeneousPolynomial q F.val ∈ actualPointInitialConePolynomialIdeal I :=
      Ideal.subset_span ⟨q,F.val,F.property.1,hF,rfl⟩
    have hmem := Ideal.mem_map_of_mem MvPolynomial.coeToMvPowerSeries.ringHom hP
    change (actualPointHomogeneousPolynomial q F.val : MvPowerSeries (Fin n) ℂ) ∈ _ at hmem
    simpa only [SetLike.mem_coe,actualPointHomogeneousPolynomial_coe,actualHomogeneousInitialForm,q] using hmem

/-- Actual polynomial point-chart dehomogenization, followed by the literal formal inclusion. -/
def actualPointDehomogenizationFormalMap (e : Fin n) (b : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →+* MvPowerSeries (Fin n) ℂ :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPointDehomogenization e b).toRingHom

/-- The entire dehomogenized source cone ideal in the genuine formal chart ring. -/
def actualDehomogenizedPointInitialConeIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (b : Fin n → ℂ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.map (actualPointDehomogenizationFormalMap e b) (actualPointInitialConePolynomialIdeal I)

/-- Unconditional entire exceptional-fibre equality, for every point-chart direction. -/
theorem actual_point_strict_exceptional_fibre_eq_dehomogenized_initial_cone
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    actualFormalStrictTransform I Set.univ e (mem_univ e) b ⊔ Ideal.span {MvPowerSeries.X e} =
      actualDehomogenizedPointInitialConeIdeal I e b ⊔ Ideal.span {MvPowerSeries.X e} := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨q,F,hFI,hF,rfl⟩
    have hP : (actualPointDehomogenization e b (actualPointHomogeneousPolynomial q F) :
        MvPowerSeries (Fin n) ℂ) ∈ actualDehomogenizedPointInitialConeIdeal I e b :=
      Ideal.mem_map_of_mem (actualPointDehomogenizationFormalMap e b)
        (Ideal.subset_span ⟨q,F,hFI,hF,rfl⟩)
    have hdiff := actual_point_normalized_member_congr_dehomogenization e b q F hF
    have hsum := (actualDehomogenizedPointInitialConeIdeal I e b ⊔
      Ideal.span {MvPowerSeries.X e}).add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left hP)
    simpa only [SetLike.mem_coe,sub_add_cancel] using hsum
  · apply sup_le _ le_sup_right
    rw [actualDehomogenizedPointInitialConeIdeal,Ideal.map_le_iff_le_comap,
      actualPointInitialConePolynomialIdeal]
    apply Ideal.span_le.mpr
    rintro P ⟨q,F,hFI,hF,rfl⟩
    rw [SetLike.mem_coe,Ideal.mem_comap]
    change (actualPointDehomogenization e b (actualPointHomogeneousPolynomial q F) :
      MvPowerSeries (Fin n) ℂ) ∈
        actualFormalStrictTransform I Set.univ e (mem_univ e) b ⊔ Ideal.span {MvPowerSeries.X e}
    have hN : actualNormalizedFormalMember Set.univ e (mem_univ e) b q F hF ∈
        actualFormalStrictTransform I Set.univ e (mem_univ e) b := by
      rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
      exact Ideal.subset_span ⟨q,F,hFI,hF,rfl⟩
    have hdiff := actual_point_normalized_member_congr_dehomogenization e b q F hF
    have hneg : (actualPointDehomogenization e b (actualPointHomogeneousPolynomial q F) :
        MvPowerSeries (Fin n) ℂ)-
        actualNormalizedFormalMember Set.univ e (mem_univ e) b q F hF ∈
          Ideal.span {MvPowerSeries.X e} := by
      simpa only [neg_sub] using
        (Ideal.span {(MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)}).neg_mem hdiff
    have hsum := (actualFormalStrictTransform I Set.univ e (mem_univ e) b ⊔
      Ideal.span {MvPowerSeries.X e}).add_mem (Ideal.mem_sup_right hneg) (Ideal.mem_sup_left hN)
    simpa only [SetLike.mem_coe,sub_add_cancel] using hsum

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

/-- The unchanged canonical source vertices' actual dehomogenized leading polynomials. -/
def actualCanonicalPointDehomogenizedIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (b : Fin n → ℂ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex I =>
    (actualPointDehomogenization e b
      (actualPointHomogeneousPolynomial (Finsupp.weight (actualCoordinateWeight Set.univ) a.val)
        (actualReducedVertexSeries MonomialOrder.degLex I a)) : MvPowerSeries (Fin n) ℂ))

/-- The entire actual fibre uses the SAME canonical source members, with their point powers proved internally. -/
theorem actual_point_strict_exceptional_fibre_eq_canonical_reduced
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    actualFormalStrictTransform I Set.univ e (mem_univ e) b ⊔ Ideal.span {MvPowerSeries.X e} =
      actualCanonicalPointDehomogenizedIdeal I e b ⊔ Ideal.span {MvPowerSeries.X e} := by
  rw [actualFormalStrictTransform_eq_reduced_vertex_span MonomialOrder.degLex I
    Set.univ e (mem_univ e) b (actualReducedVertexSeries_mem_point_power n I),
    actualCanonicalPointDehomogenizedIdeal]
  apply span_range_sup_eq_of_sub_mem
  intro a
  exact actual_point_normalized_member_congr_dehomogenization e b _
    (actualReducedVertexSeries MonomialOrder.degLex I a)
    (actualReducedVertexSeries_mem_point_power n I a)

/-- The entire dehomogenized cone and the SAME canonical finite ideal have identical exceptional fibres. -/
theorem actual_point_initial_cone_exceptional_fibre_eq_canonical_reduced
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    actualDehomogenizedPointInitialConeIdeal I e b ⊔ Ideal.span {MvPowerSeries.X e} =
      actualCanonicalPointDehomogenizedIdeal I e b ⊔ Ideal.span {MvPowerSeries.X e} :=
  (actual_point_strict_exceptional_fibre_eq_dehomogenized_initial_cone I e b).symm.trans
    (actual_point_strict_exceptional_fibre_eq_canonical_reduced I e b)

/-- The literal exceptional quotient map identifies the entire strict and whole-cone images. -/
theorem map_actual_point_strict_exceptional_quotient_eq_initial_cone
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.X e}))
        (actualFormalStrictTransform I Set.univ e (mem_univ e) b) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.X e}))
        (actualDehomogenizedPointInitialConeIdeal I e b) := by
  have h := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.X e})))
    (actual_point_strict_exceptional_fibre_eq_dehomogenized_initial_cone I e b)
  simpa only [Ideal.map_sup,Ideal.map_quotient_self,sup_bot_eq] using h

/-- The same literal exceptional quotient map also identifies the canonical finite image. -/
theorem map_actual_point_strict_exceptional_quotient_eq_canonical_reduced
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.X e}))
        (actualFormalStrictTransform I Set.univ e (mem_univ e) b) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.X e}))
        (actualCanonicalPointDehomogenizedIdeal I e b) := by
  have h := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.X e})))
    (actual_point_strict_exceptional_fibre_eq_canonical_reduced I e b)
  simpa only [Ideal.map_sup,Ideal.map_quotient_self,sup_bot_eq] using h

end
end Hironaka.HironakaActualPointExceptionalFibre
