/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalWeightedDivision
import Hironaka.Resolution.HironakaActualHomogeneousInitialHS

/-! Genuine finite initial generators and one actual original polynomial ideal realizing all HS values. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFiniteInitialGeneration
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalWeightedDivision HironakaActualHomogeneousInitialHS
variable {n : ℕ}

/-- The finite span uses the SAME actual original monic vertex series' literal initial forms. -/
def actualInitialVertexSpan (I : Ideal (MvPowerSeries (Fin n) ℂ)) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex I =>
    actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose)

private theorem power_le_order (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ genuineFormalVariables n ^ q) : (q : ℕ∞) ≤ F.order := by
  apply MvPowerSeries.nat_le_order
  intro a ha
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hF a
  simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using ha

/-- Genuine vertex minimum coefficients give the true whole maximal-power bound internally. -/
theorem actualVertexSeries_mem_degree_power (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) :
    actualVertexSeries MonomialOrder.degLex I a ∈ genuineFormalVariables n ^ normalExponentDegree a.val := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mpr
  intro b hb
  apply actualVertexSeries_total_degree_compatible I a b
  simpa only [actualWeight_one] using hb

/-- The SAME actual division coefficient has its genuine shifted whole-power bound. -/
theorem actualFormalQuotient_mem_shifted_power (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ genuineFormalVariables n ^ q)
    (a : actualInitialVertices MonomialOrder.degLex I) :
    actualFormalQuotient MonomialOrder.degLex I F a ∈
      genuineFormalVariables n ^ (q-normalExponentDegree a.val) := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mpr
  intro b hb
  exact (actual_formal_degreelex_division_maximal_filtration I F q hF).2 a b (by omega)

attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in
/-- True product components retain actual filtered quotient coefficients and SAME original vertex initial forms. -/
theorem actualFormalQuotient_vertex_product_component (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ genuineFormalVariables n ^ q)
    (a : actualInitialVertices MonomialOrder.degLex I) :
    MvPowerSeries.homogeneousComponent q
      (actualFormalQuotient MonomialOrder.degLex I F a*actualVertexSeries MonomialOrder.degLex I a)=
      if normalExponentDegree a.val ≤ q then
        MvPowerSeries.homogeneousComponent (q-normalExponentDegree a.val)
          (actualFormalQuotient MonomialOrder.degLex I F a)*
            actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
              (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose
      else 0 := by
  by_cases ha : normalExponentDegree a.val ≤ q
  · rw [if_pos ha]
    have hQ := power_le_order (q-normalExponentDegree a.val) _
      (actualFormalQuotient_mem_shifted_power I q F hF a)
    have hf := power_le_order _ _ (actualVertexSeries_mem_degree_power I a)
    have hp := MvPowerSeries.homogeneousComponent_mul_of_le_order hQ hf
    rw [Nat.sub_add_cancel ha] at hp
    rw [actualHomogeneousInitialForm,actualHomogeneousInitialDegree,
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose_spec.1]
    exact hp
  · rw [if_neg ha]
    have hf : actualVertexSeries MonomialOrder.degLex I a ∈ genuineFormalVariables n ^ (q+1) :=
      Ideal.pow_le_pow_right (by omega) (actualVertexSeries_mem_degree_power I a)
    have hp := power_le_order (q+1) _ ((genuineFormalVariables n ^ (q+1)).mul_mem_left
      (actualFormalQuotient MonomialOrder.degLex I F a) hf)
    apply MvPowerSeries.homogeneousComponent_of_lt_order_eq_zero
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self q) hp

/-- Every actual filtered original member's homogeneous component lies in the SAME finite initial-form span. -/
theorem actualFormalMember_component_mem_initial_vertex_span (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hI : F ∈ I) (hF : F ∈ genuineFormalVariables n ^ q) :
    MvPowerSeries.homogeneousComponent q F ∈ actualInitialVertexSpan I := by
  have he := congrArg (MvPowerSeries.homogeneousComponent q)
    (actual_formal_ideal_member_division MonomialOrder.degLex I F hI)
  rw [map_sum] at he
  rw [he]
  apply Ideal.sum_mem
  intro a _
  rw [actualFormalQuotient_vertex_product_component I q F hF a]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a,rfl⟩)
  · exact Ideal.zero_mem _

attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in
/-- BOTH whole ideal directions identify all actual original initial forms with the SAME finite vertex initials. -/
theorem actualHomogeneousInitialIdeal_eq_initial_vertex_span (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualHomogeneousInitialIdeal I=actualInitialVertexSpan I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro G ⟨F,rfl⟩
    change actualHomogeneousInitialForm F.val F.property.2 ∈ actualInitialVertexSpan I
    apply actualFormalMember_component_mem_initial_vertex_span I _ F.val F.property.1
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mpr
    intro b hb
    have ho := actualHomogeneousInitialDegree_eq_order F.val F.property.2
    apply MvPowerSeries.coeff_of_lt_order
    rw [← ho]
    exact_mod_cast (show Finsupp.degree b < actualHomogeneousInitialDegree F.val F.property.2 from
      by simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using hb)
  · apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    apply Ideal.subset_span
    exact ⟨⟨actualVertexSeries MonomialOrder.degLex I a,
      (actualVertexSeries_spec MonomialOrder.degLex I a).1,
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose⟩,rfl⟩

/-- Literal finite polynomial truncation of the SAME homogeneous actual vertex form. -/
def actualInitialVertexPolynomial (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) : MvPolynomial (Fin n) ℂ :=
  MvPowerSeries.truncTotal (normalExponentDegree a.val+1)
    (actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose)

/-- Actual homogeneity proves equality of the ENTIRE genuine polynomial inclusion and initial series. -/
theorem actualInitialVertexPolynomial_coe (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) :
    (actualInitialVertexPolynomial I a : MvPowerSeries (Fin n) ℂ)=
      actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
        (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose := by
  apply MvPowerSeries.ext
  intro b
  rw [actualInitialVertexPolynomial,MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hb
  · rfl
  · symm
    rw [actualHomogeneousInitialForm,MvPowerSeries.coeff_homogeneousComponent,
      actualHomogeneousInitialDegree,(actualVertexSeries_spec MonomialOrder.degLex I a).2.choose_spec.1]
    apply if_neg
    have ht : normalExponentDegree a.val+1 ≤ Finsupp.degree b := not_lt.mp hb
    simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using (show Finsupp.degree b ≠ normalExponentDegree a.val by omega)

/-- One genuine ORIGINAL finite polynomial ideal, defined independently of every HS order. -/
def actualOriginalInitialVertexIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal (HolGerm (ComplexModel (0+n))) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex I =>
    originalPolynomialEval n (actualInitialVertexPolynomial I a))

/-- BOTH WHOLE formal ideal directions realize exactly the actual homogeneous initial ideal. -/
theorem actualOriginalInitialVertexIdeal_formal_extension (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (actualOriginalInitialVertexIdeal I)=
      actualHomogeneousInitialIdeal I := by
  rw [actualOriginalInitialVertexIdeal,Ideal.map_span,← Set.range_comp,
    actualHomogeneousInitialIdeal_eq_initial_vertex_span]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  change originalTaylorAlgHom n (originalPolynomialEval n (actualInitialVertexPolynomial I a))=_
  rw [originalTaylorAlgHom_polynomialEval,actualInitialVertexPolynomial_coe]

/-- The SAME internally constructed original polynomial ideal realizes EVERY genuine HS value. -/
theorem actualOriginalInitialVertexIdeal_hs (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    hilbertSamuelValue (actualOriginalInitialVertexIdeal I) ℓ=genuineFormalHilbertSamuelValue n I ℓ := by
  rw [hilbertSamuelValue_eq_genuine_formal_extension,actualOriginalInitialVertexIdeal_formal_extension]
  exact (genuineFormalHilbertSamuelValue_homogeneous_initial I ℓ).symm

end
end Hironaka.HironakaActualFiniteInitialGeneration
