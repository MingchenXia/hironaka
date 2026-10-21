/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointNormalizedCoefficientBands

/-!
# Directional source stability and the same canonical point orders

Natural directional stability of the actual source initial ideal gives whole
canonical form sparsity and the entire sheared-source shadow dictionary.
Actual whole current jet colons then exclude every low canonical quotient band
by genuine exceptional-factor cancellation and the literal source-band formula.
The source derivation qualification is explicit; no original-only arbitrary
point criterion or relative/history closure is asserted here.
Blueprint: `hironaka-actual-directional-pivot-normality-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualDirectionalPivotNormality
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualDirectionalNormalJet
  HironakaActualHomogeneousInitialHS HironakaActualPointExceptionalInitialForm
  HironakaActualFormalCoordinatePowerDivision HironakaActualPointDehomogenizedInitial
  HironakaActualFormalBlowupAllDirections HironakaActualPointOrderRetainingHS
  HironakaActualExceptionalFilteredDivision HironakaActualPointNormalizedCoefficientBands
  HironakaActualFormalBlowupMemberGeneration HironakaActualInitialPivotNormality
  HironakaActualOriginalFormalHSTransfer HironakaActualFiniteInitialGeneration
  HironakaActualPointCentreStrictGenerators
variable {n : ℕ}
local notation "R" => MvPowerSeries (Fin n) ℂ
local notation "P" => MvPolynomial (Fin n) ℂ
local notation "𝔪" => actualFormalCoordinateIdeal n univ

private theorem pointIdeal_eq_variables : actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
  simp [actualFormalCoordinateIdeal,genuineFormalVariables]

private theorem canonical_power (K : Ideal R) (a : actualInitialVertices MonomialOrder.degLex K) :
    actualReducedVertexSeries MonomialOrder.degLex K a∈𝔪^(normalExponentDegree a.val) := by
  have h := actualReducedVertexSeries_mem_point_power n K a
  simpa [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree] using h

private theorem component_member_initial (K : Ideal R) (q : ℕ) (F : R) (hK : F∈K) (hF : F∈𝔪^q) :
    MvPowerSeries.homogeneousComponent q F∈actualHomogeneousInitialIdeal K := by
  rw [actualHomogeneousInitialIdeal_eq_initial_vertex_span]
  apply actualFormalMember_component_mem_initial_vertex_span K q F hK
  rwa [←pointIdeal_eq_variables]

/-- Natural source directional stability kills the directional derivative of
the literal leading polynomial of each SAME canonical reduced source member. -/
theorem canonical_source_form_directional_zero (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    directionalPolynomialDerivative e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a))=0 := by
  let f := actualPointHomogeneousPolynomial (normalExponentDegree a.val)
    (actualReducedVertexSeries MonomialOrder.degLex K a)
  have hf : (f : R)∈actualHomogeneousInitialIdeal K := by
    rw [show (f : R)=MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a) from actualPointHomogeneousPolynomial_coe _ _]
    exact component_member_initial K _ _ (actualReducedVertexSeries_mem MonomialOrder.degLex K a) (canonical_power K a)
  apply (MvPolynomial.coe_injective (Fin n) ℂ)
  rw [MvPolynomial.coe_zero]
  apply eq_zero_of_mem_of_diagram_coefficients_zero MonomialOrder.degLex (actualHomogeneousInitialIdeal K) _ (hD f hf)
  intro β hβ
  rw [actual_homogeneous_initial_ideal_diagram] at hβ
  rw [MvPolynomial.coeff_coe,directionalPolynomialDerivative,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_pderiv]
  have hΓ : β+Finsupp.single i 1∈actualInitialDiagram MonomialOrder.degLex K := by
    simpa only [add_comm] using actualInitialDiagram_add MonomialOrder.degLex K β (Finsupp.single i 1) hβ
  have hne : β+Finsupp.single i 1≠a.val := by
    intro heq
    have hm : Minimal (·∈actualInitialDiagram MonomialOrder.degLex K) a.val := by
      simpa [actualInitialVertices] using a.property
    have hb : β≤a.val := by rw [←heq];exact le_add_of_nonneg_right zero_le
    have hback := hm.le_of_le hβ hb
    have he := hback i
    rw [←heq,Finsupp.add_apply,Finsupp.single_eq_same] at he
    omega
  have hc := congrArg (MvPowerSeries.coeff (β+Finsupp.single i 1))
    (actualPointHomogeneousPolynomial_coe (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a))
  simp only [MvPolynomial.coeff_coe,MvPowerSeries.coeff_homogeneousComponent] at hc
  change MvPolynomial.coeff (β+Finsupp.single i 1) f=_ at hc
  rw [actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a _ hΓ,if_neg hne] at hc
  simp only [ite_self] at hc
  rw [hc,zero_mul,mul_zero]

/-- Literal dehomogenization of the SAME canonical leading form is genuinely
homogeneous, internally from natural source directional stability. -/
theorem canonical_source_dehomogeneous_homogeneous (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a))).IsHomogeneous (normalExponentDegree a.val) := by
  intro β hβ
  have hz := canonical_source_form_directional_zero K e b hD a
  have hc := dehom_directional_derivative_coefficient e b _ _
    (actualPointHomogeneousPolynomial_isHomogeneous (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a)) β
  rw [hz,map_zero,MvPolynomial.coeff_zero] at hc
  have he : (normalExponentDegree a.val : ℂ)=(β.degree : ℂ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hc.symm).resolve_right hβ)
  have hd : normalExponentDegree a.val=β.degree := by exact_mod_cast he
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hd.symm

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

private theorem projection_dehom (e : Fin n) (b : Fin n → ℂ) (f : P) :
    pivotZeroProjection e (actualPointDehomogenization e b f : R)=(actualPointDehomogenization e b f : R) := by
  apply MvPowerSeries.ext
  intro α
  rw [pivotZeroProjection_coefficient,MvPolynomial.coeff_coe]
  split_ifs with hα
  · rfl
  · symm
    by_contra hc
    exact hα (dehom_pivot_free e b f α (MvPolynomial.mem_support_iff.mpr hc))

private theorem canonical_shadow (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    pivotZeroProjection e (actualNormalizedFormalMember univ e (mem_univ e) b
      (normalExponentDegree a.val) (actualReducedVertexSeries MonomialOrder.degLex K a) (canonical_power K a))=
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex K a)) : R) := by
  have h := actual_point_normalized_member_congr_dehomogenization e b (normalExponentDegree a.val)
    (actualReducedVertexSeries MonomialOrder.degLex K a) (canonical_power K a)
  have hk : pivotZeroProjection e (actualNormalizedFormalMember univ e (mem_univ e) b
      (normalExponentDegree a.val) (actualReducedVertexSeries MonomialOrder.degLex K a) (canonical_power K a)-
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex K a)) : R))=0 :=
    (pivotZeroProjection_eq_zero_iff e _).mpr (Ideal.mem_span_singleton.mp h)
  rwa [map_sub,projection_dehom,sub_eq_zero] at hk

open HironakaActualFormalStrictGenerators HironakaActualFormalFamilyStrictGenerators
  HironakaActualReducedBasisDivision

private theorem projection_strict_eq_dehom_span (K : Ideal R) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (pivotZeroProjection e).toRingHom (actualFormalStrictTransform K univ e (mem_univ e) b)=
      Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex K =>
        (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
          (actualReducedVertexSeries MonomialOrder.degLex K a)) : R)) := by
  let B := actualReducedVertexFamily MonomialOrder.degLex K
  have hv (a : actualInitialVertices MonomialOrder.degLex K) : familyVertexSeries MonomialOrder.degLex K B a∈
      𝔪^Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val :=
    actualReducedVertexSeries_mem_point_power n K a
  rw [actualFormalStrictTransform_eq_family_span MonomialOrder.degLex K B univ e (mem_univ e) b hv,
    Ideal.map_span,←range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  have hw : Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val=normalExponentDegree a.val := by
    simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]
  have hSpec := actualNormalizedFormalMember_spec univ e (mem_univ e) b _
    (familyVertexSeries MonomialOrder.degLex K B a) (hv a)
  change (MvPowerSeries.X e)^Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val*
    familyNormalizedFormalVertex MonomialOrder.degLex K B univ e (mem_univ e) b hv a=
      actualFormalBlowup univ e b (actualReducedVertexSeries MonomialOrder.degLex K a) at hSpec
  rw [hw] at hSpec
  have hn := actualNormalizedFormalMember_unique univ e (mem_univ e) b _ _ (canonical_power K a)
    (familyNormalizedFormalVertex MonomialOrder.degLex K B univ e (mem_univ e) b hv a) hSpec
  change pivotZeroProjection e (familyNormalizedFormalVertex MonomialOrder.degLex K B univ e (mem_univ e) b hv a)=_
  rw [hn]
  exact canonical_shadow K e b a

/-- The entire independent strict ideal has exactly the entire sheared source
initial shadow, derived from natural directional source stability. -/
theorem pivot_projection_strict_eq_sheared_source_initial (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K) :
    Ideal.map (pivotZeroProjection e).toRingHom (actualFormalStrictTransform K univ e (mem_univ e) b)=
      Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K) := by
  rw [projection_strict_eq_dehom_span,actualHomogeneousInitialIdeal_eq_reduced_component_span,
    Ideal.map_span,←range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  change _=actualFormalCenterShear univ e b (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
    (actualReducedVertexSeries MonomialOrder.degLex K a))
  rw [←actualPointHomogeneousPolynomial_coe]
  exact (centerShear_eq_dehom_of_homogeneous_dehom e b _ _
    (actualPointHomogeneousPolynomial_isHomogeneous _ _)
    (canonical_source_dehomogeneous_homogeneous K e b hD a)).symm

private theorem polynomial_coe_homogeneous (f : P) (d : ℕ) (hf : f.IsHomogeneous d) : (f : R).IsHomogeneous d := by
  intro β hβ
  apply hf
  simpa only [MvPolynomial.coeff_coe] using hβ

/-- Every genuine homogeneous component remains inside the whole sheared
source initial ideal; no homogeneous-closure premise is input. -/
theorem sheared_source_initial_component_mem (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (F : R) (hF : F∈Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K))
    (q : ℕ) :
    MvPowerSeries.homogeneousComponent q F∈
      Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K) := by
  have hB : Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K)=Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex K =>
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex K a)) : R)) := by
    rw [←pivot_projection_strict_eq_sheared_source_initial K e b hD,projection_strict_eq_dehom_span]
  rw [hB] at hF ⊢
  obtain ⟨c,hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hF
  rw [←hc]
  change MvPowerSeries.homogeneousComponent q (∑ a∈c.support,c a*
    (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a)) : R))∈_
  rw [map_sum]
  apply Ideal.sum_mem
  intro a _
  have hh : (actualPointDehomogenization e b (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a)) : R).IsHomogeneous (normalExponentDegree a.val) :=
    polynomial_coe_homogeneous _ _ (canonical_source_dehomogeneous_homogeneous K e b hD a)
  by_cases ha : normalExponentDegree a.val≤q
  · rw [homogeneousComponent_mul_homogeneous_of_le q (normalExponentDegree a.val) _ _ hh ha]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a,rfl⟩)
  · rw [homogeneousComponent_mul_homogeneous_of_lt q (normalExponentDegree a.val) _ _ hh (lt_of_not_ge ha)]
    exact Ideal.zero_mem _

private theorem projection_component (e : Fin n) (q : ℕ) (F : R) :
    pivotZeroProjection e (MvPowerSeries.homogeneousComponent q F)=
      MvPowerSeries.homogeneousComponent q (pivotZeroProjection e F) := by
  apply MvPowerSeries.ext
  intro β
  simp only [pivotZeroProjection_coefficient,MvPowerSeries.coeff_homogeneousComponent]
  split_ifs <;> rfl

private theorem projected_current_initial_mem (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (q : ℕ) (F : R)
    (hF : F∈actualHomogeneousInitialIdeal (actualFormalStrictTransform K univ e (mem_univ e) b))
    (hHom : F.IsHomogeneous q) :
    pivotZeroProjection e F∈Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K) := by
  obtain ⟨L,hL,_hLq,hBand⟩ := actual_homogeneous_initial_ideal_degree_lift _ F hF q
  have hs : pivotZeroProjection e L∈Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K) := by
    rw [←pivot_projection_strict_eq_sheared_source_initial K e b hD]
    exact Ideal.mem_map_of_mem _ hL
  have hc := sheared_source_initial_component_mem K e b hD _ hs q
  rw [←projection_component,hBand,←MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hHom] at hc
  exact hc

private theorem homogeneous_of_X_factor (e : Fin n) (k : ℕ) (L G : R)
    (hLG : L=MvPowerSeries.X e*G) (hL : L.IsHomogeneous (k+1)) : G.IsHomogeneous k := by
  intro β hc
  have hcf : MvPowerSeries.coeff (Finsupp.single e 1+β) L≠0 := by
    rwa [hLG,MvPowerSeries.X,MvPowerSeries.coeff_add_monomial_mul,one_mul]
  have hdf : (Finsupp.single e 1+β).degree=k+1 := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hL hcf
  have he : (Finsupp.single e 1+β).degree=1+β.degree := by
    rw [map_add,Finsupp.degree_single]
  rw [he] at hdf
  have hβ : β.degree=k := by omega
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hβ

private theorem current_factor_projection_zero (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) (H : R)
    (hH : (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=
      actualFormalBlowup univ e b (actualReducedVertexSeries MonomialOrder.degLex K a))
    (q r : ℕ) (hqw : q<normalExponentDegree a.val) (hrq : r≤q) (hHq : H∈𝔪^q)
    (L : R) (hL : L∈actualHomogeneousInitialIdeal (actualFormalStrictTransform K univ e (mem_univ e) b))
    (hHom : L.IsHomogeneous (q-r))
    (hFactor : MvPowerSeries.homogeneousComponent q H=(MvPowerSeries.X e)^r*L) :
    pivotZeroProjection e L=0 := by
  have hProj := projected_current_initial_mem K e b hD (q-r) L hL hHom
  have hBand := projected_current_factor_eq_source_band e b (normalExponentDegree a.val)
    (actualReducedVertexSeries MonomialOrder.degLex K a) H (canonical_power K a) hH q r hrq L hFactor
  rw [hBand] at hProj ⊢
  by_cases hr : r=0
  · subst r
    rw [Nat.add_zero,Nat.sub_zero] at hBand hProj ⊢
    have hh := canonical_source_dehomogeneous_homogeneous K e b hD a
    have hz : MvPolynomial.homogeneousComponent q (actualPointDehomogenization e b
        (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
          (actualReducedVertexSeries MonomialOrder.degLex K a)))=0 := by
      apply MvPolynomial.ext
      intro β
      rw [MvPolynomial.coeff_homogeneousComponent]
      split_ifs with hβ
      · exact hh.coeff_eq_zero (by omega)
      · rfl
    rw [hz,MvPolynomial.coe_zero]
  · have hz := canonical_higher_dehomogeneous_band_eq_zero K a e b
      (normalExponentDegree a.val+r) (by omega) (q-r) (by omega)
      (dehom_band_coefficients_zero_of_current_power e b _ _ H (canonical_power K a) hH q r hHq hrq) hProj
    rw [hz,MvPolynomial.coe_zero]

private theorem current_factor_zero (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (hCol : ∀ q,((actualFormalStrictTransform K univ e (mem_univ e) b) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      actualFormalStrictTransform K univ e (mem_univ e) b ⊔ 𝔪^q)
    (a : actualInitialVertices MonomialOrder.degLex K) (H : R)
    (hH : (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=
      actualFormalBlowup univ e b (actualReducedVertexSeries MonomialOrder.degLex K a))
    (q : ℕ) (hqw : q<normalExponentDegree a.val) (hHq : H∈𝔪^q)
    (k r : ℕ) (hkr : r+k=q) (L : R)
    (hL : L∈actualHomogeneousInitialIdeal (actualFormalStrictTransform K univ e (mem_univ e) b))
    (hHom : L.IsHomogeneous k)
    (hFactor : MvPowerSeries.homogeneousComponent q H=(MvPowerSeries.X e)^r*L) : L=0 := by
  induction k generalizing r L with
  | zero =>
    have hp := current_factor_projection_zero K e b hD a H hH q r hqw (by omega) hHq L hL
      (by rw [show q-r=0 by omega];exact hHom) hFactor
    apply MvPowerSeries.ext
    intro β
    by_cases hβ : β.degree=0
    · have hz : β=0 := (Finsupp.degree_eq_zero_iff β).mp hβ
      subst β
      have hc := congrArg (MvPowerSeries.coeff (0 : Fin n →₀ ℕ)) hp
      simpa only [pivotZeroProjection_coefficient,Finsupp.zero_apply,ite_true,map_zero] using hc
    · exact hHom.coeff_eq_zero hβ
  | succ k ih =>
    have hp := current_factor_projection_zero K e b hD a H hH q r hqw (by omega) hHq L hL
      (by rw [show q-r=k+1 by omega];exact hHom) hFactor
    obtain ⟨G,hLG⟩ := (pivotZeroProjection_eq_zero_iff e L).mp hp
    have hG : G.IsHomogeneous k := homogeneous_of_X_factor e k L G hLG hHom
    have hGI : G∈actualHomogeneousInitialIdeal (actualFormalStrictTransform K univ e (mem_univ e) b) := by
      apply homogeneous_initial_pivot_cancel _ e hCol k G hG
      rwa [←hLG]
    have hFactor' : MvPowerSeries.homogeneousComponent q H=(MvPowerSeries.X e)^(r+1)*G := by
      rw [hFactor,hLG,pow_succ]
      ring
    have hz := ih (r+1) (by omega) G hGI hG hFactor'
    rw [hLG,hz,mul_zero]

/-- Whole actual current colons and natural source directional stability force
every SAME canonical normalized source member's original point order. -/
theorem canonical_directional_quotient_power_of_colons (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal K →
      (directionalPolynomialDerivative e b f : R)∈actualHomogeneousInitialIdeal K)
    (hCol : ∀ q,((actualFormalStrictTransform K univ e (mem_univ e) b) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      actualFormalStrictTransform K univ e (mem_univ e) b ⊔ 𝔪^q)
    (a : actualInitialVertices MonomialOrder.degLex K) (H : R)
    (hH : (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=
      actualFormalBlowup univ e b (actualReducedVertexSeries MonomialOrder.degLex K a)) :
    H∈𝔪^(normalExponentDegree a.val) := by
  by_contra hp
  have hne : H≠0 := by intro hz;apply hp;rw [hz];exact Ideal.zero_mem _
  let q := actualHomogeneousInitialDegree H hne
  have hHq : H∈𝔪^q := by
    rw [pointIdeal_eq_variables]
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q H).mpr
    intro β hβ
    apply MvPowerSeries.coeff_of_lt_order
    rw [←actualHomogeneousInitialDegree_eq_order H hne]
    exact_mod_cast (show β.degree<q from by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβ)
  have hqw : q<normalExponentDegree a.val := by
    by_contra h
    exact hp (Ideal.pow_le_pow_right (by omega) hHq)
  have hHJ : H∈actualFormalStrictTransform K univ e (mem_univ e) b := by
    rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    exact Ideal.subset_span ⟨normalExponentDegree a.val,actualReducedVertexSeries MonomialOrder.degLex K a,
      actualReducedVertexSeries_mem MonomialOrder.degLex K a,canonical_power K a,
      actualNormalizedFormalMember_unique univ e (mem_univ e) b _ _ (canonical_power K a) H hH⟩
  have hFJ := component_member_initial _ q H hHJ hHq
  have hz := current_factor_zero K e b hD hCol a H hH q hqw hHq q 0 (by omega)
    (MvPowerSeries.homogeneousComponent q H) hFJ (MvPowerSeries.isHomogeneous_homogeneousComponent H q) (by simp)
  change actualHomogeneousInitialForm H hne=0 at hz
  exact actualHomogeneousInitialForm_ne_zero H hne hz

open HolGerm HironakaHolomorphicPointJets HironakaActualAnalyticStrictGenerators
  HironakaActualCoefficientPresentationCentrePower HironakaActualAxisTaylorRigidity

/-- Actual original arbitrary-direction HS persistence supplies the genuine
current colons; only natural SOURCE directional stability is qualified here. -/
theorem original_directional_persistent_hs_orders_of_source_stable
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ)
    (hD : ∀ f : P,(f : R)∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) →
      (directionalPolynomialDerivative e b f : R)∈
        actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hPersist : ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e b) ℓ=hilbertSamuelValue I ℓ) :
    ∀ (a : actualInitialVertices MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) (H : R),
      (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=actualFormalBlowup univ e b
        (actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a) →
      H∈𝔪^(normalExponentDegree a.val) := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  obtain ⟨_H,_hN,hStrict⟩ := exists_actual_point_normalized_member_generators n I e b
  have hCurrent := original_point_persistent_hs_initial_colons I e b hPersist
  dsimp only at hCurrent
  have hCol : ∀ q,((actualFormalStrictTransform K univ e (mem_univ e) b) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      actualFormalStrictTransform K univ e (mem_univ e) b ⊔ 𝔪^q := by
    intro q
    have hc := (hCurrent q).2
    rw [hStrict] at hc
    exact hc
  intro a H hH
  exact canonical_directional_quotient_power_of_colons K e b hD hCol a H hH

end
end Hironaka.HironakaActualDirectionalPivotNormality
