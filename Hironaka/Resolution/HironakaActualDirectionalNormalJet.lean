/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualInitialPivotNormality
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Genuine directional source-normal chart-jet independence

The literal polynomial direction v_e=1,v_i=b_i differentiates every actual
source-diagram-normal polynomial to another source-normal polynomial.
Genuine Euler and actual dehomogenization give an exact coefficient formula.
A finite homogeneous-degree induction proves that the first chart band of a
source-normal polynomial cannot be a nonzero member of the entire sheared
source initial ideal. Canonical higher source bands supply normality internally.
No old/current diagram inclusion or output-order certificate is used.
Current quotient-band extraction and the full arbitrary-direction HS converse
remain separate consumers.
Blueprint: `hironaka-actual-directional-normal-jet-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualDirectionalNormalJet
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualPointDehomogenizedInitial HironakaActualPointOrderRetainingHS
  HironakaActualFormalBlowupAllDirections HironakaActualHomogeneousInitialHS
  HironakaActualPointExceptionalInitialForm HironakaRelativeNormalMonomialBasis
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
local notation "R" => MvPowerSeries (Fin n) ℂ

def directionalPolynomialDerivative (e : Fin n) (b : Fin n → ℂ) (f : P) : P :=
  ∑ i : Fin n,MvPolynomial.C (if i=e then 1 else b i)*MvPolynomial.pderiv i f

theorem directional_derivative_normal (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (f : P) (hNormal : ∀ β∈actualInitialDiagram MonomialOrder.degLex K,MvPolynomial.coeff β f=0) :
    ∀ β∈actualInitialDiagram MonomialOrder.degLex K,
      MvPolynomial.coeff β (directionalPolynomialDerivative e b f)=0 := by
  intro β hβ
  rw [directionalPolynomialDerivative,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_pderiv]
  have h := actualInitialDiagram_add MonomialOrder.degLex K β (Finsupp.single i 1) hβ
  rw [hNormal _ (by simpa only [add_comm] using h),zero_mul,mul_zero]

private theorem pderiv_dehom (e i : Fin n) (b : Fin n → ℂ) (f : P) :
    MvPolynomial.pderiv i (actualPointDehomogenization e b f)=
      if i=e then 0 else actualPointDehomogenization e b (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [actualPointDehomogenization]
  | add f g hf hg => simp only [map_add,hf,hg];split_ifs <;> simp
  | mul_X f j hf =>
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,actualPointDehomogenization,MvPolynomial.aeval_X,
      map_add,MvPolynomial.pderiv_X,Pi.single_apply] at hf ⊢
    by_cases hi : i=e <;> by_cases hj : j=e <;> by_cases hij : j=i <;>
      simp_all [map_zero,map_one]

private theorem euler_coefficient (f : P) (β : Fin n →₀ ℕ) :
    MvPolynomial.coeff β (∑ i : Fin n,MvPolynomial.X i*MvPolynomial.pderiv i f)=
      (β.degree : ℂ)*MvPolynomial.coeff β f := by
  rw [MvPolynomial.coeff_sum]
  have hterm (i : Fin n) :
      MvPolynomial.coeff β (MvPolynomial.X i*MvPolynomial.pderiv i f)=
        (β i : ℂ)*MvPolynomial.coeff β f := by
    by_cases hi : β i=0
    · rw [MvPolynomial.coeff_X_mul',if_neg (by simpa using hi)]
      simp [hi]
    · rw [MvPolynomial.coeff_X_mul',if_pos (Finsupp.mem_support_iff.mpr hi),MvPolynomial.coeff_pderiv,
        Finsupp.sub_add_single_one_cancel hi]
      have he : ((β-Finsupp.single i 1 : Fin n →₀ ℕ) i)+1=β i := by simp only [Finsupp.tsub_apply,Finsupp.single_eq_same];omega
      rw [←Nat.cast_add_one,he,mul_comm]
  simp_rw [hterm]
  rw [←Finset.sum_mul,←Nat.cast_sum]
  congr 1
  simp [Finsupp.degree_eq_weight_one,Finsupp.weight_apply,Finsupp.sum_fintype]

private theorem dehom_directional_euler (e : Fin n) (b : Fin n → ℂ)
    (f : P) (d : ℕ) (hf : f.IsHomogeneous d) :
    actualPointDehomogenization e b (directionalPolynomialDerivative e b f)+
      (∑ i : Fin n,MvPolynomial.X i*MvPolynomial.pderiv i (actualPointDehomogenization e b f))=
      d • actualPointDehomogenization e b f := by
  have h := congrArg (actualPointDehomogenization e b) hf.sum_X_mul_pderiv
  simp only [map_sum,map_mul,map_nsmul] at h
  rw [directionalPolynomialDerivative,map_sum,←Finset.sum_add_distrib]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,show actualPointDehomogenization e b (MvPolynomial.C (if i=e then 1 else b i))=
      MvPolynomial.C (if i=e then 1 else b i) from (actualPointDehomogenization e b).commutes _,pderiv_dehom]
  by_cases hi : i=e
  · simp [actualPointDehomogenization,hi]
  · simp only [actualPointDehomogenization,MvPolynomial.aeval_X,if_neg hi]
    ring

theorem dehom_directional_derivative_coefficient (e : Fin n) (b : Fin n → ℂ)
    (f : P) (d : ℕ) (hf : f.IsHomogeneous d) (β : Fin n →₀ ℕ) :
    MvPolynomial.coeff β (actualPointDehomogenization e b (directionalPolynomialDerivative e b f))=
      ((d : ℂ)-(β.degree : ℂ))*MvPolynomial.coeff β (actualPointDehomogenization e b f) := by
  have h := congrArg (MvPolynomial.coeff β) (dehom_directional_euler e b f d hf)
  simp only [MvPolynomial.coeff_add,euler_coefficient] at h
  have hc : MvPolynomial.coeff β (d • actualPointDehomogenization e b f)=
      (d : ℂ)*MvPolynomial.coeff β (actualPointDehomogenization e b f) := by
    rw [nsmul_eq_mul]
    exact MvPolynomial.coeff_C_mul _ _ _
  rw [hc] at h
  linear_combination h

private theorem dehom_totalDegree_le (e : Fin n) (b : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    (actualPointDehomogenization e b f).totalDegree≤f.totalDegree := by
  have hlin (i : Fin n) :
      (if i=e then (1 : MvPolynomial (Fin n) ℂ) else MvPolynomial.C (b i)+MvPolynomial.X i).totalDegree≤1 := by
    split_ifs
    · simp
    · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  conv_lhs => rw [←f.support_sum_monomial_coeff,map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α hα
  change (MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i)
    (MvPolynomial.monomial α (MvPolynomial.coeff α f))).totalDegree≤_
  rw [MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  change (MvPolynomial.C (MvPolynomial.coeff α f)).totalDegree+_≤_
  rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (by simpa using Nat.mul_le_mul_left (α i) (hlin i))))
  exact MvPolynomial.le_totalDegree hα


theorem directional_derivative_homogeneous (e : Fin n) (b : Fin n → ℂ)
    (f : P) (d : ℕ) (hf : f.IsHomogeneous d) :
    (directionalPolynomialDerivative e b f).IsHomogeneous (d-1) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact hf.pderiv.C_mul _

private theorem low_zero_homogeneous (f : P) (k : ℕ)
    (hBound : f.totalDegree≤k)
    (hLow : ∀ β : Fin n →₀ ℕ,β.degree<k → MvPolynomial.coeff β f=0) :
    f.IsHomogeneous k := by
  intro β hβ
  have hUp := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hβ)).trans hBound
  have hDn : k≤β.degree := by
    by_contra h
    exact hβ (hLow β (by omega))
  change (Finsupp.weight (fun _ : Fin n => (1 : ℕ))) β=k
  rw [←Finsupp.degree_eq_weight_one]
  exact le_antisymm hUp hDn

private theorem derivative_band (e : Fin n) (b : Fin n → ℂ)
    (f : P) (d : ℕ) (hf : f.IsHomogeneous d) (k : ℕ) :
    MvPolynomial.homogeneousComponent k (actualPointDehomogenization e b (directionalPolynomialDerivative e b f))=
      ((d : ℂ)-(k : ℂ)) • MvPolynomial.homogeneousComponent k (actualPointDehomogenization e b f) := by
  apply MvPolynomial.ext
  intro β
  simp only [MvPolynomial.coeff_homogeneousComponent,MvPolynomial.coeff_smul]
  split_ifs with hβ
  · rw [dehom_directional_derivative_coefficient e b f d hf β,hβ]
    rfl
  · simp

/-- A genuine first chart band of a source-normal homogeneous polynomial is
independent of the ENTIRE sheared source initial ideal. -/
theorem first_dehomogeneous_normal_band_eq_zero (K : Ideal R) (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (f : P) (hf : f.IsHomogeneous d)
    (hNormal : ∀ β∈actualInitialDiagram MonomialOrder.degLex K,MvPolynomial.coeff β f=0)
    (k : ℕ) (hkd : k≤d)
    (hLow : ∀ β : Fin n →₀ ℕ,β.degree<k → MvPolynomial.coeff β (actualPointDehomogenization e b f)=0)
    (hMem : (MvPolynomial.homogeneousComponent k (actualPointDehomogenization e b f) : R)∈
      Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K)) :
    MvPolynomial.homogeneousComponent k (actualPointDehomogenization e b f)=0 := by
  induction d using Nat.strong_induction_on generalizing f k with
  | h d ih =>
    by_cases hdk : d=k
    · subst d
      have hfh : (actualPointDehomogenization e b f).IsHomogeneous k :=
        low_zero_homogeneous _ k ((dehom_totalDegree_le e b f).trans hf.totalDegree_le) hLow
      rw [MvPolynomial.homogeneousComponent_eq_self hfh] at hMem ⊢
      have hShear := centerShear_eq_dehom_of_homogeneous_dehom e b f k hf hfh
      rw [←hShear] at hMem
      have hSource : (f : R)∈actualHomogeneousInitialIdeal K :=
        (Ideal.apply_mem_of_equiv_iff (f := (actualFormalCenterShearAlgEquiv univ e b).toRingEquiv)).mp hMem
      have hz : (f : R)=0 := by
        apply eq_zero_of_mem_of_diagram_coefficients_zero MonomialOrder.degLex (actualHomogeneousInitialIdeal K) _ hSource
        intro β hβ
        rw [actual_homogeneous_initial_ideal_diagram] at hβ
        rw [MvPolynomial.coeff_coe]
        exact hNormal β hβ
      have hpoly : f=0 := (MvPolynomial.coe_injective (Fin n) ℂ) (by simpa only [MvPolynomial.coe_zero] using hz)
      rw [hpoly,map_zero]
    · have hLess : d-1<d := by omega
      have hkd' : k≤d-1 := by omega
      have hDh : (directionalPolynomialDerivative e b f).IsHomogeneous (d-1) := directional_derivative_homogeneous e b f d hf
      have hDN := directional_derivative_normal K e b f hNormal
      have hDL (β : Fin n →₀ ℕ) (hβ : β.degree<k) :
          MvPolynomial.coeff β (actualPointDehomogenization e b (directionalPolynomialDerivative e b f))=0 := by
        rw [dehom_directional_derivative_coefficient e b f d hf β,hLow β hβ,mul_zero]
      have hDB := derivative_band e b f d hf k
      have hDM : (MvPolynomial.homogeneousComponent k
          (actualPointDehomogenization e b (directionalPolynomialDerivative e b f)) : R)∈
          Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K) := by
        rw [hDB,MvPolynomial.coe_smul,Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hMem
      have hz := ih (d-1) hLess (directionalPolynomialDerivative e b f) hDh hDN k hkd' hDL hDM
      rw [hDB] at hz
      have hn : (d : ℂ)-(k : ℂ)≠0 := by
        intro he
        have hc : (d : ℂ)=(k : ℂ) := sub_eq_zero.mp he
        have hd : d=k := by exact_mod_cast hc
        exact hdk hd
      exact (smul_eq_zero.mp hz).resolve_left hn

/-- Canonical higher homogeneous source bands provide the normal input
internally for the SAME reduced source family. -/
theorem canonical_higher_dehomogeneous_band_eq_zero (K : Ideal R)
    (a : actualInitialVertices MonomialOrder.degLex K) (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (hHigh : normalExponentDegree a.val<d)
    (k : ℕ) (hkd : k≤d)
    (hLow : ∀ β : Fin n →₀ ℕ,β.degree<k → MvPolynomial.coeff β
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d
        (actualReducedVertexSeries MonomialOrder.degLex K a)))=0)
    (hMem : (MvPolynomial.homogeneousComponent k
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d
        (actualReducedVertexSeries MonomialOrder.degLex K a))) : R)∈
      Ideal.map (actualFormalCenterShear univ e b).toRingHom (actualHomogeneousInitialIdeal K)) :
    MvPolynomial.homogeneousComponent k
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d
        (actualReducedVertexSeries MonomialOrder.degLex K a)))=0 := by
  apply first_dehomogeneous_normal_band_eq_zero K e b d _
    (actualPointHomogeneousPolynomial_isHomogeneous _ _) _ k hkd hLow hMem
  intro β hβ
  have hc := congrArg (MvPowerSeries.coeff β) (actualPointHomogeneousPolynomial_coe d
    (actualReducedVertexSeries MonomialOrder.degLex K a))
  simp only [MvPolynomial.coeff_coe,MvPowerSeries.coeff_homogeneousComponent] at hc
  rw [hc]
  split_ifs with hd
  · rw [actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a β hβ]
    apply if_neg
    intro he
    subst β
    have hdeg : normalExponentDegree a.val=d := by
      simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hd
    omega
  · rfl

end
end Hironaka.HironakaActualDirectionalNormalJet

