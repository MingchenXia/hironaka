/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHomogeneousInitialHS

/-! Actual original and homogeneous vertex whole-jet bases constructed from genuine triangular coefficients. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFiniteJetVertexBasis
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalStandardMonomialHS HironakaActualHomogeneousInitialHS
variable {n : ℕ}

/-- The actual bounded original exponent family is genuinely finite. -/
instance actualFiniteJetExponentFintype (n q : ℕ) : Fintype (normalExponentIndex n q) :=
  normalExponentFintype n q

/-- The SAME actual whole formal jet quotient retains its existing complex action. -/
abbrev actualWholeFormalJet (n q : ℕ) := MvPowerSeries (Fin n) ℂ ⧸ genuineFormalVariables n ^ q

/-- Actual original standard-monomial quotient finiteness supplies the genuine whole jet's finite dimension internally. -/
instance actualWholeFormalJetFinite (n q : ℕ) : FiniteDimensional ℂ (actualWholeFormalJet n q) := by
  have h := finiteDimensional_formal_quotient_sup_variables_pow n q (⊥ : Ideal (MvPowerSeries (Fin n) ℂ))
  rw [bot_sup_eq] at h
  exact h

private theorem initialDiagram_bot (n : ℕ) :
    actualInitialDiagram MonomialOrder.degLex (⊥ : Ideal (MvPowerSeries (Fin n) ℂ))=∅ := by
  ext a
  simp only [Set.mem_empty_iff_false,iff_false]
  rintro ⟨F,hF,hne,_⟩
  exact hne (by simpa using hF)

private def zeroStandardIndexEquiv (n q : ℕ) :
    actualStandardIndex n (⊥ : Ideal (MvPowerSeries (Fin n) ℂ)) q ≃ normalExponentIndex n q where
  toFun := Subtype.val
  invFun := fun a => ⟨a,by rw [initialDiagram_bot]; simp⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The actual zero-ideal jet basis INTERNALLY proves the SAME genuine whole jet dimension. -/
theorem actualWholeFormalJet_finrank (n q : ℕ) :
    Module.finrank ℂ (actualWholeFormalJet n q)=Fintype.card (normalExponentIndex n q) := by
  let E : (actualStandardIndex n (⊥ : Ideal (MvPowerSeries (Fin n) ℂ)) q → ℂ) ≃ₗ[ℂ]
      actualWholeFormalJet n q := by
    have h := actualStandardQuotientLinearEquiv n (⊥ : Ideal (MvPowerSeries (Fin n) ℂ)) q
    rw [bot_sup_eq] at h
    exact h
  calc
    _=Module.finrank ℂ (actualStandardIndex n (⊥ : Ideal (MvPowerSeries (Fin n) ℂ)) q → ℂ) := E.finrank_eq.symm
    _=Fintype.card (actualStandardIndex n (⊥ : Ideal (MvPowerSeries (Fin n) ℂ)) q) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _=_ := Fintype.card_congr (zeroStandardIndexEquiv n q)

/-- The literal genuine finite series sum, with the original complex scalar action. -/
def actualTriangularJetLift (n q : ℕ) (V : normalExponentIndex n q → MvPowerSeries (Fin n) ℂ) :
    (normalExponentIndex n q → ℂ) →ₗ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun c := ∑ a, c a • V a
  map_add' c d := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]

/-- The actual finite series sum maps to the SAME genuine whole jet quotient. -/
def actualTriangularJetMap (n q : ℕ) (V : normalExponentIndex n q → MvPowerSeries (Fin n) ℂ) :
    (normalExponentIndex n q → ℂ) →ₗ[ℂ] actualWholeFormalJet n q :=
  (Ideal.Quotient.mkₐ ℂ (genuineFormalVariables n ^ q)).toLinearMap.comp (actualTriangularJetLift n q V)

private theorem triangular_jet_zero (q : ℕ) (V : normalExponentIndex n q → MvPowerSeries (Fin n) ℂ)
    (hV : ∀ a, MvPowerSeries.coeff a.val (V a)=1 ∧
      ∀ b, MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn a.val → MvPowerSeries.coeff b (V a)=0)
    (c : normalExponentIndex n q → ℂ) (hz : actualTriangularJetMap n q V c=0) : c=0 := by
  by_contra hne
  have hc : ∃ a, c a ≠ 0 := by
    by_contra h
    apply hne
    funext a
    exact not_not.mp (fun hca => h ⟨a,hca⟩)
  let S : Set (MonomialOrder.degLex (σ := Fin n)).syn :=
    {x | ∃ a : normalExponentIndex n q, c a ≠ 0 ∧ MonomialOrder.degLex.toSyn a.val=x}
  have hSN : S.Nonempty := by obtain ⟨a,ha⟩ := hc; exact ⟨_,a,ha,rfl⟩
  have hw : S.IsWF := Set.IsWF.of_wellFoundedLT S
  obtain ⟨a,hca,hax⟩ := hw.min_mem hSN
  have hmin (b : normalExponentIndex n q) (hb : c b ≠ 0) :
      MonomialOrder.degLex.toSyn a.val ≤ MonomialOrder.degLex.toSyn b.val := by
    rw [hax]
    exact hw.min_le hSN ⟨b,hb,rfl⟩
  have hcoeff : MvPowerSeries.coeff a.val (actualTriangularJetLift n q V c)=c a := by
    change MvPowerSeries.coeff a.val (∑ b : normalExponentIndex n q, c b • V b)=c a
    rw [map_sum]
    rw [Finset.sum_eq_single a]
    · rw [map_smul,(hV a).1,smul_eq_mul,mul_one]
    · intro b _ hba
      by_cases hb : c b=0
      · rw [hb,zero_smul,map_zero]
      · have hlt : MonomialOrder.degLex.toSyn a.val < MonomialOrder.degLex.toSyn b.val := by
          apply lt_of_le_of_ne (hmin b hb)
          intro he
          exact hba (Subtype.ext (MonomialOrder.degLex.toSyn.injective he)).symm
        rw [map_smul,(hV b).2 a.val hlt,smul_zero]
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  change Ideal.Quotient.mk (genuineFormalVariables n ^ q) (actualTriangularJetLift n q V c)=0 at hz
  have hpow := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hzero := (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hpow a.val a.property
  rw [hcoeff] at hzero
  exact hca hzero

/-- True bounded triangular coefficients internally prove actual whole-jet map injectivity. -/
theorem actualTriangularJetMap_injective (q : ℕ)
    (V : normalExponentIndex n q → MvPowerSeries (Fin n) ℂ)
    (hV : ∀ a, MvPowerSeries.coeff a.val (V a)=1 ∧
      ∀ b, MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn a.val → MvPowerSeries.coeff b (V a)=0) :
    Function.Injective (actualTriangularJetMap n q V) := by
  intro c d hcd
  have hz : actualTriangularJetMap n q V (c-d)=0 := by rw [map_sub,hcd,sub_self]
  exact sub_eq_zero.mp (triangular_jet_zero q V hV (c-d) hz)

/-- Actual whole-jet dimension and genuine injectivity internally construct the true complex linear inverse. -/
def actualTriangularJetEquiv (n q : ℕ)
    (V : normalExponentIndex n q → MvPowerSeries (Fin n) ℂ)
    (hV : ∀ a, MvPowerSeries.coeff a.val (V a)=1 ∧
      ∀ b, MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn a.val → MvPowerSeries.coeff b (V a)=0) :
    (normalExponentIndex n q → ℂ) ≃ₗ[ℂ] actualWholeFormalJet n q :=
  LinearEquiv.ofBijective (actualTriangularJetMap n q V)
    ⟨actualTriangularJetMap_injective q V hV,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [Module.finrank_fintype_fun_eq_card,actualWholeFormalJet_finrank])).mp
          (actualTriangularJetMap_injective q V hV)⟩

/-- The SAME genuine vertex series or its actual homogeneous initial form, with no supplied family. -/
def actualFiniteJetVertexSeries (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) : MvPowerSeries (Fin n) ℂ :=
  if useInitial then actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
    (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose
  else actualVertexSeries MonomialOrder.degLex I a

/-- Actual original coefficients and genuine homogeneous projection supply BOTH true monic vertex families internally. -/
theorem actualFiniteJetVertexSeries_spec (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) :
    ∃ hne : actualFiniteJetVertexSeries useInitial I a ≠ 0,
      actualInitialExponent MonomialOrder.degLex (actualFiniteJetVertexSeries useInitial I a) hne=a.val ∧
        MvPowerSeries.coeff a.val (actualFiniteJetVertexSeries useInitial I a)=1 := by
  cases useInitial
  · simpa only [actualFiniteJetVertexSeries,Bool.false_eq_true,if_false] using
      (actualVertexSeries_spec MonomialOrder.degLex I a).2
  · let F := actualVertexSeries MonomialOrder.degLex I a
    let hF := (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose
    have ha : actualInitialExponent MonomialOrder.degLex F hF=a.val :=
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose_spec.1
    change ∃ hne : actualHomogeneousInitialForm F hF ≠ 0,
      actualInitialExponent MonomialOrder.degLex (actualHomogeneousInitialForm F hF) hne=a.val ∧
        MvPowerSeries.coeff a.val (actualHomogeneousInitialForm F hF)=1
    refine ⟨actualHomogeneousInitialForm_ne_zero F hF,
      (actualHomogeneousInitialForm_initialExponent F hF).trans ha,?_⟩
    rw [actualHomogeneousInitialForm,MvPowerSeries.coeff_homogeneousComponent]
    have hd : Finsupp.degree a.val=actualHomogeneousInitialDegree F hF := by
      rw [actualHomogeneousInitialDegree,ha]
      simp only [Finsupp.degree_eq_sum,normalExponentDegree]
    rw [if_pos hd]
    exact actualVertexSeries_coefficient MonomialOrder.degLex I a

/-- The SAME actual division owner supplies a literal original or homogeneous vertex product, with genuine monomials outside the actual diagram. -/
def actualOwnedJetSeries (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (alpha : Fin n →₀ ℕ) : MvPowerSeries (Fin n) ℂ :=
  if h : alpha ∈ actualInitialDiagram MonomialOrder.degLex I then
    let a := Classical.choose (exists_actualDivisionOwner MonomialOrder.degLex I alpha h)
    MvPowerSeries.monomial (alpha-a.val) 1*actualFiniteJetVertexSeries useInitial I a
  else MvPowerSeries.monomial alpha 1

/-- Genuine actual owner inequalities and TRUE convolution internally give nonzero monic least exponents for BOTH whole-jet families. -/
theorem actualOwnedJetSeries_spec (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (alpha : Fin n →₀ ℕ) :
    ∃ hne : actualOwnedJetSeries useInitial I alpha ≠ 0,
      actualInitialExponent MonomialOrder.degLex (actualOwnedJetSeries useInitial I alpha) hne=alpha ∧
        MvPowerSeries.coeff alpha (actualOwnedJetSeries useInitial I alpha)=1 := by
  by_cases h : alpha ∈ actualInitialDiagram MonomialOrder.degLex I
  · rw [actualOwnedJetSeries,dif_pos h]
    dsimp only
    let a := Classical.choose (exists_actualDivisionOwner MonomialOrder.degLex I alpha h)
    have ha : a.val ≤ alpha := Classical.choose_spec (exists_actualDivisionOwner MonomialOrder.degLex I alpha h)
    have hsum : alpha-a.val+a.val=alpha := tsub_add_cancel_of_le ha
    obtain ⟨hne,hmin,hcoeff⟩ := actualFiniteJetVertexSeries_spec useInitial I a
    have hm := actualMonomial_ne_zero (alpha-a.val)
    refine ⟨mul_ne_zero hm hne,?_,?_⟩
    · rw [actualInitialExponent_mul MonomialOrder.degLex (MvPowerSeries.monomial (alpha-a.val) 1)
        (actualFiniteJetVertexSeries useInitial I a) hm hne,actualInitialExponent_monomial,hmin,hsum]
    · have hc := coeff_mul_actualInitialExponent MonomialOrder.degLex
        (MvPowerSeries.monomial (alpha-a.val) 1) (actualFiniteJetVertexSeries useInitial I a) hm hne
      rw [actualInitialExponent_monomial,hmin,hsum,MvPowerSeries.coeff_monomial_same,hcoeff,one_mul] at hc
      exact hc
  · rw [actualOwnedJetSeries,dif_neg h]
    exact ⟨actualMonomial_ne_zero alpha,actualInitialExponent_monomial MonomialOrder.degLex alpha,
      MvPowerSeries.coeff_monomial_same alpha 1⟩

/-- BOTH actual original and homogeneous families supply every true triangular coefficient condition internally. -/
theorem actualOwnedJetSeries_triangular (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (alpha : Fin n →₀ ℕ) :
    MvPowerSeries.coeff alpha (actualOwnedJetSeries useInitial I alpha)=1 ∧
      ∀ b, MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn alpha →
        MvPowerSeries.coeff b (actualOwnedJetSeries useInitial I alpha)=0 := by
  obtain ⟨hne,hmin,hcoeff⟩ := actualOwnedJetSeries_spec useInitial I alpha
  refine ⟨hcoeff,fun b hb => ?_⟩
  apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne b
  rwa [hmin]

/-- The ACTUAL original/initial vertex family gives a genuine whole-jet complex linear equivalence, with all triangular hypotheses internally proved. -/
def actualVertexWholeJetEquiv (n q : ℕ) (useInitial : Bool)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    (normalExponentIndex n q → ℂ) ≃ₗ[ℂ] actualWholeFormalJet n q :=
  actualTriangularJetEquiv n q (fun a => actualOwnedJetSeries useInitial I a.val)
    (fun a => actualOwnedJetSeries_triangular useInitial I a.val)

/-- A true coordinate unit vector retains exactly the SAME actual original/initial series class in the genuine whole quotient. -/
theorem actualVertexWholeJetEquiv_single (n q : ℕ) (useInitial : Bool)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : normalExponentIndex n q) :
    actualVertexWholeJetEquiv n q useInitial I (Pi.single a 1)=
      Ideal.Quotient.mk (genuineFormalVariables n ^ q) (actualOwnedJetSeries useInitial I a.val) := by
  change Ideal.Quotient.mk (genuineFormalVariables n ^ q)
    (∑ b : normalExponentIndex n q, (Pi.single a (1 : ℂ) : normalExponentIndex n q → ℂ) b • actualOwnedJetSeries useInitial I b.val)=_
  congr 1
  simp [Pi.single_apply]

/-- Both genuine finite actual vertex lists are actual bases of the SAME original complex whole-jet space. -/
def actualVertexWholeJetBasis (n q : ℕ) (useInitial : Bool)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Module.Basis (normalExponentIndex n q) ℂ (actualWholeFormalJet n q) :=
  (Pi.basisFun ℂ (normalExponentIndex n q)).map (actualVertexWholeJetEquiv n q useInitial I)

/-- The actual inverse for the original family and genuine homogeneous forward map give a TRUE complex LINEAR whole-jet comparison. -/
def actualVertexJetInitialComparison (n q : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualWholeFormalJet n q ≃ₗ[ℂ] actualWholeFormalJet n q :=
  (actualVertexWholeJetEquiv n q false I).symm.trans (actualVertexWholeJetEquiv n q true I)

/-- Every actual original jet generator is sent to the SAME indexed genuine homogeneous initial jet generator. -/
theorem actualVertexJetInitialComparison_generator (n q : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : normalExponentIndex n q) :
    actualVertexJetInitialComparison n q I
      (Ideal.Quotient.mk (genuineFormalVariables n ^ q) (actualOwnedJetSeries false I a.val))=
        Ideal.Quotient.mk (genuineFormalVariables n ^ q) (actualOwnedJetSeries true I a.val) := by
  rw [← actualVertexWholeJetEquiv_single n q false I a]
  change actualVertexWholeJetEquiv n q true I
    ((actualVertexWholeJetEquiv n q false I).symm (actualVertexWholeJetEquiv n q false I (Pi.single a 1)))=_
  rw [LinearEquiv.symm_apply_apply,actualVertexWholeJetEquiv_single]

/-- Genuine finite Taylor truncation of a factor preserves the SAME actual monomial-times-series whole jet class. -/
theorem actualWholeFormalJet_monomial_truncation (n q : ℕ) (beta : Fin n →₀ ℕ)
    (F : MvPowerSeries (Fin n) ℂ) :
    Ideal.Quotient.mk (genuineFormalVariables n ^ q) (MvPowerSeries.monomial beta 1*F)=
      Ideal.Quotient.mk (genuineFormalVariables n ^ q)
        (MvPowerSeries.monomial beta 1*(MvPowerSeries.truncTotal (q-normalExponentDegree beta) F :
          MvPowerSeries (Fin n) ℂ)) := by
  let d := normalExponentDegree beta
  have hM : MvPowerSeries.monomial beta (1 : ℂ) ∈ genuineFormalVariables n ^ d := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n d _).mpr
    intro a ha
    by_cases he : a=beta
    · subst a; dsimp only [d] at ha; omega
    · simp [MvPowerSeries.coeff_monomial,he]
  have hR : F-(MvPowerSeries.truncTotal (q-d) F : MvPowerSeries (Fin n) ℂ) ∈
      genuineFormalVariables n ^ (q-d) := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q-d) _).mpr
    intro a ha
    have ht : MvPolynomial.coeff a (MvPowerSeries.truncTotal (q-d) F)=MvPowerSeries.coeff a F :=
      MvPowerSeries.coeff_truncTotal F (by
        simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using ha)
    rw [map_sub,MvPolynomial.coeff_coe,ht,sub_self]
  have hp := Ideal.mul_mem_mul hM hR
  rw [← pow_add] at hp
  have hq : q ≤ d+(q-d) := by omega
  have hp' := (Ideal.pow_le_pow_right hq) hp
  apply Ideal.Quotient.eq.mpr
  rw [← mul_sub]
  exact hp'

end
end Hironaka.HironakaActualFiniteJetVertexBasis
