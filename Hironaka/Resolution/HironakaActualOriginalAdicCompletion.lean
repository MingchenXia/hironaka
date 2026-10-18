/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalIdealContraction
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! Genuine original polynomial jet rings and the maximal-adic completion. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualOriginalAdicCompletion
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction

/-- The whole original polynomial preimage of every genuine maximal-ideal power. -/
theorem originalPolynomial_mem_maximal_pow_iff (n q : ℕ)
    (P : MvPolynomial (Fin n) ℂ) :
    originalPolynomialEval n P ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q ↔
      P ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ q := by
  rw [mem_original_maximal_pow_iff_formal_coefficients_zero,
    MvPolynomial.mem_pow_idealOfVars_iff']
  simp only [originalTaylorAlgHom_polynomialEval,MvPolynomial.coeff_coe,
    normalExponentDegree,Finsupp.degree_eq_sum]

/-- Evaluation of the actual original coordinate germs on the entire polynomial jet quotient. -/
def originalPolynomialJetHom (n q : ℕ) :
    (MvPolynomial (Fin n) ℂ ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ q) →+*
      (HolGerm (ComplexModel (0+n)) ⧸
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (originalPolynomialEval n).toRingHom)
    (fun P hP => Ideal.Quotient.eq_zero_iff_mem.mpr
      ((originalPolynomial_mem_maximal_pow_iff n q P).mpr hP))

/-- Every actual original whole jet class has a genuine polynomial representative. -/
theorem originalPolynomialJetHom_bijective (n q : ℕ) :
    Function.Bijective (originalPolynomialJetHom n q) := by
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (originalPolynomial_mem_maximal_pow_iff n q P).mp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  · intro x
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective x
    cases q with
    | zero =>
      refine ⟨0,?_⟩
      rw [map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)).symm
    | succ k =>
      refine ⟨Ideal.Quotient.mk _ (originalTaylorPolynomial n k g),?_⟩
      exact originalTaylorPolynomial_quotient_class n k g

/-- This is an isomorphism of the whole actual local jet rings, not just their dimensions. -/
def originalPolynomialJetEquiv (n q : ℕ) :
    (MvPolynomial (Fin n) ℂ ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ q) ≃+*
      (HolGerm (ComplexModel (0+n)) ⧸
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) :=
  RingEquiv.ofBijective (originalPolynomialJetHom n q) (originalPolynomialJetHom_bijective n q)

/-- Every power-reduction square commutes on the same original evaluated polynomial. -/
theorem originalPolynomialJetEquiv_transition (n : ℕ) {p q : ℕ} (hpq : p ≤ q)
    (x : MvPolynomial (Fin n) ℂ ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ q) :
    Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) hpq
      (originalPolynomialJetEquiv n q x) =
      originalPolynomialJetEquiv n p
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin n) ℂ) hpq x) := by
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem actualCompletion_reduction {R : Type*} [CommRing R] (I : Ideal R)
    {p q : ℕ} (hpq : p ≤ q) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hpq (AdicCompletion.evalₐ I q x)=
      AdicCompletion.evalₐ I p x := by
  obtain ⟨a,rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk,AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I^p) (a q)=Ideal.Quotient.mk (I^p) (a p)
  apply Ideal.Quotient.eq.mpr
  simpa only [smul_eq_mul,Ideal.mul_top] using (SModEq.sub_mem.mp (a.property hpq).symm)

private theorem actualPolynomialCompletion_compatible (n : ℕ) {p q : ℕ} (hpq : p ≤ q) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) hpq).comp
      ((originalPolynomialJetEquiv n q).toRingHom.comp
        (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin n) ℂ) q).toRingHom)=
      (originalPolynomialJetEquiv n p).toRingHom.comp
        (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin n) ℂ) p).toRingHom := by
  ext x
  exact (originalPolynomialJetEquiv_transition n hpq _).trans
    (congrArg (originalPolynomialJetEquiv n p) (actualCompletion_reduction _ hpq x))

private theorem actualOriginalCompletion_compatible (n : ℕ) {p q : ℕ} (hpq : p ≤ q) :
    (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin n) ℂ) hpq).comp
      ((originalPolynomialJetEquiv n q).symm.toRingHom.comp
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) q).toRingHom)=
      (originalPolynomialJetEquiv n p).symm.toRingHom.comp
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) p).toRingHom := by
  ext x
  simp only [RingHom.comp_apply]
  apply (originalPolynomialJetEquiv n p).injective
  change originalPolynomialJetEquiv n p
    (Ideal.Quotient.factorPow _ hpq ((originalPolynomialJetEquiv n q).symm
      (AdicCompletion.evalₐ _ q x))) =
    originalPolynomialJetEquiv n p ((originalPolynomialJetEquiv n p).symm
      (AdicCompletion.evalₐ _ p x))
  rw [← originalPolynomialJetEquiv_transition n hpq]
  rw [RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  exact actualCompletion_reduction _ hpq x

/-- Actual original evaluation on all coherent polynomial quotient families. -/
def actualPolynomialCompletionHom (n : ℕ) :
    AdicCompletion (MvPolynomial.idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) →+*
      AdicCompletion (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))))
        (HolGerm (ComplexModel (0+n))) :=
  AdicCompletion.liftRingHom _
    (fun q => (originalPolynomialJetEquiv n q).toRingHom.comp
      (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin n) ℂ) q).toRingHom)
    (actualPolynomialCompletion_compatible n)

/-- The genuine inverse system map uses the inverse whole jet isomorphism at EVERY power. -/
def actualOriginalToPolynomialCompletionHom (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))))
        (HolGerm (ComplexModel (0+n))) →+*
      AdicCompletion (MvPolynomial.idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  AdicCompletion.liftRingHom _
    (fun q => (originalPolynomialJetEquiv n q).symm.toRingHom.comp
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) q).toRingHom)
    (actualOriginalCompletion_compatible n)

private theorem eval_actualPolynomialCompletionHom (n q : ℕ)
    (x : AdicCompletion (MvPolynomial.idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)) :
    AdicCompletion.evalₐ _ q (actualPolynomialCompletionHom n x)=
      originalPolynomialJetEquiv n q (AdicCompletion.evalₐ _ q x) := by
  exact AdicCompletion.evalₐ_liftRingHom _ _ (actualPolynomialCompletion_compatible n) q x

private theorem eval_actualOriginalToPolynomialCompletionHom (n q : ℕ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))))
      (HolGerm (ComplexModel (0+n)))) :
    AdicCompletion.evalₐ _ q (actualOriginalToPolynomialCompletionHom n x)=
      (originalPolynomialJetEquiv n q).symm (AdicCompletion.evalₐ _ q x) := by
  exact AdicCompletion.evalₐ_liftRingHom _ _ (actualOriginalCompletion_compatible n) q x

/-- The entire genuine polynomial and original germ completions are isomorphic as rings. -/
def actualPolynomialCompletionEquiv (n : ℕ) :
    AdicCompletion (MvPolynomial.idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))))
        (HolGerm (ComplexModel (0+n))) where
  __ := actualPolynomialCompletionHom n
  invFun := actualOriginalToPolynomialCompletionHom n
  left_inv x := by
    change actualOriginalToPolynomialCompletionHom n (actualPolynomialCompletionHom n x)=x
    apply AdicCompletion.ext_evalₐ
    intro q
    rw [eval_actualOriginalToPolynomialCompletionHom,eval_actualPolynomialCompletionHom,
      RingEquiv.symm_apply_apply]
  right_inv x := by
    change actualPolynomialCompletionHom n (actualOriginalToPolynomialCompletionHom n x)=x
    apply AdicCompletion.ext_evalₐ
    intro q
    rw [eval_actualPolynomialCompletionHom,eval_actualOriginalToPolynomialCompletionHom,
      RingEquiv.apply_symm_apply]

/-- Internally identify the completion of the ACTUAL original analytic local ring with formal series. -/
def actualOriginalCompletionEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))))
        (HolGerm (ComplexModel (0+n))) ≃+* MvPowerSeries (Fin n) ℂ :=
  (actualPolynomialCompletionEquiv n).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).symm.toRingEquiv

private theorem actualTaylor_truncTotal (n k : ℕ) (g : HolGerm (ComplexModel (0+n))) :
    MvPowerSeries.truncTotal (k+1) (originalTaylorAlgHom n g)=originalTaylorPolynomial n k g := by
  ext α
  by_cases hα : normalExponentDegree α < k+1
  · rw [MvPowerSeries.coeff_truncTotal _ (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα),
      originalTaylorAlgHom_coefficient,originalTaylorCoefficientMap_eq_coefficient n k g α hα]
  · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by
        simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using Nat.le_of_not_gt hα),
      originalTaylorPolynomial_coefficient_high n k g α (Nat.le_of_not_gt hα)]

/-- The completion isomorphism retains the SAME genuine Taylor series of EVERY original germ. -/
theorem actualOriginalCompletionEquiv_of (n : ℕ) (g : HolGerm (ComplexModel (0+n))) :
    actualOriginalCompletionEquiv n
      (AdicCompletion.of (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) _ g)=
        originalTaylorAlgHom n g := by
  change (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).symm
    ((actualPolynomialCompletionEquiv n).symm
      (AdicCompletion.of (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) _ g))=_
  apply (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).injective
  rw [AlgEquiv.apply_symm_apply]
  apply (actualPolynomialCompletionEquiv n).injective
  rw [RingEquiv.apply_symm_apply]
  apply AdicCompletion.ext_evalₐ
  intro q
  change AdicCompletion.evalₐ _ q
    (AdicCompletion.of (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) _ g)=
      AdicCompletion.evalₐ _ q (actualPolynomialCompletionHom n
        (MvPowerSeries.toAdicCompletion (Fin n) ℂ (originalTaylorAlgHom n g)))
  rw [AdicCompletion.evalₐ_of]
  rw [eval_actualPolynomialCompletionHom]
  change Ideal.Quotient.mk _ g=originalPolynomialJetEquiv n q
    (Ideal.Quotient.mk _ (MvPowerSeries.truncTotal q (originalTaylorAlgHom n g)))
  cases q with
  | zero =>
    exact Ideal.Quotient.eq.mpr (by simp)
  | succ k =>
    rw [actualTaylor_truncTotal]
    exact (originalTaylorPolynomial_quotient_class n k g).symm

end
end Hironaka.HironakaActualOriginalAdicCompletion
