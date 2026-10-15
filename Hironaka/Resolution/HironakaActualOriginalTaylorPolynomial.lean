/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualWholeIdealJetDetection
import Hironaka.Resolution.HironakaRelativeNormalActualBaseJetDimension

/-! Canonical original complex polynomial representatives, before formal-series algebra. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalTaylorPolynomial
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualBaseJetDimension HironakaActualWholeIdealJetDetection

/-- Genuine complex polynomial evaluation at the SAME actual original coordinate germs. -/
def originalPolynomialEval (n : ℕ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] HolGerm (ComplexModel (0+n)) :=
  MvPolynomial.aeval (normalCoordinate 0 n)

/-- Literal original coefficients and coordinate powers are retained by the actual evaluation. -/
theorem originalPolynomialEval_monomial (n : ℕ) (α : Fin n →₀ ℕ) (c : ℂ) :
    originalPolynomialEval n (MvPolynomial.monomial α c)=
      HolGerm.constHom c * normalExponentMonomial 0 n α := by
  rw [originalPolynomialEval,MvPolynomial.aeval_monomial]
  change HolGerm.constHom c * α.prod (fun i k => normalCoordinate 0 n i ^ k)=_
  exact congrArg (fun z => HolGerm.constHom c*z)
    (α.prod_fintype (fun i k => normalCoordinate 0 n i ^ k) (fun _ => pow_zero _))

/-- The actual zero-base coefficient lift has precisely the original complex polynomial values. -/
theorem normalPolynomialEval_original_coefficient_lift (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    normalPolynomialEval 0 n (P.map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0)))=
      originalPolynomialEval n P := by
  let := tangentAlgebra 0 n
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.map_C,normalPolynomialEval,MvPolynomial.aeval_C,
      originalPolynomialEval,MvPolynomial.aeval_C]
    rfl
  | add P Q hP hQ => rw [map_add,map_add,map_add,hP,hQ]
  | mul_X P i hP =>
    rw [map_mul,MvPolynomial.map_X,map_mul,map_mul,hP]
    simp only [normalPolynomialEval,originalPolynomialEval,MvPolynomial.aeval_X]

/-- Actual original polynomial membership in a true maximal power annihilates EVERY lower coefficient. -/
theorem originalPolynomial_coefficient_eq_zero_of_eval_mem (n q : ℕ)
    (P : MvPolynomial (Fin n) ℂ) (α : Fin n →₀ ℕ) (hα : normalExponentDegree α < q)
    (hP : originalPolynomialEval n P ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) :
    MvPolynomial.coeff α P=0 := by
  have hp : normalPolynomialEval 0 n (P.map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0))) ∈
      normalIdeal 0 n ^ q := by
    rw [normalPolynomialEval_original_coefficient_lift,zeroTangentNormalIdeal_eq_maximalIdeal]
    exact hP
  have hc := coefficient_eq_zero_of_normalPolynomialEval_mem 0 n q _ α hα hp
  rw [MvPolynomial.coeff_map] at hc
  have he := congrArg HolGerm.eval hc
  simpa only [map_zero,HolGerm.eval_constHom] using he

/-- True original quotient coordinates, with the original constant-germ complex scalar action. -/
def originalJetCoordinates (n k : ℕ) : HolGerm (ComplexModel (0+n)) →ₗ[ℂ]
    (normalExponentIndex n (k+1) → ℂ) :=
  (actualZeroTangentJetComplexEquiv n k).symm.toLinearMap.comp
    (Ideal.Quotient.mkₐ ℂ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1))).toLinearMap

/-- The internally constructed actual finite original complex Taylor polynomial. -/
def originalTaylorPolynomial (n k : ℕ) (g : HolGerm (ComplexModel (0+n))) : MvPolynomial (Fin n) ℂ :=
  let := normalExponentFintype n (k+1)
  ∑ α : normalExponentIndex n (k+1), MvPolynomial.monomial α.val (originalJetCoordinates n k g α)

/-- Every genuine lower coefficient is precisely its actual original quotient coordinate. -/
theorem originalTaylorPolynomial_coefficient_low (n k : ℕ) (g : HolGerm (ComplexModel (0+n)))
    (α : Fin n →₀ ℕ) (hα : normalExponentDegree α < k+1) :
    MvPolynomial.coeff α (originalTaylorPolynomial n k g)=originalJetCoordinates n k g ⟨α,hα⟩ := by
  classical
  let := normalExponentFintype n (k+1)
  have he (β : normalExponentIndex n (k+1)) : β.val=α ↔ β=⟨α,hα⟩ := by
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg Subtype.val h
  simp [originalTaylorPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,he]

/-- The actual original polynomial has no coefficient beyond the TRUE degree bound. -/
theorem originalTaylorPolynomial_coefficient_high (n k : ℕ) (g : HolGerm (ComplexModel (0+n)))
    (α : Fin n →₀ ℕ) (hα : k+1 ≤ normalExponentDegree α) :
    MvPolynomial.coeff α (originalTaylorPolynomial n k g)=0 := by
  classical
  let := normalExponentFintype n (k+1)
  have he (β : normalExponentIndex n (k+1)) : β.val ≠ α := by
    intro he
    have := β.property
    rw [he] at this
    omega
  simp [originalTaylorPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,he]

/-- The actual evaluation has the SAME genuine entire quotient class as the original numerator. -/
theorem originalTaylorPolynomial_quotient_class (n k : ℕ) (g : HolGerm (ComplexModel (0+n))) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1))
      (originalPolynomialEval n (originalTaylorPolynomial n k g))=
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1)) g := by
  classical
  let := normalExponentFintype n (k+1)
  let c := originalJetCoordinates n k g
  have hc : c=∑ α : normalExponentIndex n (k+1), c α • Pi.single α 1 := by
    ext β
    simp [Pi.single_apply]
  have he := (actualZeroTangentJetComplexEquiv n k).apply_symm_apply
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1)) g)
  change actualZeroTangentJetComplexEquiv n k c=_ at he
  rw [hc,map_sum] at he
  rw [originalTaylorPolynomial,map_sum,map_sum]
  rw [← he]
  apply Finset.sum_congr rfl
  intro α _
  rw [map_smul,actualZeroTangentJetComplexEquiv_single,originalPolynomialEval_monomial]
  change Ideal.Quotient.mk _ (HolGerm.constHom (c α)*normalExponentMonomial 0 n α.val)=_
  exact ((Ideal.Quotient.mkₐ ℂ _).toLinearMap.map_smul (c α) (normalExponentMonomial 0 n α.val)).symm

/-- The true finite polynomial leaves an ACTUAL original whole maximal-power remainder. -/
theorem originalTaylorPolynomial_remainder (n k : ℕ) (g : HolGerm (ComplexModel (0+n))) :
    g-originalPolynomialEval n (originalTaylorPolynomial n k g) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) :=
  Ideal.Quotient.eq.mp (originalTaylorPolynomial_quotient_class n k g).symm

/-- True bounded support and a genuine whole remainder uniquely determine the original polynomial. -/
theorem originalTaylorPolynomial_unique (n k : ℕ) (g : HolGerm (ComplexModel (0+n)))
    (P : MvPolynomial (Fin n) ℂ)
    (hbound : ∀ α, k+1 ≤ normalExponentDegree α → MvPolynomial.coeff α P=0)
    (hrem : g-originalPolynomialEval n P ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1)) :
    P=originalTaylorPolynomial n k g := by
  have hp : originalPolynomialEval n (P-originalTaylorPolynomial n k g) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) := by
    rw [map_sub]
    have he : originalPolynomialEval n P-originalPolynomialEval n (originalTaylorPolynomial n k g)=
        (g-originalPolynomialEval n (originalTaylorPolynomial n k g))-(g-originalPolynomialEval n P) := by ring
    rw [he]
    exact Ideal.sub_mem _ (originalTaylorPolynomial_remainder n k g) hrem
  ext α
  by_cases hα : normalExponentDegree α < k+1
  · have hc := originalPolynomial_coefficient_eq_zero_of_eval_mem n (k+1) _ α hα hp
    simpa only [MvPolynomial.coeff_sub,sub_eq_zero] using hc
  · rw [hbound α (by omega),originalTaylorPolynomial_coefficient_high n k g α (by omega)]

/-- The same actual original complex coordinate map preserves addition of entire numerators. -/
theorem originalTaylorPolynomial_add (n k : ℕ) (g h : HolGerm (ComplexModel (0+n))) :
    originalTaylorPolynomial n k (g+h)=originalTaylorPolynomial n k g+originalTaylorPolynomial n k h := by
  ext α
  by_cases hα : normalExponentDegree α < k+1
  · rw [originalTaylorPolynomial_coefficient_low n k (g+h) α hα,MvPolynomial.coeff_add,
      originalTaylorPolynomial_coefficient_low n k g α hα,originalTaylorPolynomial_coefficient_low n k h α hα]
    exact congrFun ((originalJetCoordinates n k).map_add g h) ⟨α,hα⟩
  · rw [originalTaylorPolynomial_coefficient_high n k (g+h) α (by omega),MvPolynomial.coeff_add,
      originalTaylorPolynomial_coefficient_high n k g α (by omega),
      originalTaylorPolynomial_coefficient_high n k h α (by omega),add_zero]

/-- Original complex constants act by the SAME original complex scalar on every actual polynomial. -/
theorem originalTaylorPolynomial_smul (n k : ℕ) (c : ℂ) (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorPolynomial n k (c • g)=c • originalTaylorPolynomial n k g := by
  ext α
  by_cases hα : normalExponentDegree α < k+1
  · rw [originalTaylorPolynomial_coefficient_low n k (c • g) α hα,MvPolynomial.coeff_smul,
      originalTaylorPolynomial_coefficient_low n k g α hα]
    exact congrFun ((originalJetCoordinates n k).map_smul c g) ⟨α,hα⟩
  · rw [originalTaylorPolynomial_coefficient_high n k (c • g) α (by omega),MvPolynomial.coeff_smul,
      originalTaylorPolynomial_coefficient_high n k g α (by omega),smul_zero]

/-- Genuine whole original remainders internally force stabilization of every lower coefficient. -/
theorem originalTaylorPolynomial_coefficient_stable (n k l : ℕ) (hkl : k ≤ l)
    (g : HolGerm (ComplexModel (0+n))) (α : Fin n →₀ ℕ) (hα : normalExponentDegree α < k+1) :
    MvPolynomial.coeff α (originalTaylorPolynomial n l g)=MvPolynomial.coeff α (originalTaylorPolynomial n k g) := by
  have hl : g-originalPolynomialEval n (originalTaylorPolynomial n l g) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) :=
    Ideal.pow_le_pow_right (by omega) (originalTaylorPolynomial_remainder n l g)
  have hp : originalPolynomialEval n (originalTaylorPolynomial n l g-originalTaylorPolynomial n k g) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) := by
    rw [map_sub]
    have he : originalPolynomialEval n (originalTaylorPolynomial n l g)-originalPolynomialEval n (originalTaylorPolynomial n k g)=
        (g-originalPolynomialEval n (originalTaylorPolynomial n k g))-(g-originalPolynomialEval n (originalTaylorPolynomial n l g)) := by ring
    rw [he]
    exact Ideal.sub_mem _ (originalTaylorPolynomial_remainder n k g) hl
  have hc := originalPolynomial_coefficient_eq_zero_of_eval_mem n (k+1) _ α hα hp
  simpa only [MvPolynomial.coeff_sub,sub_eq_zero] using hc

/-- The stable ORIGINAL complex coefficient map, before any formal-series multiplication is introduced. -/
def originalTaylorCoefficientMap (n : ℕ) : HolGerm (ComplexModel (0+n)) →ₗ[ℂ] ((Fin n →₀ ℕ) → ℂ) where
  toFun g α := originalJetCoordinates n (normalExponentDegree α) g ⟨α,by omega⟩
  map_add' g h := by
    funext α
    exact congrFun ((originalJetCoordinates n (normalExponentDegree α)).map_add g h) ⟨α,by omega⟩
  map_smul' c g := by
    funext α
    exact congrFun ((originalJetCoordinates n (normalExponentDegree α)).map_smul c g) ⟨α,by omega⟩

/-- ALL actual larger truncations retain the SAME internally produced original complex coefficient. -/
theorem originalTaylorCoefficientMap_eq_coefficient (n k : ℕ) (g : HolGerm (ComplexModel (0+n)))
    (α : Fin n →₀ ℕ) (hα : normalExponentDegree α < k+1) :
    originalTaylorCoefficientMap n g α=MvPolynomial.coeff α (originalTaylorPolynomial n k g) := by
  have hs := originalTaylorPolynomial_coefficient_stable n (normalExponentDegree α) k (by omega) g α (by omega)
  rw [originalTaylorPolynomial_coefficient_low n (normalExponentDegree α) g α (by omega)] at hs
  exact hs.symm

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Every original complex coefficient vanishes only for the true zero original germ. -/
theorem originalTaylorCoefficientMap_eq_zero_iff (n : ℕ) (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorCoefficientMap n g=0 ↔ g=0 := by
  constructor
  · intro hzero
    have hg : g ∈ (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) := by
      apply (mem_original_ideal_iff_all_positive_thickenings ⊥ g).mpr
      intro k
      have hp : originalTaylorPolynomial n k g=0 := by
        ext α
        by_cases hα : normalExponentDegree α < k+1
        · rw [← originalTaylorCoefficientMap_eq_coefficient n k g α hα]
          exact congrFun hzero α
        · exact originalTaylorPolynomial_coefficient_high n k g α (by omega)
      have hrem := originalTaylorPolynomial_remainder n k g
      rw [hp,map_zero,sub_zero] at hrem
      simpa only [bot_sup_eq] using hrem
    simpa only [Ideal.mem_bot] using hg
  · rintro rfl
    exact map_zero _

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The entire original germ ring has a faithful complex linear system of ACTUAL stabilized coefficients. -/
theorem originalTaylorCoefficientMap_injective (n : ℕ) : Function.Injective (originalTaylorCoefficientMap n) := by
  intro g h he
  apply sub_eq_zero.mp
  apply (originalTaylorCoefficientMap_eq_zero_iff n (g-h)).mp
  rw [map_sub,he,sub_self]

end
end Hironaka.HironakaActualOriginalTaylorPolynomial
