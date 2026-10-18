/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalPolynomialJetAlgebra

/-! Actual stable relative coefficient germs and genuine common finite holomorphic domains.
The full formal normal-coefficient dictionary remains a separate producer. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualRelativeCoefficientGerms
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalPolynomialJetAlgebra OkaRelationSheaf

/-- Actual original normal-power quotient coordinates, not a prescribed coefficient family. -/
def actualNormalJetCoordinates (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) : normalExponentIndex t q → HolGerm (ComplexModel d) :=
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  (normalPowerLinearEquiv d t q).symm (Ideal.Quotient.mk (normalIdeal d t ^ q) g)

/-- The actual finite original polynomial extracted from the true quotient class. -/
def actualNormalTaylorPolynomial (d t q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  let := normalExponentFintype t q
  ∑ α : normalExponentIndex t q, MvPolynomial.monomial α.val (actualNormalJetCoordinates d t q g α)

/-- Each true low polynomial coefficient is exactly the entire original quotient coordinate. -/
theorem actualNormalTaylorPolynomial_coefficient (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (α : normalExponentIndex t q) :
    MvPolynomial.coeff α.val (actualNormalTaylorPolynomial d t q g) =
      actualNormalJetCoordinates d t q g α :=
  coefficient_normalMonomialCombination_polynomial d t q _ α

/-- No artificial high-degree term is inserted into the genuine finite normal polynomial. -/
theorem actualNormalTaylorPolynomial_coefficient_high (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (α : Fin t →₀ ℕ) (hα : q ≤ normalExponentDegree α) :
    MvPolynomial.coeff α (actualNormalTaylorPolynomial d t q g)=0 := by
  let := normalExponentFintype t q
  have hne (β : normalExponentIndex t q) : β.val ≠ α := by
    intro he
    have hlt := β.property
    rw [he] at hlt
    omega
  simp [actualNormalTaylorPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hne]

/-- Genuine quotient-basis inversion gives the SAME original numerator modulo the whole normal power. -/
theorem actualNormalTaylorPolynomial_remainder (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    g-normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g) ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  have he := (normalPowerLinearEquiv d t q).apply_symm_apply
    (Ideal.Quotient.mk (normalIdeal d t ^ q) g)
  change normalMonomialCombination d t q (actualNormalJetCoordinates d t q g)=
    Ideal.Quotient.mk (normalIdeal d t ^ q) g at he
  rw [normalMonomialCombination_apply] at he
  exact Ideal.Quotient.eq.mp he.symm

/-- Genuine whole coefficient separation proves uniqueness, not only equality of point values. -/
theorem actualNormalTaylorPolynomial_unique (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t)))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hhigh : ∀ α, q ≤ normalExponentDegree α → MvPolynomial.coeff α P=0)
    (hrem : g-normalPolynomialEval d t P ∈ normalIdeal d t ^ q) :
    P=actualNormalTaylorPolynomial d t q g := by
  let := tangentAlgebra d t
  have hm : normalPolynomialEval d t (P-actualNormalTaylorPolynomial d t q g) ∈
      normalIdeal d t ^ q := by
    rw [map_sub]
    have he : normalPolynomialEval d t P-normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g)=
        (g-normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g))-
          (g-normalPolynomialEval d t P) := by ring
    rw [he]
    exact Ideal.sub_mem _ (actualNormalTaylorPolynomial_remainder d t q g) hrem
  apply MvPolynomial.ext
  intro α
  by_cases hα : normalExponentDegree α < q
  · have hz := coefficient_eq_zero_of_normalPolynomialEval_mem d t q _ α hα hm
    rw [MvPolynomial.coeff_sub,sub_eq_zero] at hz
    exact hz
  · rw [hhigh α (by omega),actualNormalTaylorPolynomial_coefficient_high d t q g α (by omega)]

/-- Actual original relative coefficients stabilize in the ENTIRE base germ ring. -/
theorem actualNormalTaylorPolynomial_coefficient_stable (d t q r : ℕ) (hqr : q ≤ r)
    (g : HolGerm (ComplexModel (d+t))) (α : Fin t →₀ ℕ) (hα : normalExponentDegree α < q) :
    MvPolynomial.coeff α (actualNormalTaylorPolynomial d t r g)=
      MvPolynomial.coeff α (actualNormalTaylorPolynomial d t q g) := by
  let := tangentAlgebra d t
  have hm : normalPolynomialEval d t
      (actualNormalTaylorPolynomial d t r g-actualNormalTaylorPolynomial d t q g) ∈ normalIdeal d t ^ q := by
    rw [map_sub]
    have he : normalPolynomialEval d t (actualNormalTaylorPolynomial d t r g)-
        normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g)=
      (g-normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g))-
        (g-normalPolynomialEval d t (actualNormalTaylorPolynomial d t r g)) := by ring
    rw [he]
    exact Ideal.sub_mem _ (actualNormalTaylorPolynomial_remainder d t q g)
      (Ideal.pow_le_pow_right hqr (actualNormalTaylorPolynomial_remainder d t r g))
  have hz := coefficient_eq_zero_of_normalPolynomialEval_mem d t q _ α hα hm
  rwa [MvPolynomial.coeff_sub,sub_eq_zero] at hz

/-- One genuine whole holomorphic coefficient germ, independently of all subsequent truncations. -/
def actualNormalAnalyticCoefficientGerm (d t : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (α : Fin t →₀ ℕ) : HolGerm (ComplexModel d) :=
  MvPolynomial.coeff α (actualNormalTaylorPolynomial d t (normalExponentDegree α+1) g)

/-- Every actual later truncation uses the SAME internally constructed original coefficient germs. -/
theorem actualNormalTaylorPolynomial_coefficient_eq_germ (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (α : Fin t →₀ ℕ) (hα : normalExponentDegree α < q) :
    MvPolynomial.coeff α (actualNormalTaylorPolynomial d t q g)=actualNormalAnalyticCoefficientGerm d t g α :=
  actualNormalTaylorPolynomial_coefficient_stable d t (normalExponentDegree α+1) q
    (by omega) g α (by omega)

/-- ALL finite original low coefficient families have one real common holomorphic domain, internally. -/
theorem exists_actual_finite_coefficient_common_domain (d t q : ℕ) {ι : Type*} [Fintype ι]
    (g : ι → HolGerm (ComplexModel (d+t))) :
    ∃ (U : Set (ComplexModel d)), IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
      ∃ (c : ι → (Fin t →₀ ℕ) → ComplexModel d → ℂ) (hc : ∀ i α, HolAt (c i α) 0),
        (∀ i α, normalExponentDegree α < q →
          MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (c i α) U) ∧
        (∀ i α, actualNormalAnalyticCoefficientGerm d t (g i) α=HolGerm.mk (c i α) (hc i α)) ∧
        ∀ i r α, normalExponentDegree α < r →
          MvPolynomial.coeff α (actualNormalTaylorPolynomial d t r (g i))=HolGerm.mk (c i α) (hc i α) := by
  let := normalExponentFintype t q
  choose c hc he using fun i α => HolGerm.exists_eq_mk (actualNormalAnalyticCoefficientGerm d t (g i) α)
  have hnear : ∀ᶠ w in 𝓝 (0 : ComplexModel d),
      ∀ i (α : normalExponentIndex t q), DifferentiableAt ℂ (c i α.val) w :=
    eventually_all.mpr fun i => eventually_all.mpr fun α => hc i α.val
  obtain ⟨U,hUf,hU,h0U⟩ := eventually_nhds_iff.mp hnear
  refine ⟨U,hU,h0U,c,hc,?_,he,?_⟩
  · intro i α hα w hw
    exact ((hUf w hw) i ⟨α,hα⟩).mdifferentiableAt.mdifferentiableWithinAt
  · intro i r α hα
    exact (actualNormalTaylorPolynomial_coefficient_eq_germ d t r (g i) α hα).trans (he i α)

end
end Hironaka.HironakaActualRelativeCoefficientGerms
