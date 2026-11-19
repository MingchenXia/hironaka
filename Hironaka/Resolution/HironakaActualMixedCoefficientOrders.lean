/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRelativeNormalizedSaturation

/-!
# Actual mixed point-order coefficient constraints in the same relative chart

Whole original maximal powers are detected by finite orders of the actual
analytic normal coefficient germs. Literal homogeneous bands retain tangent
degrees. For the SAME actual normalized quotient, genuine whole exceptional
congruence and actual Taylor separation identify every pivot-free base germ
with the literal B-polynomial coefficient, deriving its actual mixed order
from only the natural CURRENT quotient order.

These are concrete finite mixed coefficient constraints, not completed mixed
syzygy lifting, maximal-symbol regularity or a relative HS criterion.
Blueprint: `hironaka-actual-mixed-coefficient-orders-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualMixedCoefficientOrders
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis HironakaRelativeNormalIdeal
  HironakaActualOriginalFormalTaylor HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualAnalyticFormalNormalPowers HironakaActualRelativePolynomialRehomogenization
  HironakaActualNormalQuotientExceptionalRestriction HironakaActualNormalAxisDehomogenization
  HironakaActualNormalHomogeneousComponents
  HironakaActualAnalyticBlowupTaylor HironakaHolomorphicJetMonomialSpan
  HironakaActualTaylorCoordinateNaturality

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h


private theorem actual_maximal_power_iff (n q : ℕ) (g : HolGerm (ComplexModel n)) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      ∀ α : Fin n →₀ ℕ,normalExponentDegree α<q → MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=0 := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ h : HolGerm (ComplexModel m),h∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel m))^q ↔
      ∀ α : Fin n →₀ ℕ,normalExponentDegree α<q → MvPowerSeries.coeff α (f h)=0
  have h : P (0+n) (originalTaylorAlgHom n) := fun h =>
    mem_original_maximal_pow_iff_formal_coefficients_zero n q h
  exact unshiftedTaylor_property n P h g

private theorem joined_degree {d t : ℕ} (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    normalExponentDegree (actualJoinedExponent β γ)=normalExponentDegree β+normalExponentDegree γ := by
  simp [normalExponentDegree,actualJoinedExponent,Fin.sum_univ_add]

/-- The WHOLE original maximal power is exactly its finite mixed base-germ coefficient orders. -/
theorem mem_maximal_pow_iff_actual_normal_coefficients (d t q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^q ↔
      ∀ γ : Fin t →₀ ℕ,normalExponentDegree γ<q →
        actualNormalAnalyticCoefficientGerm d t g γ∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))^(q-normalExponentDegree γ) := by
  constructor
  · intro hg γ hγ
    apply (actual_maximal_power_iff d _ _).mpr
    intro β hβ
    rw [←actualFormalNormalCoefficient_actualTaylor]
    change MvPowerSeries.coeff (actualJoinedExponent β γ) (actualUnshiftedTaylorAlgHom (d+t) g)=0
    apply (actual_maximal_power_iff (d+t) q g).mp hg
    rw [joined_degree]
    omega
  · intro hc
    apply (actual_maximal_power_iff (d+t) q g).mpr
    intro α hα
    let β := actualTangentExponent α
    let γ := actualNormalExponent α
    have hsplit : actualJoinedExponent β γ=α := actualJoinedExponent_split α
    have hsum : normalExponentDegree β+normalExponentDegree γ<q := by rw [←joined_degree,hsplit];exact hα
    have hγ : normalExponentDegree γ<q := by omega
    have hβ : normalExponentDegree β<q-normalExponentDegree γ := by omega
    have hz := (actual_maximal_power_iff d _ _).mp (hc γ hγ) β hβ
    rw [←actualFormalNormalCoefficient_actualTaylor] at hz
    change MvPowerSeries.coeff (actualJoinedExponent β γ) (actualUnshiftedTaylorAlgHom (d+t) g)=0 at hz
    rwa [hsplit] at hz

/-- The genuine TOTAL homogeneous band retains the exact tangent degree of every actual normal coefficient. -/
theorem actualFormalNormalCoefficient_homogeneousComponent (d t q : ℕ)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (γ : Fin t →₀ ℕ) :
    actualFormalNormalCoefficient (MvPowerSeries.homogeneousComponent q F) γ=
      if normalExponentDegree γ≤q then MvPowerSeries.homogeneousComponent (q-normalExponentDegree γ)
        (actualFormalNormalCoefficient F γ) else 0 := by
  apply MvPowerSeries.ext
  intro β
  change MvPowerSeries.coeff (actualJoinedExponent β γ) (MvPowerSeries.homogeneousComponent q F)=_
  rw [MvPowerSeries.coeff_homogeneousComponent]
  have hj : (actualJoinedExponent β γ).degree=β.degree+normalExponentDegree γ := by
    simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using joined_degree β γ
  by_cases hγ : normalExponentDegree γ≤q
  · rw [if_pos hγ,MvPowerSeries.coeff_homogeneousComponent]
    have he : (actualJoinedExponent β γ).degree=q ↔ β.degree=q-normalExponentDegree γ := by omega
    simp only [he]
    rfl
  · rw [if_neg hγ,map_zero]
    have he : (actualJoinedExponent β γ).degree≠q := by omega
    simp only [if_neg he]

/-- Genuine whole exceptional congruence identifies EVERY pivot-free entire analytic coefficient. -/
theorem relative_quotient_pivot_free_coefficient (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (w : ℕ) (G H : HolGerm (ComplexModel (d+t))) (hG : G∈normalIdeal d t ^w)
    (hH : coordinateGerm (j.natAdd d)^w*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b G)
    (γ : Fin t →₀ ℕ) (hγ : γ j=0) :
    actualNormalAnalyticCoefficientGerm d t H γ=MvPolynomial.coeff γ
      (relativePolynomialDehomogenization j b (actualNormalHomogeneousPolynomial d t w G)) := by
  let p := relativePolynomialDehomogenization j b (actualNormalHomogeneousPolynomial d t w G)
  have hcong : H-normalPolynomialEval d t p∈Ideal.span {coordinateGerm (j.natAdd d)} := by
    change H-normalPolynomialEval d t (relativePolynomialDehomogenization j b _ )∈_
    rw [relativePolynomialDehomogenization_eval]
    exact actual_analytic_normal_quotient_initial_restriction d t j b w G H hG hH
  obtain ⟨K,hK⟩ := Ideal.mem_span_singleton.mp hcong
  have hdiv : (MvPowerSeries.X (j.natAdd d) : MvPowerSeries (Fin (d+t)) ℂ)^1 ∣
      actualUnshiftedTaylorAlgHom (d+t) H-actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t p) := by
    refine ⟨actualUnshiftedTaylorAlgHom (d+t) K,?_⟩
    rw [pow_one,←map_sub,hK,map_mul,actualUnshiftedTaylor_coordinate]
  apply actualUnshiftedTaylorAlgHom_injective d
  change actualUnshiftedTaylorAlgHom d (actualNormalAnalyticCoefficientGerm d t H γ)=
    actualUnshiftedTaylorAlgHom d (MvPolynomial.coeff γ p)
  rw [←actualFormalNormalCoefficient_actualTaylor,←actualFormalNormalCoefficient_normalPolynomialEval]
  apply MvPowerSeries.ext
  intro β
  have hidx : actualJoinedExponent β γ (j.natAdd d)<1 := by simp [actualJoinedExponent,hγ]
  have hz := MvPowerSeries.X_pow_dvd_iff.mp hdiv (actualJoinedExponent β γ) hidx
  rw [map_sub,sub_eq_zero] at hz
  exact hz

/-- Natural CURRENT quotient orders OUTPUT actual finite mixed base-coefficient orders for the SAME literal chart polynomial. -/
theorem relative_quotient_mixed_coefficient_order (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (w r : ℕ) (G H : HolGerm (ComplexModel (d+t))) (hG : G∈normalIdeal d t ^w)
    (hH : coordinateGerm (j.natAdd d)^w*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b G)
    (hOrder : H∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^r)
    (γ : Fin t →₀ ℕ) (hγ : γ j=0) (hdeg : normalExponentDegree γ<r) :
    MvPolynomial.coeff γ (relativePolynomialDehomogenization j b (actualNormalHomogeneousPolynomial d t w G))∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))^(r-normalExponentDegree γ) := by
  rw [←relative_quotient_pivot_free_coefficient d t j b w G H hG hH γ hγ]
  exact (mem_maximal_pow_iff_actual_normal_coefficients d t r H).mp hOrder γ hdeg

end
end Hironaka.HironakaActualMixedCoefficientOrders
