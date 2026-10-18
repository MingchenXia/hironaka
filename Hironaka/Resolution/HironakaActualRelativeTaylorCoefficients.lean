/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRelativeCoefficientGerms
import Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality
import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-! Literal entire formal coefficients of actual analytic relative coefficient germs. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualRelativeTaylorCoefficients
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
  HironakaActualRelativeCoefficientGerms OkaRelationSheaf

/-- The true inclusion of the first coordinate block. -/
def actualTangentFormalEmbedding (d t : ℕ) : Fin d ↪ Fin (d+t) :=
  ⟨Fin.castAdd t, fun _ _ h => Fin.ext (congrArg (fun x : Fin (d+t) => x.val) h)⟩

/-- The true inclusion of the second coordinate block. -/
def actualNormalFormalEmbedding (d t : ℕ) : Fin t ↪ Fin (d+t) :=
  ⟨Fin.natAdd d, fun _ _ h => Fin.ext (by have hh := congrArg Fin.val h; simpa using hh)⟩

/-- Genuine exponent embedding has exactly zero normal block. -/
theorem actualJoinedExponent_tangent_embedding (d t : ℕ) (β : Fin d →₀ ℕ) :
    actualJoinedExponent β (0 : Fin t →₀ ℕ)=
      Finsupp.embDomain (actualTangentFormalEmbedding d t) β := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change _ = Finsupp.embDomain (actualTangentFormalEmbedding d t) β
      (actualTangentFormalEmbedding d t j)
    rw [Finsupp.embDomain_apply_self]
    simp [actualJoinedExponent]
  · have hn : ¬∃ a : Fin d, actualTangentFormalEmbedding d t a=j.natAdd d := by
      rintro ⟨a,ha⟩
      have hval := congrArg Fin.val ha
      change a.val=d+j.val at hval
      omega
    rw [Finsupp.embDomain_apply, dif_neg hn]
    simp [actualJoinedExponent]

/-- Genuine exponent embedding has exactly zero tangential block. -/
theorem actualJoinedExponent_normal_embedding (d t : ℕ) (α : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin d →₀ ℕ) α=
      Finsupp.embDomain (actualNormalFormalEmbedding d t) α := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hn : ¬∃ a : Fin t, actualNormalFormalEmbedding d t a=j.castAdd t := by
      rintro ⟨a,ha⟩
      have hval := congrArg Fin.val ha
      change d+a.val=j.val at hval
      omega
    rw [Finsupp.embDomain_apply,dif_neg hn]
    simp [actualJoinedExponent]
  · change _ = Finsupp.embDomain (actualNormalFormalEmbedding d t) α
      (actualNormalFormalEmbedding d t j)
    rw [Finsupp.embDomain_apply_self]
    simp [actualJoinedExponent]

/-- Genuine Taylor expansion sends an actual entire normal monomial to the literal formal monomial. -/
theorem actualUnshiftedTaylor_normalExponentMonomial (d t : ℕ) (α : Fin t →₀ ℕ) :
    actualUnshiftedTaylorAlgHom (d+t) (normalExponentMonomial d t α)=
      MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) α) (1 : ℂ) := by
  rw [normalExponentMonomial,map_prod]
  simp_rw [map_pow,originalTaylor_normalCoordinate]
  rw [actualJoinedExponent_normal_embedding,Finsupp.embDomain_eq_mapDomain,
    MvPowerSeries.monomial_mapDomain_apply_one]
  symm
  exact α.prod_fintype (fun i k => (MvPowerSeries.X (i.natAdd d) : MvPowerSeries (Fin (d+t)) ℂ)^k)
    (fun _ => pow_zero _)

/-- Renaming a true tangential series has no nonzero normal coefficient. -/
theorem coefficient_tangent_rename_joined (d t : ℕ) (F : MvPowerSeries (Fin d) ℂ)
    (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff (actualJoinedExponent β γ) (MvPowerSeries.rename (Fin.castAdd t) F)=
      if γ=0 then MvPowerSeries.coeff β F else 0 := by
  by_cases hγ : γ=0
  · subst γ
    rw [if_pos rfl,actualJoinedExponent_tangent_embedding]
    exact MvPowerSeries.coeff_embDomain_rename (actualTangentFormalEmbedding d t) F β
  · rw [if_neg hγ]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨δ,hδ⟩
    apply hγ
    have he : actualJoinedExponent δ (0 : Fin t →₀ ℕ)=actualJoinedExponent β γ := by
      rw [actualJoinedExponent_tangent_embedding,Finsupp.embDomain_eq_mapDomain]
      exact hδ
    ext j
    have hh := congrArg (fun a : Fin (d+t) →₀ ℕ => a (j.natAdd d)) he.symm
    simpa [actualJoinedExponent] using hh

/-- Actual formal normal-monomial multiplication extracts the exact whole tangential coefficient. -/
theorem coefficient_tangent_rename_mul_normal_monomial (d t : ℕ)
    (F : MvPowerSeries (Fin d) ℂ) (β : Fin d →₀ ℕ) (α γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff (actualJoinedExponent β γ)
      (MvPowerSeries.rename (Fin.castAdd t) F *
        MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) α) 1)=
      if α=γ then MvPowerSeries.coeff β F else 0 := by
  rw [MvPowerSeries.coeff_mul_monomial]
  by_cases hle : actualJoinedExponent (0 : Fin d →₀ ℕ) α ≤ actualJoinedExponent β γ
  · rw [if_pos hle,mul_one]
    have hαγ : α ≤ γ := by
      intro j
      have h := hle (j.natAdd d)
      simpa [actualJoinedExponent] using h
    have he : actualJoinedExponent β γ-actualJoinedExponent (0 : Fin d →₀ ℕ) α=
        actualJoinedExponent β (γ-α) := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]
    rw [he,coefficient_tangent_rename_joined]
    have hz : γ-α=0 ↔ α=γ := by
      constructor
      · intro h
        exact le_antisymm hαγ (tsub_eq_zero_iff_le.mp h)
      · intro h
        subst γ
        exact tsub_self _
    simp only [hz]
  · rw [if_neg hle]
    have hne : α ≠ γ := by
      intro h
      subst γ
      apply hle
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]
    rw [if_neg hne]

/-- The coefficient formula applies to the actual original normal polynomial monomial. -/
theorem coefficient_actualTaylor_normalPolynomial_monomial (d t : ℕ)
    (a : HolGerm (ComplexModel d)) (β : Fin d →₀ ℕ) (α γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff (actualJoinedExponent β γ)
      (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t (MvPolynomial.monomial α a)))=
      if α=γ then MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom d a) else 0 := by
  rw [normalPolynomialEval_monomial,map_mul,actualUnshiftedTaylor_normalExponentMonomial]
  have he := congrArg (fun f : HolGerm (ComplexModel d) →ₐ[ℂ] MvPowerSeries (Fin (d+t)) ℂ => f a)
    (actualUnshiftedTaylor_tangentPullback d t)
  change actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t a)=
    MvPowerSeries.rename (Fin.castAdd t) (actualUnshiftedTaylorAlgHom d a) at he
  rw [he]
  exact coefficient_tangent_rename_mul_normal_monomial d t _ β α γ

/-- Every coefficient of the genuine Taylor expansion of an actual relative polynomial is literal. -/
theorem actualFormalNormalCoefficient_normalPolynomialEval (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (γ : Fin t →₀ ℕ) :
    actualFormalNormalCoefficient
      (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t P)) γ=
      actualUnshiftedTaylorAlgHom d (MvPolynomial.coeff γ P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α a =>
      apply MvPowerSeries.ext
      intro β
      change MvPowerSeries.coeff (actualJoinedExponent β γ)
        (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t (MvPolynomial.monomial α a)))=_
      rw [coefficient_actualTaylor_normalPolynomial_monomial,MvPolynomial.coeff_monomial]
      split_ifs <;> simp
  | add P Q hP hQ =>
      apply MvPowerSeries.ext
      intro β
      have hp := congrArg (MvPowerSeries.coeff β) hP
      have hq := congrArg (MvPowerSeries.coeff β) hQ
      change MvPowerSeries.coeff (actualJoinedExponent β γ)
        (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t (P+Q)))=_
      simp only [map_add,MvPolynomial.coeff_add]
      exact congrArg₂ (·+·) hp hq

/-- The actual normal-coordinate ideal counts exactly the true normal exponent, regardless of tangent degree. -/
theorem actualJoinedExponent_normal_weight (d t : ℕ) (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    Finsupp.weight (HironakaActualFormalCoordinatePowerDivision.actualCoordinateWeight
      (actualTangentCentreVariables d t)) (actualJoinedExponent β γ)=normalExponentDegree γ := by
  have hcast (j : Fin d) : j.castAdd t ∉ actualTangentCentreVariables d t := by
    rintro ⟨k,hk⟩
    have hh := congrArg Fin.val hk
    change d+k.val=j.val at hh
    omega
  have hnormal (j : Fin t) : j.natAdd d ∈ actualTangentCentreVariables d t := ⟨j,rfl⟩
  rw [Finsupp.weight_eq_sum,Fin.sum_univ_add]
  simp [actualJoinedExponent,HironakaActualFormalCoordinatePowerDivision.actualCoordinateWeight,
    hcast,hnormal,normalExponentDegree,smul_eq_mul]

/-- The whole original Taylor normal coefficient is exactly the Taylor series of the genuine analytic coefficient germ. -/
theorem actualFormalNormalCoefficient_actualTaylor (d t : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    actualFormalNormalCoefficient (actualUnshiftedTaylorAlgHom (d+t) g) γ=
      actualUnshiftedTaylorAlgHom d (actualNormalAnalyticCoefficientGerm d t g γ) := by
  let q := normalExponentDegree γ+1
  let P := actualNormalTaylorPolynomial d t q g
  have hm := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
    (actualNormalTaylorPolynomial_remainder d t q g)
  rw [Ideal.map_pow,map_normalIdeal_originalTaylor] at hm
  apply MvPowerSeries.ext
  intro β
  have hz := (HironakaActualFormalCoordinatePowerDivision.mem_actualFormalCoordinateIdeal_pow_iff
    (actualTangentCentreVariables d t) q _).mp hm (actualJoinedExponent β γ)
    (by rw [actualJoinedExponent_normal_weight];dsimp [q];omega)
  rw [map_sub,map_sub,sub_eq_zero] at hz
  have hp := congrArg (MvPowerSeries.coeff β)
    (actualFormalNormalCoefficient_normalPolynomialEval d t P γ)
  exact hz.trans hp

/-- All finite actual analytic families have genuine representatives on a common low-degree domain with literal entire-series identities. -/
theorem exists_actual_finite_coefficient_common_domain_with_Taylor (d t q : ℕ)
    {ι : Type*} [Fintype ι] (g : ι → HolGerm (ComplexModel (d+t))) :
    ∃ (U : Set (ComplexModel d)), IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
      ∃ (c : ι → (Fin t →₀ ℕ) → ComplexModel d → ℂ) (hc : ∀ i α, HolAt (c i α) 0),
        (∀ i α, normalExponentDegree α < q →
          MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (c i α) U) ∧
        (∀ i α, actualFormalNormalCoefficient (actualUnshiftedTaylorAlgHom (d+t) (g i)) α=
          actualUnshiftedTaylorAlgHom d (HolGerm.mk (c i α) (hc i α))) ∧
        ∀ i r α, normalExponentDegree α < r →
          MvPolynomial.coeff α (actualNormalTaylorPolynomial d t r (g i))=HolGerm.mk (c i α) (hc i α) := by
  obtain ⟨U,hU,h0,c,hc,hhol,he,hstable⟩ := exists_actual_finite_coefficient_common_domain d t q g
  refine ⟨U,hU,h0,c,hc,hhol,?_,hstable⟩
  intro i α
  rw [actualFormalNormalCoefficient_actualTaylor,he i α]

end
end Hironaka.HironakaActualRelativeTaylorCoefficients
