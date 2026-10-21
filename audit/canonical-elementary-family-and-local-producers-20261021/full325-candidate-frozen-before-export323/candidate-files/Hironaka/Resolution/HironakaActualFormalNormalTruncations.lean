/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Pi
/-!
# Actual formal base change of whole normal truncations

Literal finite normal monomial combinations over the original formal tangent
series ring give all whole formal normal-power quotients. Their injectivity
and surjectivity use the actual entire normal-coefficient power criterion.
The genuine analytic normal monomial equivalence, after formal base tensoring,
therefore identifies every actual analytic normal truncation with its whole
formal counterpart. Every pure tensor retains its original Taylor numerator.

This treats the ambient I=0 normal-power quotient. Additional original ideal
images, transition compatibility, canonical standard monomial families and
reduced-vertex centre powers remain separate assertions.
-/

set_option autoImplicit false
open Set TensorProduct
open scoped TensorProduct
namespace Hironaka.HironakaActualFormalNormalTruncations
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
variable (d t q : ℕ)
local instance : Fintype (normalExponentIndex t q) := normalExponentFintype t q
local instance instAlgebraMvPowerSeriesFinComplexHAddNat_transcendentalNakamaye : Algebra (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin (d+t)) ℂ) :=
  (MvPowerSeries.rename (Fin.castAdd t : Fin d → Fin (d+t))).toRingHom.toAlgebra

def formalNormalCombination : (normalExponentIndex t q → MvPowerSeries (Fin d) ℂ) →ₗ[MvPowerSeries (Fin d) ℂ]
    MvPowerSeries (Fin (d+t)) ℂ :=
  Fintype.linearCombination (MvPowerSeries (Fin d) ℂ)
    (fun γ => MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val) 1)

theorem formalNormalCombination_coefficient
    (a : normalExponentIndex t q → MvPowerSeries (Fin d) ℂ)
    (γ : normalExponentIndex t q) (β : Fin d →₀ ℕ) :
    MvPowerSeries.coeff (actualJoinedExponent β γ.val) (formalNormalCombination d t q a)=
      MvPowerSeries.coeff β (a γ) := by
  change MvPowerSeries.coeff (actualJoinedExponent β γ.val)
    (∑ α : normalExponentIndex t q, MvPowerSeries.rename (Fin.castAdd t) (a α) *
      MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) α.val) 1)=_
  rw [map_sum]
  simp_rw [coefficient_tangent_rename_mul_normal_monomial]
  rw [Finset.sum_eq_single γ]
  · rw [if_pos rfl]
  · intro α _ hαγ
    rw [if_neg (fun he => hαγ (Subtype.ext he))]
  · intro hγ
    exact False.elim (hγ (Finset.mem_univ γ))

def formalNormalMonomialMap :
    (normalExponentIndex t q → MvPowerSeries (Fin d) ℂ) →ₗ[MvPowerSeries (Fin d) ℂ]
    (MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) :=
  (Ideal.Quotient.mkₐ (MvPowerSeries (Fin d) ℂ)
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)).toLinearMap.comp
      (formalNormalCombination d t q)

theorem formalNormalMonomialMap_injective : Function.Injective (formalNormalMonomialMap d t q) := by
  intro a b hab
  funext γ
  apply MvPowerSeries.ext
  intro β
  have hm := Ideal.Quotient.eq.mp hab
  have hz := (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q _).mp hm
    (actualJoinedExponent β γ.val) (by rw [actualJoinedExponent_normal_weight]; exact γ.property)
  rw [map_sub,formalNormalCombination_coefficient,formalNormalCombination_coefficient] at hz
  exact sub_eq_zero.mp hz

theorem formalNormalMonomialMap_surjective : Function.Surjective (formalNormalMonomialMap d t q) := by
  intro x
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective x
  let a : normalExponentIndex t q → MvPowerSeries (Fin d) ℂ :=
    fun γ => actualFormalNormalCoefficient F γ.val
  have hm : F-formalNormalCombination d t q a ∈
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q := by
    apply (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q _).mpr
    intro α hα
    let β := actualTangentExponent α
    let γ := actualNormalExponent α
    have he : actualJoinedExponent β γ=α := actualJoinedExponent_split α
    have hγ : normalExponentDegree γ < q := by
      rw [← he,actualJoinedExponent_normal_weight] at hα
      exact hα
    rw [← he,map_sub,formalNormalCombination_coefficient d t q a ⟨γ,hγ⟩ β]
    exact sub_self _
  refine ⟨a,Ideal.Quotient.eq.mpr ?_⟩
  simpa only [neg_sub] using
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q).neg_mem hm

def formalNormalPowerLinearEquiv :
    (normalExponentIndex t q → MvPowerSeries (Fin d) ℂ) ≃ₗ[MvPowerSeries (Fin d) ℂ]
    (MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) :=
  LinearEquiv.ofBijective (formalNormalMonomialMap d t q)
    ⟨formalNormalMonomialMap_injective d t q,formalNormalMonomialMap_surjective d t q⟩

local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
local instance : Algebra (HolGerm (ComplexModel d)) (MvPowerSeries (Fin d) ℂ) :=
  (actualUnshiftedTaylorAlgHom d).toRingHom.toAlgebra

theorem formalNormalMonomialMap_actualTaylorCoordinates (g : HolGerm (ComplexModel (d+t))) :
    formalNormalMonomialMap d t q
      (fun γ => actualUnshiftedTaylorAlgHom d (actualNormalJetCoordinates d t q g γ))=
    Ideal.Quotient.mk
      (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
      (actualUnshiftedTaylorAlgHom (d+t) g) := by
  apply Ideal.Quotient.eq.mpr
  apply (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q _).mpr
  intro α hα
  let β := actualTangentExponent α
  let γ := actualNormalExponent α
  have he : actualJoinedExponent β γ=α := actualJoinedExponent_split α
  have hγ : normalExponentDegree γ < q := by
    rw [← he,actualJoinedExponent_normal_weight] at hα
    exact hα
  rw [← he,map_sub,formalNormalCombination_coefficient d t q _ ⟨γ,hγ⟩ β]
  have hc := congrArg (MvPowerSeries.coeff β) (actualFormalNormalCoefficient_actualTaylor d t g γ)
  have ha : actualNormalAnalyticCoefficientGerm d t g γ=actualNormalJetCoordinates d t q g ⟨γ,hγ⟩ := by
    rw [← actualNormalTaylorPolynomial_coefficient_eq_germ d t q g γ hγ]
    exact actualNormalTaylorPolynomial_coefficient d t q g ⟨γ,hγ⟩
  rw [ha] at hc
  exact sub_eq_zero.mpr hc.symm

def normalTruncationBaseChangeEquiv :
    (MvPowerSeries (Fin d) ℂ ⊗[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t^q)) ≃ₗ[MvPowerSeries (Fin d) ℂ]
    (MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) :=
  (((normalPowerLinearEquiv d t q).symm.baseChange (HolGerm (ComplexModel d))
    (MvPowerSeries (Fin d) ℂ) _ _).trans
      (TensorProduct.piScalarRight (HolGerm (ComplexModel d))
        (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin d) ℂ) (normalExponentIndex t q))).trans
          (formalNormalPowerLinearEquiv d t q)

theorem normalTruncationBaseChangeEquiv_tmul_mk
    (c : MvPowerSeries (Fin d) ℂ) (g : HolGerm (ComplexModel (d+t))) :
    normalTruncationBaseChangeEquiv d t q
      (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (normalIdeal d t^q) g)=
    c • Ideal.Quotient.mk
      (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
      (actualUnshiftedTaylorAlgHom (d+t) g) := by
  change formalNormalMonomialMap d t q
    (fun γ => actualUnshiftedTaylorAlgHom d (actualNormalJetCoordinates d t q g γ) * c)=_
  have hf : (fun γ => actualUnshiftedTaylorAlgHom d (actualNormalJetCoordinates d t q g γ)*c)=
      c • (fun γ => actualUnshiftedTaylorAlgHom d (actualNormalJetCoordinates d t q g γ)) := by
    funext γ
    exact mul_comm _ _
  rw [hf,map_smul,formalNormalMonomialMap_actualTaylorCoordinates]

end
end Hironaka.HironakaActualFormalNormalTruncations
