/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalNormalTruncations
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis

/-! # Actual reduced vertex normal support from literal monomial independence

The source of the named map consists of finite normal coefficient families
over the entire formal tangent ring, zero on the actual forbidden normal
exponents. Its map is literal monomial evaluation in the actual quotient.
Injectivity forces genuine normal powers of canonical reduced vertices.
The original geometric producer of that injectivity remains separate.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualReducedNormalSupport
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeTaylorCoefficients HironakaActualFormalNormalTruncations
  HironakaRelativeNormalMonomialBasis

variable (d t : ℕ)
local instance (q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q
local instance instAlgebraMvPowerSeriesFinComplexHAddNat_transcendentalNakamaye : Algebra (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin (d+t)) ℂ) :=
  (MvPowerSeries.rename (Fin.castAdd t : Fin d → Fin (d+t))).toRingHom.toAlgebra

/-- Literal finite normal coefficients reconstruct the entire series modulo the true normal power. -/
theorem sub_formalNormalCombination_mem_normal_power (q : ℕ)
    (F : MvPowerSeries (Fin (d+t)) ℂ) :
    F-formalNormalCombination d t q
      (fun γ => actualFormalNormalCoefficient F γ.val) ∈
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q _).mpr
  intro α hα
  let β := actualTangentExponent α
  let γ := actualNormalExponent α
  have he : actualJoinedExponent β γ=α := actualJoinedExponent_split α
  have hγ : normalExponentDegree γ < q := by
    rw [← he,actualJoinedExponent_normal_weight] at hα
    exact hα
  rw [← he,map_sub,formalNormalCombination_coefficient d t q _ ⟨γ,hγ⟩ β]
  exact sub_self _

/-- The actual free normal coefficient arrays restricted to normal-standard labels of the original diagram. -/
def formalStandardNormalCoefficients (m : MonomialOrder (Fin (d+t)))
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) (q : ℕ) :
    Submodule (MvPowerSeries (Fin d) ℂ)
      (normalExponentIndex t q → MvPowerSeries (Fin d) ℂ) where
  carrier := {a | ∀ γ, actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val ∈
    actualInitialDiagram m K → a γ=0}
  zero_mem' := by intro γ _; rfl
  add_mem' := by
    intro a b ha hb γ hγ
    change a γ+b γ=0
    rw [ha γ hγ,hb γ hγ,add_zero]
  smul_mem' := by
    intro c a ha γ hγ
    change c • a γ=0
    rw [ha γ hγ,smul_zero]

/-- The named map sends literal normal-standard coefficients to their genuine monomial classes. -/
def standardNormalMonomialMap (m : MonomialOrder (Fin (d+t)))
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) (q : ℕ) :
    formalStandardNormalCoefficients d t m K q →ₗ[MvPowerSeries (Fin d) ℂ]
      (MvPowerSeries (Fin (d+t)) ℂ ⧸
        (K ⊔ actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)) :=
  (Ideal.Quotient.mkₐ (MvPowerSeries (Fin d) ℂ)
    (K ⊔ actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)).toLinearMap.comp
      ((formalNormalCombination d t q).comp (formalStandardNormalCoefficients d t m K q).subtype)

private theorem joined_zero_le (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin d →₀ ℕ) γ ≤ actualJoinedExponent β γ := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]

/-- Genuine reduced-tail support makes every low normal coefficient an actual normal-standard family. -/
theorem reducedNormalCoefficients_mem_standard (m : MonomialOrder (Fin (d+t)))
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) (a : actualInitialVertices m K)
    (q : ℕ)
    (hq : q ≤ Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) :
    (fun γ : normalExponentIndex t q =>
      actualFormalNormalCoefficient (actualReducedVertexSeries m K a) γ.val) ∈
        formalStandardNormalCoefficients d t m K q := by
  intro γ hγ
  apply MvPowerSeries.ext
  intro β
  rw [map_zero]
  change MvPowerSeries.coeff (actualJoinedExponent β γ.val) (actualReducedVertexSeries m K a)=0
  have hdiag : actualJoinedExponent β γ.val ∈ actualInitialDiagram m K :=
    actualInitialDiagram_upper m K _ _ hγ (joined_zero_le d t β γ.val)
  have hne : actualJoinedExponent β γ.val ≠ a.val := by
    intro he
    have hw := congrArg (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t))) he
    rw [actualJoinedExponent_normal_weight] at hw
    have hl := γ.property
    omega
  rw [actualReducedVertexSeries_coefficient_diagram m K a _ hdiag,if_neg hne]

/-- Literal normal-standard monomial independence forces the genuine canonical reduced vertex into its true normal power. -/
theorem actualReducedVertexSeries_mem_normal_power_of_standardNormalMonomialMap_injective
    (m : MonomialOrder (Fin (d+t))) (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (a : actualInitialVertices m K)
    (hinj : Function.Injective (standardNormalMonomialMap d t m K
      (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val))) :
    actualReducedVertexSeries m K a ∈
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
        Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  let q := Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val
  let F := actualReducedVertexSeries m K a
  let b : formalStandardNormalCoefficients d t m K q :=
    ⟨fun γ => actualFormalNormalCoefficient F γ.val,
      reducedNormalCoefficients_mem_standard d t m K a q le_rfl⟩
  have hdiff := sub_formalNormalCombination_mem_normal_power d t q F
  have hcomb : formalNormalCombination d t q b.val ∈
      K ⊔ actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q := by
    have hm : F ∈ K := actualReducedVertexSeries_mem m K a
    have he : formalNormalCombination d t q b.val =
        F-(F-formalNormalCombination d t q b.val) := by abel
    rw [he]
    exact (K ⊔ actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q).sub_mem
      (Ideal.mem_sup_left hm) (Ideal.mem_sup_right hdiff)
  have hz : standardNormalMonomialMap d t m K q b=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hcomb
  have hb : b=0 := hinj (by simpa only [map_zero] using hz)
  apply (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q F).mpr
  intro α hα
  let β := actualTangentExponent α
  let γ := actualNormalExponent α
  have he : actualJoinedExponent β γ=α := actualJoinedExponent_split α
  have hγ : normalExponentDegree γ < q := by
    rw [← he,actualJoinedExponent_normal_weight] at hα
    exact hα
  have hc := congrArg (fun v : formalStandardNormalCoefficients d t m K q =>
    MvPowerSeries.coeff β (v.val ⟨γ,hγ⟩)) hb
  change MvPowerSeries.coeff (actualJoinedExponent β γ) F=0 at hc
  rwa [he] at hc

/-- One all-order literal independence producer gives true normal support for every actual reduced vertex. -/
theorem all_actualReducedVertexSeries_mem_normal_power_of_standardNormalMonomialMap_injective
    (m : MonomialOrder (Fin (d+t))) (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hinj : ∀ q : ℕ, Function.Injective (standardNormalMonomialMap d t m K q)) :
    ∀ a : actualInitialVertices m K, actualReducedVertexSeries m K a ∈
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
        Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  intro a
  exact actualReducedVertexSeries_mem_normal_power_of_standardNormalMonomialMap_injective
    d t m K a (hinj _)

end
end Hironaka.HironakaActualReducedNormalSupport
