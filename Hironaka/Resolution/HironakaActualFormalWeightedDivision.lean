/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalVertexDivision

/-! Genuine compatible weight bounds for the actual coefficient-recursive whole formal division. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalWeightedDivision
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
variable {n : ℕ}

/-- The genuine recursion preserves every actual weight compatible with its true vertex coefficients. -/
theorem actualDivisionCoefficient_eq_zero_of_weight_lt (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (actualVertexSeries m I a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0) :
    ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → actualDivisionCoefficient m I F c=0 := by
  intro c
  have hwf := InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))
  induction c using hwf.induction with
  | h c ih =>
      intro hc
      rw [actualDivisionCoefficient_eq,hF c hc]
      have ht : actualDivisionTail m I F c=0 := by
        unfold actualDivisionTail
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro p hp
        by_cases hs : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c
        · rw [if_pos hs]
          split_ifs
          · by_cases hz : MvPowerSeries.coeff p.2 (actualVertexSeries m I a)=0
            · rw [hz,mul_zero]
            · have hle : Finsupp.weight w (a : Fin n →₀ ℕ) ≤ Finsupp.weight w p.2 := by
                by_contra h
                exact hz (hvertex a p.2 (lt_of_not_ge h))
              have he : Finsupp.weight w p.1+Finsupp.weight w p.2=Finsupp.weight w c := by
                rw [← map_add,Finset.mem_antidiagonal.mp hp]
              have hsmall : Finsupp.weight w (p.1+(a : Fin n →₀ ℕ)) < d := by
                rw [map_add]
                exact lt_of_le_of_lt ((Nat.add_le_add_left hle _).trans (le_of_eq he)) hc
              rw [ih _ hs hsmall,zero_mul]
          · rfl
        · rw [if_neg hs]
      rw [ht,sub_self]

/-- The SAME genuine quotient series have the actual shifted weight bounds. -/
theorem actualFormalQuotient_coefficient_weight_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (actualVertexSeries m I a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : Finsupp.weight w b+Finsupp.weight w (a : Fin n →₀ ℕ) < d) :
    MvPowerSeries.coeff b (actualFormalQuotient m I F a)=0 := by
  have hz := actualDivisionCoefficient_eq_zero_of_weight_lt m I w d F hvertex hF
    (b+(a : Fin n →₀ ℕ)) (by rwa [map_add])
  change (if actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a then
    actualDivisionCoefficient m I F (b+(a : Fin n →₀ ℕ)) else 0)=0
  split_ifs <;> simp only [hz]

/-- The ACTUAL remainder retains the numerator's compatible weight filtration. -/
theorem actualFormalRemainder_coefficient_weight_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (actualVertexSeries m I a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0)
    (c : Fin n →₀ ℕ) (hc : Finsupp.weight w c < d) :
    MvPowerSeries.coeff c (actualFormalRemainder m I F)=0 := by
  have hz := actualDivisionCoefficient_eq_zero_of_weight_lt m I w d F hvertex hF c hc
  change (if c ∈ actualInitialDiagram m I then 0 else actualDivisionCoefficient m I F c)=0
  split_ifs <;> simp only [hz]

/-- Actual ideal members retain the genuine WHOLE division identity and the SAME centre-weight coefficient bounds. -/
theorem actual_formal_ideal_member_weighted_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hmem : F ∈ I)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (actualVertexSeries m I a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0) :
    F=∑ a : actualInitialVertices m I, actualFormalQuotient m I F a*actualVertexSeries m I a ∧
      ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
        MvPowerSeries.coeff b (actualFormalQuotient m I F a) ≠ 0 →
          d-Finsupp.weight w (a : Fin n →₀ ℕ) ≤ Finsupp.weight w b := by
  refine ⟨actual_formal_ideal_member_division m I F hmem,?_⟩
  intro a b hb
  have hle : d ≤ Finsupp.weight w b+Finsupp.weight w (a : Fin n →₀ ℕ) := by
    by_contra h
    exact hb (actualFormalQuotient_coefficient_weight_bound m I w d F hvertex hF a b (lt_of_not_ge h))
  omega

/-- Actual constant coordinate weights agree with the ORIGINAL total exponent degree. -/
theorem actualWeight_one (b : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ : Fin n => 1) b=normalExponentDegree b := by
  rw [← Finsupp.degree_eq_weight_one,Finsupp.degree_eq_sum]
  rfl

/-- The genuine degree-lex vertex series internally have the required ACTUAL total-degree compatibility. -/
theorem actualVertexSeries_total_degree_compatible (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) (b : Fin n →₀ ℕ)
    (hb : Finsupp.weight (fun _ : Fin n => 1) b <
      Finsupp.weight (fun _ : Fin n => 1) (a : Fin n →₀ ℕ)) :
    MvPowerSeries.coeff b (actualVertexSeries MonomialOrder.degLex I a)=0 := by
  apply actualVertexSeries_coefficient_lower
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa only [ofDegLex_toDegLex,← Finsupp.degree_eq_weight_one] using hb

/-- EVERY actual degree-lex division preserves the GENUINE formal maximal filtration internally. -/
theorem actual_formal_degreelex_division_maximal_filtration (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (d : ℕ) (hF : F ∈ genuineFormalVariables n ^ d) :
    actualFormalRemainder MonomialOrder.degLex I F ∈ genuineFormalVariables n ^ d ∧
      ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ b : Fin n →₀ ℕ,
        normalExponentDegree b+normalExponentDegree (a : Fin n →₀ ℕ) < d →
          MvPowerSeries.coeff b (actualFormalQuotient MonomialOrder.degLex I F a)=0 := by
  have hcoeff := (mem_genuineFormalVariables_pow_iff_coefficients_zero n d F).mp hF
  have hw : ∀ b : Fin n →₀ ℕ, Finsupp.weight (fun _ : Fin n => 1) b < d →
      MvPowerSeries.coeff b F=0 := by simpa only [actualWeight_one] using hcoeff
  constructor
  · apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n d _).mpr
    intro b hb
    apply actualFormalRemainder_coefficient_weight_bound MonomialOrder.degLex I
      (fun _ => 1) d F (actualVertexSeries_total_degree_compatible I) hw b
    rwa [actualWeight_one]
  · intro a b hb
    apply actualFormalQuotient_coefficient_weight_bound MonomialOrder.degLex I
      (fun _ => 1) d F (actualVertexSeries_total_degree_compatible I) hw a b
    simpa only [actualWeight_one] using hb

end
end Hironaka.HironakaActualFormalWeightedDivision
