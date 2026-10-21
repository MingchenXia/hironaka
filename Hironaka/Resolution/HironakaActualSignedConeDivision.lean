/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReducedBasisDivision
import Hironaka.Resolution.HironakaActualFormalMonomialBlowupReflection

/-!
# Genuine signed support cones under actual whole owner division

The existing well-founded coefficient recursion preserves additive integer
weights, including the actual tangent-scaling blowup cone. Quotient and
remainder support bounds are outputs. Producing a suitable geometric image
family and analytic inverse-image convergence remains separate.
Blueprint: `hironaka-actual-signed-cone-division-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualSignedConeDivision
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedBasisDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalMonomialBlowupReflection
variable {n : ℕ}

/-- The genuine recursion preserves every actual weight compatible with its true vertex coefficients. -/
theorem familyDivisionCoefficient_eq_zero_of_signed_weight_lt (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (ν : (Fin n →₀ ℕ) →+ ℤ) (d : ℤ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      ν b < ν (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, ν c < d → MvPowerSeries.coeff c F=0) :
    ∀ c : Fin n →₀ ℕ, ν c < d → familyDivisionCoefficient m I B F c=0 := by
  intro c
  have hwf := InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))
  induction c using hwf.induction with
  | h c ih =>
      intro hc
      rw [familyDivisionCoefficient_eq,hF c hc]
      have ht : familyDivisionTail m I B F c=0 := by
        unfold familyDivisionTail
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro p hp
        by_cases hs : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c
        · rw [if_pos hs]
          split_ifs
          · by_cases hz : MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)=0
            · rw [hz,mul_zero]
            · have hle : ν (a : Fin n →₀ ℕ) ≤ ν p.2 := by
                by_contra h
                exact hz (hvertex a p.2 (lt_of_not_ge h))
              have he : ν p.1+ν p.2=ν c := by
                rw [← map_add,Finset.mem_antidiagonal.mp hp]
              have hsmall : ν (p.1+(a : Fin n →₀ ℕ)) < d := by
                rw [map_add]
                exact lt_of_le_of_lt (calc ν p.1 + ν (a : Fin n →₀ ℕ) ≤ ν p.1 + ν p.2 := by omega
                        _ = ν c := he) hc
              rw [ih _ hs hsmall,zero_mul]
          · rfl
        · rw [if_neg hs]
      rw [ht,sub_self]

/-- The SAME genuine quotient series have the actual shifted weight bounds. -/
theorem familyFormalQuotient_signed_weight_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (ν : (Fin n →₀ ℕ) →+ ℤ) (d : ℤ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      ν b < ν (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, ν c < d → MvPowerSeries.coeff c F=0)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : ν b+ν (a : Fin n →₀ ℕ) < d) :
    MvPowerSeries.coeff b (familyFormalQuotient m I B F a)=0 := by
  have hz := familyDivisionCoefficient_eq_zero_of_signed_weight_lt m I B ν d F hvertex hF
    (b+(a : Fin n →₀ ℕ)) (by rwa [map_add])
  change (if HironakaActualFormalVertexDivision.actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a then
    familyDivisionCoefficient m I B F (b+(a : Fin n →₀ ℕ)) else 0)=0
  split_ifs <;> simp only [hz]

/-- The ACTUAL remainder retains the numerator's compatible weight filtration. -/
theorem familyFormalRemainder_signed_weight_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (ν : (Fin n →₀ ℕ) →+ ℤ) (d : ℤ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      ν b < ν (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, ν c < d → MvPowerSeries.coeff c F=0)
    (c : Fin n →₀ ℕ) (hc : ν c < d) :
    MvPowerSeries.coeff c (familyFormalRemainder m I B F)=0 := by
  have hz := familyDivisionCoefficient_eq_zero_of_signed_weight_lt m I B ν d F hvertex hF c hc
  change (if c ∈ actualInitialDiagram m I then 0 else familyDivisionCoefficient m I B F c)=0
  split_ifs <;> simp only [hz]


/-- The literal SIGNED chart exponent: exceptional exponent minus selected nonpivot weight. -/
def actualBlowupConeWeight (A : Set (Fin n)) (e : Fin n) : (Fin n →₀ ℕ) →+ ℤ where
  toFun a := (a e : ℤ)-(Finsupp.weight (actualCoordinateWeight (A\{e})) a : ℤ)
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply,map_add,Nat.cast_add];ring

private theorem actualBlowupConeWeight_image (A : Set (Fin n)) (e : Fin n) (a : Fin n →₀ ℕ) :
    actualBlowupConeWeight A e (actualMonomialBlowupExponent A e a)=(a e : ℤ) := by
  change (actualMonomialBlowupExponent A e a e : ℤ)-
    (Finsupp.weight (actualCoordinateWeight (A\{e})) (actualMonomialBlowupExponent A e a) : ℤ)=_
  rw [actualMonomialBlowupExponent_other_weight]
  change ((a e+(Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) a)) e : ℕ) : ℤ)-_= _
  rw [Finsupp.single_eq_same]
  omega

/-- EVERY genuine zero-direction chart image internally has no coefficient outside its signed cone. -/
theorem actualFormalBlowup_zero_coefficient_outside_cone (A : Set (Fin n)) (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) (hα : actualBlowupConeWeight A e α<0) :
    MvPowerSeries.coeff α (actualFormalBlowup A e (fun _ => 0) F)=0 := by
  rw [actualFormalBlowup,MvPowerSeries.substAlgHom_apply,MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A e (fun _ => 0))) F _]
  apply finsum_eq_zero_of_forall_eq_zero
  intro a
  rw [actualFormalBlowup_zero_coordinate_product,MvPowerSeries.coeff_monomial,if_neg]
  · simp
  · intro h
    have he := actualBlowupConeWeight_image A e a
    rw [←h] at he
    have hn : (0 : ℤ)≤(a e : ℤ) := by omega
    omega

/-- The SAME prescribed actual image family has genuine whole owner quotients/remainder inside the chart cone. -/
theorem actual_image_family_division_cone (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (A : Set (Fin n)) (e : Fin n)
    (G : actualInitialVertices m I → MvPowerSeries (Fin n) ℂ)
    (hB : ∀ a,familyVertexSeries m I B a=actualFormalBlowup A e (fun _ => 0) (G a))
    (ha : ∀ a : actualInitialVertices m I,actualBlowupConeWeight A e a.val=0)
    (F : MvPowerSeries (Fin n) ℂ) :
    (∀ (a : actualInitialVertices m I) (β : Fin n →₀ ℕ),actualBlowupConeWeight A e β<0 →
      MvPowerSeries.coeff β (familyFormalQuotient m I B (actualFormalBlowup A e (fun _ => 0) F) a)=0) ∧
    ∀ β : Fin n →₀ ℕ,actualBlowupConeWeight A e β<0 →
      MvPowerSeries.coeff β (familyFormalRemainder m I B (actualFormalBlowup A e (fun _ => 0) F))=0 := by
  have hvertex (a : actualInitialVertices m I) (β : Fin n →₀ ℕ)
      (hβ : actualBlowupConeWeight A e β<actualBlowupConeWeight A e a.val) :
      MvPowerSeries.coeff β (familyVertexSeries m I B a)=0 := by
    rw [hB a]
    apply actualFormalBlowup_zero_coefficient_outside_cone
    rwa [ha a] at hβ
  have hF := actualFormalBlowup_zero_coefficient_outside_cone A e F
  refine ⟨?_,?_⟩
  · intro a β hβ
    apply familyFormalQuotient_signed_weight_bound m I B (actualBlowupConeWeight A e) 0 _ hvertex hF
    simpa only [ha a,add_zero] using hβ
  · intro β hβ
    exact familyFormalRemainder_signed_weight_bound m I B (actualBlowupConeWeight A e) 0 _ hvertex hF β hβ

end
end Hironaka.HironakaActualSignedConeDivision
