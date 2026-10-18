/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReducedBasisDivision
import Hironaka.Resolution.HironakaActualFormalStrictGenerators

/-! Entire actual source strict ideals for any literal centre-compatible monic vertex family. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalFamilyStrictGenerators
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedBasisDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators
variable {n : ℕ}

/-- Actual vertex normalized generators use the literal source vertex-power membership only. -/
def familyNormalizedFormalVertex (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, familyVertexSeries m I B a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  actualNormalizedFormalMember A e he b _ (familyVertexSeries m I B a) (hv a)

/-- EVERY normalized original member lies in the genuine finite normalized vertex ideal. -/
theorem familyNormalizedFormalMember_mem_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, familyVertexSeries m I B a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hI : F ∈ I)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) :
    actualNormalizedFormalMember A e he b d F hF ∈
      Ideal.span (range (familyNormalizedFormalVertex m I B A e he b hv)) := by
  let w (a : actualInitialVertices m I) := Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)
  have hd : F=∑ a : actualInitialVertices m I,
      familyFormalQuotient m I B F a*familyVertexSeries m I B a ∧
      ∀ a : actualInitialVertices m I, familyFormalQuotient m I B F a ∈
        actualFormalCoordinateIdeal n A ^ (d-w a) :=
    ⟨family_formal_ideal_member_division m I B F hI,
      familyFormalQuotient_mem_coordinate_power m I B A d F hv hF⟩
  let Q (a : actualInitialVertices m I) := familyFormalQuotient m I B F a
  let Qb (a : actualInitialVertices m I) := actualNormalizedFormalMember A e he b (d-w a) (Q a) (hd.2 a)
  let fb := familyNormalizedFormalVertex m I B A e he b hv
  have ht (a : actualInitialVertices m I) :
      actualFormalBlowup A e b (Q a*familyVertexSeries m I B a)=
        (MvPowerSeries.X e)^d*((MvPowerSeries.X e)^(w a-d)*Qb a*fb a) := by
    rw [map_mul,← actualNormalizedFormalMember_spec A e he b (d-w a) (Q a) (hd.2 a),
      ← actualNormalizedFormalMember_spec A e he b (w a) (familyVertexSeries m I B a) (hv a)]
    change ((MvPowerSeries.X e)^(d-w a)*Qb a)*((MvPowerSeries.X e)^(w a)*fb a)=_
    calc
      _=(MvPowerSeries.X e)^((d-w a)+w a)*(Qb a*fb a) := by rw [pow_add]; ring
      _=(MvPowerSeries.X e)^d*((MvPowerSeries.X e)^(w a-d)*Qb a*fb a) := by
        rw [show (d-w a)+w a=d+(w a-d) by omega,pow_add]
        ring
  have hs : actualNormalizedFormalMember A e he b d F hF=
      ∑ a : actualInitialVertices m I, (MvPowerSeries.X e)^(w a-d)*Qb a*fb a := by
    apply mul_left_cancel₀ (pow_ne_zero d (actualFormalExceptional_ne_zero e))
    calc
      _=actualFormalBlowup A e b F := actualNormalizedFormalMember_spec A e he b d F hF
      _=actualFormalBlowup A e b (∑ a : actualInitialVertices m I, Q a*familyVertexSeries m I B a) :=
        congrArg (actualFormalBlowup A e b) hd.1
      _=∑ a : actualInitialVertices m I, actualFormalBlowup A e b (Q a*familyVertexSeries m I B a) :=
        map_sum _ _ _
      _=_ := by simp_rw [ht]; exact (Finset.mul_sum _ _ _).symm
  rw [hs]
  apply Ideal.sum_mem
  intro a _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a,rfl⟩)

/-- Every true normalized family generator and every original member give BOTH entire ideal inclusions. -/
theorem actualFormalStrictTransform_eq_family_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, familyVertexSeries m I B a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val) :
    actualFormalStrictTransform I A e he b=
      Ideal.span (range (familyNormalizedFormalVertex m I B A e he b hv)) := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro G ⟨d,F,hI,hF,rfl⟩
    exact familyNormalizedFormalMember_mem_span m I B A e he b hv d F hI hF
  · apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    exact Ideal.subset_span ⟨_,familyVertexSeries m I B a,B.mem a,hv a,rfl⟩

end
end Hironaka.HironakaActualFormalFamilyStrictGenerators
