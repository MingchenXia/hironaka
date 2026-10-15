/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalStrictGenerators
import Hironaka.Resolution.HironakaActualReducedBasisDivision
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower

/-! Real original coefficient cosupport produces entire reduced formal strict generators. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCoefficientReducedStrictGenerators
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualReducedBasisDivision
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualCoefficientPresentationCentrePower
  OkaRelationSheaf IdealWeightPowers GermIdealOrder
variable {n : ℕ}

/-- The same actual reduced member has its literal vertex centre order, from true power membership. -/
theorem actualFormalCenterOrder_reduced_vertex (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (a : actualInitialVertices m I)
    (ha : actualReducedVertexSeries m I a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) :
    actualFormalCenterOrder A (actualReducedVertexSeries m I a)
      (actualReducedVertexSeries_ne_zero m I a) =
        Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ) := by
  apply le_antisymm
  · apply actualFormalCenterOrder_le_weight
    rw [actualReducedVertexSeries_coefficient]
    exact one_ne_zero
  · exact (mem_coordinate_power_iff_le_actualFormalCenterOrder A _ _ _).mp ha

/-- Actual exceptional division of the SAME reduced member at its true vertex centre power. -/
def actualNormalizedReducedFormalVertex (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hB : ∀ a : actualInitialVertices m I, actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  actualNormalizedFormalMember A e he b _ (actualReducedVertexSeries m I a) (hB a)

/-- EVERY normalized original member lies in the whole actual normalized REDUCED basis ideal. -/
theorem actualNormalizedFormalMember_mem_reduced_vertex_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hB : ∀ a : actualInitialVertices m I, actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hI : F ∈ I)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ q) :
    actualNormalizedFormalMember A e he b q F hF ∈
      Ideal.span (range (actualNormalizedReducedFormalVertex m I A e he b hB)) := by
  let w (a : actualInitialVertices m I) := Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)
  have hd := actual_reduced_basis_entire_filtered_division m I A q F hI hF hB
  let Q (a : actualInitialVertices m I) := familyFormalQuotient m I (actualReducedVertexFamily m I) F a
  let Qb (a : actualInitialVertices m I) := actualNormalizedFormalMember A e he b (q-w a) (Q a) (hd.2 a)
  let fb := actualNormalizedReducedFormalVertex m I A e he b hB
  have ht (a : actualInitialVertices m I) :
      actualFormalBlowup A e b (Q a*actualReducedVertexSeries m I a) =
        (MvPowerSeries.X e)^q*((MvPowerSeries.X e)^(w a-q)*Qb a*fb a) := by
    rw [map_mul,← actualNormalizedFormalMember_spec A e he b (q-w a) (Q a) (hd.2 a),
      ← actualNormalizedFormalMember_spec A e he b (w a) (actualReducedVertexSeries m I a) (hB a)]
    change ((MvPowerSeries.X e)^(q-w a)*Qb a)*((MvPowerSeries.X e)^(w a)*fb a)=_
    calc
      _=(MvPowerSeries.X e)^((q-w a)+w a)*(Qb a*fb a) := by rw [pow_add]; ring
      _=(MvPowerSeries.X e)^q*((MvPowerSeries.X e)^(w a-q)*Qb a*fb a) := by
        rw [show (q-w a)+w a=q+(w a-q) by omega,pow_add]
        ring
  have hs : actualNormalizedFormalMember A e he b q F hF =
      ∑ a : actualInitialVertices m I, (MvPowerSeries.X e)^(w a-q)*Qb a*fb a := by
    apply mul_left_cancel₀ (pow_ne_zero q (actualFormalExceptional_ne_zero e))
    calc
      _=actualFormalBlowup A e b F := actualNormalizedFormalMember_spec A e he b q F hF
      _=actualFormalBlowup A e b (∑ a : actualInitialVertices m I, Q a*actualReducedVertexSeries m I a) :=
        congrArg (actualFormalBlowup A e b) hd.1
      _=∑ a : actualInitialVertices m I, actualFormalBlowup A e b (Q a*actualReducedVertexSeries m I a) :=
        map_sum _ _ _
      _=_ := by simp_rw [ht]; exact (Finset.mul_sum _ _ _).symm
  rw [hs]
  apply Ideal.sum_mem
  intro a _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a,rfl⟩)

/-- BOTH WHOLE ideal inclusions identify the genuine source formal strict ideal with the actual reduced normalized generators. -/
theorem actualFormalStrictTransform_eq_reduced_vertex_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hB : ∀ a : actualInitialVertices m I, actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) :
    actualFormalStrictTransform I A e he b =
      Ideal.span (range (actualNormalizedReducedFormalVertex m I A e he b hB)) := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro G ⟨q,F,hI,hF,rfl⟩
    exact actualNormalizedFormalMember_mem_reduced_vertex_span m I A e he b hB q F hI hF
  · apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    exact Ideal.subset_span ⟨_,actualReducedVertexSeries m I a,actualReducedVertexSeries_mem m I a,hB a,rfl⟩

/-- The actual ambient centre of the literal coefficient presentation coordinates `(u,y,z)`. -/
def actualCoefficientCentreVariables (k s t : ℕ) : Set (Fin ((k+s)+t)) :=
  actualPresentationCentreVariables (actualTangentCentreVariables k s)

/-- Its actual vertex weight uses the SAME selected coordinate indices. -/
def actualCoefficientCentreVertexWeight (k s t : ℕ) (a : Fin ((k+s)+t) →₀ ℕ) : ℕ :=
  Finsupp.weight (actualCoordinateWeight (actualCoefficientCentreVariables k s t)) a

/-- Genuine original low coefficient data, with no centre power, quotient or strict-generation certificate. -/
structure ActualReducedCoefficientPresentation (k s t : ℕ)
    (m : MonomialOrder (Fin ((k+s)+t))) (I : Ideal (MvPowerSeries (Fin ((k+s)+t)) ℂ)) where
  coefficient : actualInitialVertices m I → (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ
  holomorphic : ∀ a γ, HolAt (coefficient a γ) 0
  ideal : actualInitialVertices m I → (Fin t →₀ ℕ) → GermIdeal (k+s) (ComplexModel (k+s))
  coherent : ∀ (a : actualInitialVertices m I) γ, actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a →
    (ideal a γ).IsCoherent
  member : ∀ (a : actualInitialVertices m I) γ, actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a →
    (ideal a γ).mem 0 (coefficient a γ)
  centre_smooth : IsClosedSubmanifold (k+s) (complexCoordinatePlane (k+s) k)
  centre_cosupport : ∀ (a : actualInitialVertices m I) γ, actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a →
    complexCoordinatePlane (k+s) k ⊆ cosupport (k+s) univ (ideal a γ)
      (actualCoefficientCentreVertexWeight k s t a-actualNormalDegree γ)
  coefficient_eq : ∀ (a : actualInitialVertices m I) γ, actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a →
    actualFormalNormalCoefficient (actualReducedVertexSeries m I a) γ =
      actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk (coefficient a γ) (holomorphic a γ))

/-- Actual original coefficient cosupport INTERNALLY produces every genuine reduced member's entire centre power. -/
theorem actualReducedCoefficientPresentation_centre_powers (k s t : ℕ)
    (m : MonomialOrder (Fin ((k+s)+t))) (I : Ideal (MvPowerSeries (Fin ((k+s)+t)) ℂ))
    (P : ActualReducedCoefficientPresentation k s t m I) (a : actualInitialVertices m I) :
    actualReducedVertexSeries m I a ∈ actualFormalCoordinateIdeal ((k+s)+t)
      (actualCoefficientCentreVariables k s t) ^ actualCoefficientCentreVertexWeight k s t a := by
  exact mem_actualPresentationCentre_power_of_original_coefficient_cosupport k s t
    (actualCoefficientCentreVertexWeight k s t a) (actualReducedVertexSeries m I a)
    (P.coefficient a) (P.holomorphic a) (P.ideal a) (P.coherent a) (P.member a)
    P.centre_smooth (P.centre_cosupport a) (P.coefficient_eq a)

/-- Original geometric coefficient data supply finite WHOLE strict generators and their actual exceptional identities in EVERY real chart. -/
theorem exists_actual_reduced_strict_generators_of_original_coefficients (k s t : ℕ)
    (m : MonomialOrder (Fin ((k+s)+t))) (I : Ideal (MvPowerSeries (Fin ((k+s)+t)) ℂ))
    (P : ActualReducedCoefficientPresentation k s t m I)
    (e : Fin ((k+s)+t)) (he : e ∈ actualCoefficientCentreVariables k s t)
    (b : Fin ((k+s)+t) → ℂ) :
    ∃ G : actualInitialVertices m I → MvPowerSeries (Fin ((k+s)+t)) ℂ,
      actualFormalStrictTransform I (actualCoefficientCentreVariables k s t) e he b = Ideal.span (range G) ∧
      ∀ a : actualInitialVertices m I,
        (MvPowerSeries.X e)^actualCoefficientCentreVertexWeight k s t a * G a =
          actualFormalBlowup (actualCoefficientCentreVariables k s t) e b (actualReducedVertexSeries m I a) := by
  let hB := actualReducedCoefficientPresentation_centre_powers k s t m I P
  let G := actualNormalizedReducedFormalVertex m I (actualCoefficientCentreVariables k s t) e he b hB
  refine ⟨G,actualFormalStrictTransform_eq_reduced_vertex_span m I _ e he b hB,?_⟩
  intro a
  exact actualNormalizedFormalMember_spec _ e he b _ (actualReducedVertexSeries m I a) (hB a)

end
end Hironaka.HironakaActualCoefficientReducedStrictGenerators
