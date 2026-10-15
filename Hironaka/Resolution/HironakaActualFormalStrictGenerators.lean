/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalBlowupAllDirections

/-! The literal BM97 formal strict ideal from true maximal center orders, and its internally proved finite strict generators. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalStrictGenerators
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
variable {n : ℕ}

private theorem exists_nonzero_center_weight (A : Set (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) :
    ∃ d : ℕ, ∃ a : Fin n →₀ ℕ, MvPowerSeries.coeff a F ≠ 0 ∧
      Finsupp.weight (actualCoordinateWeight A) a=d := by
  have ha : ∃ a, MvPowerSeries.coeff a F ≠ 0 := by
    by_contra h
    apply hne
    apply MvPowerSeries.ext
    intro a
    rw [map_zero]
    exact not_not.mp (fun hne => h ⟨a,hne⟩)
  obtain ⟨a,ha⟩ := ha
  exact ⟨_,a,ha,rfl⟩

/-- The genuine finite center order is internally the least actual nonzero coefficient weight. -/
def actualFormalCenterOrder (A : Set (Fin n)) (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) : ℕ :=
  Nat.find (exists_nonzero_center_weight A F hne)

/-- The actual least center weight is attained by a true nonzero original coefficient. -/
theorem actualFormalCenterOrder_witness (A : Set (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (hne : F ≠ 0) :
    ∃ a : Fin n →₀ ℕ, MvPowerSeries.coeff a F ≠ 0 ∧
      Finsupp.weight (actualCoordinateWeight A) a=actualFormalCenterOrder A F hne :=
  Nat.find_spec (exists_nonzero_center_weight A F hne)

/-- EVERY true nonzero original coefficient has at least the internally constructed actual center order. -/
theorem actualFormalCenterOrder_le_weight (A : Set (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (hne : F ≠ 0) (a : Fin n →₀ ℕ) (ha : MvPowerSeries.coeff a F ≠ 0) :
    actualFormalCenterOrder A F hne ≤ Finsupp.weight (actualCoordinateWeight A) a :=
  Nat.find_min' (exists_nonzero_center_weight A F hne) ⟨a,ha,rfl⟩

/-- BOTH genuine center-power directions prove that the actual finite center order is the LARGEST true power membership. -/
theorem mem_coordinate_power_iff_le_actualFormalCenterOrder (A : Set (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) (d : ℕ) :
    F ∈ actualFormalCoordinateIdeal n A ^ d ↔ d ≤ actualFormalCenterOrder A F hne := by
  constructor
  · intro hF
    obtain ⟨a,ha,hw⟩ := actualFormalCenterOrder_witness A F hne
    by_contra hd
    exact ha ((mem_actualFormalCoordinateIdeal_pow_iff A d F).mp hF a (by rw [hw]; omega))
  · intro hd
    apply (mem_actualFormalCoordinateIdeal_pow_iff A d F).mpr
    intro a ha
    by_contra hne'
    have hw := actualFormalCenterOrder_le_weight A F hne a hne'
    omega

/-- Every actual nonzero series belongs to its TRUE internally computed maximal center power. -/
theorem mem_actualFormalCenterOrder_power (A : Set (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (hne : F ≠ 0) : F ∈ actualFormalCoordinateIdeal n A ^ actualFormalCenterOrder A F hne :=
  (mem_coordinate_power_iff_le_actualFormalCenterOrder A F hne _).mpr le_rfl

/-- The SAME actual source series does not belong to the next true center power. -/
theorem not_mem_actualFormalCenterOrder_succ_power (A : Set (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) :
    F ∉ actualFormalCoordinateIdeal n A ^ (actualFormalCenterOrder A F hne+1) := by
  rw [mem_coordinate_power_iff_le_actualFormalCenterOrder A F hne]
  omega

/-- Real monic vertex coefficients and explicit true power membership internally identify the SAME vertex's center order. -/
theorem actualFormalCenterOrder_vertex (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (a : actualInitialVertices m I)
    (hvertex : actualVertexSeries m I a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) :
    actualFormalCenterOrder A (actualVertexSeries m I a) (actualVertexSeries_spec m I a).2.choose=
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ) := by
  apply le_antisymm
  · apply actualFormalCenterOrder_le_weight
    rw [actualVertexSeries_coefficient]
    exact one_ne_zero
  · exact (mem_coordinate_power_iff_le_actualFormalCenterOrder A _ _ _).mp hvertex

/-- The true normalized zero original member contributes only zero. -/
theorem actualNormalizedFormalMember_zero (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (d : ℕ) (hF : (0 : MvPowerSeries (Fin n) ℂ) ∈ actualFormalCoordinateIdeal n A ^ d) :
    actualNormalizedFormalMember A e he b d 0 hF=0 := by
  symm
  apply actualNormalizedFormalMember_unique A e he b d 0 hF 0
  simp

/-- Actual exceptional-product identities and true domain cancellation compare EVERY lower normalization to the SAME higher normalization. -/
theorem actualNormalizedFormalMember_lower_order (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (q d : ℕ) (hqd : q ≤ d) (F : MvPowerSeries (Fin n) ℂ)
    (hq : F ∈ actualFormalCoordinateIdeal n A ^ q) (hd : F ∈ actualFormalCoordinateIdeal n A ^ d) :
    actualNormalizedFormalMember A e he b q F hq=
      (MvPowerSeries.X e)^(d-q)*actualNormalizedFormalMember A e he b d F hd := by
  symm
  apply actualNormalizedFormalMember_unique A e he b q F hq
  rw [← mul_assoc,← pow_add,Nat.add_sub_of_le hqd]
  exact actualNormalizedFormalMember_spec A e he b d F hd

/-- The EXACT BM97 p268 formal strict ideal: normalized images of ALL actual nonzero original members at their true maximal center order. -/
def actualFormalStrictTransform (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span {G | ∃ (F : MvPowerSeries (Fin n) ℂ) (_hI : F ∈ I) (hne : F ≠ 0),
    G=actualNormalizedFormalMember A e he b (actualFormalCenterOrder A F hne) F
      (mem_actualFormalCenterOrder_power A F hne)}

/-- BOTH WHOLE ideal inclusions identify the EXACT source formal strict ideal with all normalized original members. -/
theorem actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) :
    actualFormalStrictTransform I A e he b=actualNormalizedOriginalMemberIdeal I A e he b := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro G ⟨F,hI,hne,rfl⟩
    exact Ideal.subset_span ⟨_,F,hI,mem_actualFormalCenterOrder_power A F hne,rfl⟩
  · apply Ideal.span_le.mpr
    rintro G ⟨d,F,hI,hF,rfl⟩
    by_cases hne : F=0
    · subst F
      rw [actualNormalizedFormalMember_zero]
      exact Ideal.zero_mem _
    · have hd := (mem_coordinate_power_iff_le_actualFormalCenterOrder A F hne d).mp hF
      rw [actualNormalizedFormalMember_lower_order A e he b d (actualFormalCenterOrder A F hne) hd F hF
        (mem_actualFormalCenterOrder_power A F hne)]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨F,hI,hne,rfl⟩)

/-- GENUINE finite strict generators in the EXACT source formal ideal, from actual whole division and explicit source vertex powers. -/
theorem actualFormalStrictTransform_eq_vertex_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, actualVertexSeries m I a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) :
    actualFormalStrictTransform I A e he b=
      Ideal.span (range (actualNormalizedFormalVertex m I A e he b hv)) := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  exact actualNormalizedOriginalMemberIdeal_eq_vertex_span m I A e he b hv

end
end Hironaka.HironakaActualFormalStrictGenerators
