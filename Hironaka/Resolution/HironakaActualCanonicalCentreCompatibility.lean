/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReducedBasisDivision

/-! Literal canonical centre compatibility follows from any genuine compatible monic family. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalCentreCompatibility
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalCoordinatePowerDivision HironakaActualReducedFormalStandardBasis
  HironakaActualReducedBasisDivision
variable {n : ℕ}

/-- The actual canonical remainder preserves the whole centre filtration whenever any true monic family does. -/
theorem actualFormalRemainder_mem_coordinate_power_of_family (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (A : Set (Fin n))
    (hB : ∀ a : actualInitialVertices m I, familyVertexSeries m I B a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ q) :
    actualFormalRemainder m I F ∈ actualFormalCoordinateIdeal n A ^ q := by
  rw [← familyFormalRemainder_eq_canonical m I B F]
  apply (mem_actualFormalCoordinateIdeal_pow_iff A q _).mpr
  exact familyFormalRemainder_coefficient_weight_bound m I B (actualCoordinateWeight A) q F
    (fun a => (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mp (hB a))
    ((mem_actualFormalCoordinateIdeal_pow_iff A q F).mp hF)

/-- The actual canonical reduced members inherit genuine centre powers without any convergence assumption. -/
theorem actualReducedVertexSeries_mem_coordinate_power_of_family (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (A : Set (Fin n))
    (hB : ∀ a : actualInitialVertices m I, familyVertexSeries m I B a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val)
    (a : actualInitialVertices m I) :
    actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val := by
  have hM : MvPowerSeries.monomial a.val (1 : ℂ) ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val := by
    apply (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mpr
    intro c hc
    have hne : c ≠ a.val := by
      intro he
      rw [he] at hc
      exact (lt_irrefl _ hc)
    simp only [MvPowerSeries.coeff_monomial,if_neg hne]
  exact Ideal.sub_mem _ hM (actualFormalRemainder_mem_coordinate_power_of_family m I B A hB _ _ hM)

/-- Canonical reduced compatibility and existence of a true compatible monic family are equivalent. -/
theorem actualReducedVertexCentreCompatibility_iff_exists_family (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) :
    (∀ a : actualInitialVertices m I, actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val) ↔
    ∃ B : ActualMonicVertexFamily m I, ∀ a : actualInitialVertices m I,
      familyVertexSeries m I B a ∈
        actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val := by
  constructor
  · intro h
    exact ⟨actualReducedVertexFamily m I,h⟩
  · rintro ⟨B,hB⟩
    exact actualReducedVertexSeries_mem_coordinate_power_of_family m I B A hB

end
end Hironaka.HironakaActualCanonicalCentreCompatibility
