import Hironaka.Geometry.MonomialBlowupTowerRegular

/-! The last actual continuation blowup is covered by its finished coordinate chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerBoundaryLastChart

open Algebra.NodeBlowupChart MonomialBlowupIteration PrincipalBlowup

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A] (t : A) [Fact (t ≠ 0)]

local instance : Fact ((1 : A) ≠ 0) := ⟨one_ne_zero⟩

/-- Canonical identification of the literal node coefficients `t*1` and `t`. -/
def coefficientOneEquiv : Node A (t * 1) ≃ₐ[A] Node A t :=
  Ideal.quotientEquivAlgOfEq A (by rw [mul_one])

theorem coefficientOneEquiv_eq_originalMap :
    (coefficientOneEquiv t).toAlgHom = uChartOriginalMap t 1 := by
  apply Ideal.Quotient.algHom_ext
  ext j
  fin_cases j
  · change coefficientOneEquiv t (coordinate (t * 1) 0) =
      uChartOriginalMap t 1 (coordinate (t * 1) 0)
    rw [uChartOriginalMap_coordinate0]
    exact Ideal.quotientEquivAlgOfEq_mk _ _ _
  · change coefficientOneEquiv t (coordinate (t * 1) 1) =
      uChartOriginalMap t 1 (coordinate (t * 1) 1)
    rw [uChartOriginalMap_coordinate1]
    have h : coefficientOneEquiv t (coordinate (t * 1) 1) = coordinate t 1 :=
      Ideal.quotientEquivAlgOfEq_mk _ _ _
    simpa only [map_one, mul_one] using h

omit [IsDomain A] [Fact (t ≠ 0)] in
/-- The actual terminal continuation centre is intrinsically principal. -/
theorem centerIdeal_one : centerIdeal t (1 : A) =
    Ideal.span {coordinate (t * 1) 0} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | rfl
    · exact Ideal.mem_span_singleton_self _
    · apply Ideal.mem_span_singleton.mpr
      refine ⟨coordinate (t * 1) 1, ?_⟩
      have h : coordinate (t * 1) 0 * coordinate (t * 1) 1 =
          algebraMap A (Node A (t * 1)) (t * 1) :=
        Algebra.NodeDomain.nodeCoordinateProduct (t * 1)
      simpa only [map_mul, map_one, mul_one] using h.symm
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.subset_span (Set.mem_insert _ _)

instance originalMap_isIso :
    IsIso (Spec.map (CommRingCat.ofHom (uChartOriginalMap t (1 : A)).toRingHom)) := by
  rw [← coefficientOneEquiv_eq_originalMap]
  change IsIso (Scheme.Spec.mapIso
    (coefficientOneEquiv t).toRingEquiv.toCommRingCatIso.op).hom
  infer_instance

instance structure_one_isIso : IsIso (affineBlowupStructure (centerIdeal t (1 : A))) := by
  have h : IsIso (affineBlowupStructure (Ideal.span {coordinate (t * 1) 0})) :=
    affineBlowupStructure_span_singleton_isIso _
      (Algebra.NodeDomain.nodeCoordinate_ne_zero (t * 1)
        (mul_ne_zero (Fact.out : t ≠ 0) one_ne_zero) 0)
  rw [centerIdeal_one]
  exact h

/-- The literal native coordinate-chart map in the last step is an actual isomorphism. -/
instance lastUChart_isIso : IsIso (uChartInclusion t (1 : A)) := by
  have h : IsIso (uChartInclusion t (1 : A) ≫ affineBlowupStructure (centerIdeal t 1)) := by
    rw [uChartInclusion_structure]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (affineBlowupStructure (centerIdeal t 1))

theorem lastUChart_opensRange : (uChartInclusion t (1 : A)).opensRange = ⊤ :=
  Scheme.Hom.opensRange_of_isIso _

end Hironaka.Geometry.MonomialBlowupTowerBoundaryLastChart
