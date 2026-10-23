import DeJongAlterations.Geometry.SteinGenericFiber
import DeJongAlterations.Geometry.FiniteBirationalNormalGenericBaseChange

/-!
# Actual relative and absolute dimensions of finite-type varieties

The original structural field maps and the original morphism's generic
stalk map form the genuine scalar tower. No coefficient compatibility
or dimension comparison certificate is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.VarietyFunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (p : S ⟶ Spec (.of k)) (f : X ⟶ S) [IsDominant f]

/-- The native structural coefficient fields and the actual generic map form the original tower. -/
theorem functionFieldScalarTower :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    letI := SeparableGenericSmoothness.functionFieldAlgebra (f ≫ p)
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    IsScalarTower k S.functionField X.functionField := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := SeparableGenericSmoothness.functionFieldAlgebra (f ≫ p)
  let := FiniteBirationalNormal.functionFieldAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  have hcat : CommRingCat.ofHom (algebraMap k X.functionField) =
      CommRingCat.ofHom ((algebraMap S.functionField X.functionField).comp
        (algebraMap k S.functionField)) := by
    apply Spec.map_injective
    rw [SteinGenericFiber.structureFieldMap_generic (f ≫ p)]
    change X.fromSpecStalk (genericPoint X) ≫ f ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k S.functionField) ≫
        NormalizationInExtension.functionFieldMap f)
    rw [Spec.map_comp, SteinGenericFiber.structureFieldMap_generic p,
      FiniteBirationalNormal.functionFieldMap_fromSpecStalk_assoc]
  exact congrArg CommRingCat.Hom.hom hcat

/-- The actual generic curve fibre gives the exact original absolute variety dimension. -/
theorem dimension_eq_base_add_one [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (hgen : topologicalKrullDim (f.fiber (genericPoint S)) = 1) :
    topologicalKrullDim X = topologicalKrullDim S + 1 := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := SeparableGenericSmoothness.functionFieldAlgebra (f ≫ p)
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let := functionFieldScalarTower p f
  obtain ⟨n, hS, htrS⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  obtain ⟨d, hX, htrX⟩ := FunctionFieldDimension.exists_dimension_and_trdeg (f ≫ p)
  obtain ⟨r, hr, hrel⟩ := SteinGenericFiber.exists_dimension_and_trdeg f
  have hr1 : r = 1 := by exact_mod_cast hr.symm.trans hgen
  have hsum := trdeg_add_eq k S.functionField (A := X.functionField)
  rw [htrS, hrel, hr1, htrX] at hsum
  have hnat : n + 1 = d := by exact_mod_cast hsum
  rw [hX, hS, ← hnat]
  exact_mod_cast rfl

/-- An actual finite dominant map preserves the original global variety dimension. -/
theorem dimension_eq_of_isFinite [LocallyOfFiniteType p] [IsFinite f] :
    topologicalKrullDim X = topologicalKrullDim S := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := SeparableGenericSmoothness.functionFieldAlgebra (f ≫ p)
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let := functionFieldScalarTower p f
  let : FiniteDimensional S.functionField X.functionField := FiniteBirationalNormal.finite_functionField f
  obtain ⟨n, hS, htrS⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  obtain ⟨d, hX, htrX⟩ := FunctionFieldDimension.exists_dimension_and_trdeg (f ≫ p)
  have hsum := trdeg_add_eq k S.functionField (A := X.functionField)
  rw [trdeg_eq_zero (R := S.functionField) (A := X.functionField), add_zero, htrS, htrX] at hsum
  have hnat : n = d := by exact_mod_cast hsum
  rw [hX, hS, hnat]

end DeJongAlterations.Geometry.VarietyFunctionFieldDimension
