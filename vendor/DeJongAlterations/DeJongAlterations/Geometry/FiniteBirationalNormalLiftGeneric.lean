import DeJongAlterations.Geometry.FiniteBirationalNormalLift
import DeJongAlterations.Geometry.NormalizationInExtension
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Actual generic behavior of the constructed normalization lifts

The original closure-ring coefficient maps identify the literal generic
map from the specified ambient field, and the constructed scheme lift
retains its original function-field embedding on that actual generic map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic-stalk spectrum map commutes with the two actual generic-point morphisms. -/
@[reassoc]
theorem functionFieldMap_fromSpecStalk (h : X ⟶ Y) [IsDominant h] :
    Spec.map (NormalizationInExtension.functionFieldMap h) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ h := by
  simp only [NormalizationInExtension.functionFieldMap, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

variable {S : Scheme.{u}} [IsIntegral S] (L : Type u) [Field L]
  [Algebra S.functionField L] [FiniteDimensional S.functionField L]

attribute [local instance] NormalizationInExtension.sectionsAlgebra

/-- The actual comparison-field generic map is the original closure-coefficient chart map. -/
theorem functionFieldEquiv_fromSpecStalk (U : NormalizationInExtension.NonemptyAffineOpen S) :
    Spec.map (CommRingCat.ofHom (NormalizationInExtension.functionFieldEquiv L U).toRingHom) ≫
      (NormalizationInExtension.normalization S L).fromSpecStalk
        (genericPoint (NormalizationInExtension.normalization S L)) =
      Spec.map (CommRingCat.ofHom (algebraMap (NormalizationInExtension.closureRing L U) L)) ≫
        NormalizationInExtension.chartInclusion S L U := by
  let C := NormalizationInExtension.closureRing L U
  let := NormalizationInExtension.closureRing_isFractionRing L U
  let e := IsLocalization.algEquiv C⁰ (Spec (.of C)).functionField L
  change Spec.map ((NormalizationInExtension.chartFunctionFieldIso L U).hom ≫
    CommRingCat.ofHom e.toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Spec.map (NormalizationInExtension.functionFieldMap
      (NormalizationInExtension.chartInclusion S L U)) ≫
      (NormalizationInExtension.normalization S L).fromSpecStalk
        (genericPoint (NormalizationInExtension.normalization S L))) = _
  rw [functionFieldMap_fromSpecStalk]
  rw [← Category.assoc, Spec.fromSpecStalk_eq', ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext c
  exact e.commutes c

variable {T : Scheme.{u}} [IsIntegral T] (f : T ⟶ S) [IsDominant f] [IsFinite f]
  (σ : letI := functionFieldAlgebra f; T.functionField →ₐ[S.functionField] L)

/-- The literal global scheme lift agrees with the original field embedding on the actual generic map. -/
theorem normalizationLift_generic (U : NormalizationInExtension.NonemptyAffineOpen S) :
    letI := functionFieldAlgebra f
    Spec.map (CommRingCat.ofHom (NormalizationInExtension.functionFieldEquiv L U).toRingHom) ≫
      (NormalizationInExtension.normalization S L).fromSpecStalk
        (genericPoint (NormalizationInExtension.normalization S L)) ≫
      normalizationLift f L σ =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ T.fromSpecStalk (genericPoint T) := by
  let := functionFieldAlgebra f
  have hT : genericPoint T ∈ f ⁻¹ᵁ U.1.1 :=
    ((genericPoint_spec T).mem_open_set_iff (f ⁻¹ᵁ U.1.1).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ U.1.1)))
  rw [← Category.assoc, functionFieldEquiv_fromSpecStalk, Category.assoc,
    normalizationLift_restrict, affineLift, ← Category.assoc, ← Spec.map_comp]
  rw [← (U.1.2.preimage f).fromSpecStalk_eq_fromSpecStalk hT, IsAffineOpen.fromSpecStalk,
    ← Spec.map_comp_assoc]
  rfl

end DeJongAlterations.Geometry.FiniteBirationalNormal
