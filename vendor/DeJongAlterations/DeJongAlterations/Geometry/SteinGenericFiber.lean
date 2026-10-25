import DeJongAlterations.Geometry.GenericFiberFunctionField
import DeJongAlterations.Geometry.FiniteBirationalNormalLiftGeneric
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension

/-!
# Canonical scalar compatibility for the actual generic fibre

The original generic-stalk homomorphism and the actual residue-field
structure on the native fibre form the same coefficient triangle.
No function-field comparison or scalar compatibility is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.SteinGenericFiber

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {Z : Scheme.{u}} [IsIntegral Z]

/-- The canonical structural field homomorphism is the actual generic-point morphism over the field. -/
theorem structureFieldMap_generic (p : Z ⟶ Spec (.of k)) :
    Spec.map (CommRingCat.ofHom
      (@algebraMap k Z.functionField _ _
        (SeparableGenericSmoothness.functionFieldAlgebra p))) =
      Z.fromSpecStalk (genericPoint Z) ≫ p := by
  change Spec.map (StructureSheaf.toStalk k (p (genericPoint Z)) ≫
    p.stalkMap (genericPoint Z)) = _
  rw [Spec.map_comp]
  simpa only [Spec.fromSpecStalk_eq'] using
    Scheme.SpecMap_stalkMap_fromSpecStalk p (x := genericPoint Z)

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

attribute [local instance] GenericFiberIntegral.genericFiber_isIntegral
  GenericFiberFunctionField.genericFiberι_isDominant

/-- The literal coefficient identity uses the original map and original generic-fibre inclusion. -/
theorem coefficient_triangle :
    letI : Algebra (S.residueField (genericPoint S))
        (f.fiber (genericPoint S)).functionField :=
      SeparableGenericSmoothness.functionFieldAlgebra
      (k := S.residueField (genericPoint S))
      (f.fiberToSpecResidueField (genericPoint S))
    (algebraMap (S.residueField (genericPoint S))
      (f.fiber (genericPoint S)).functionField).comp (S.residue (genericPoint S)).hom =
    (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))).hom.comp
      (NormalizationInExtension.functionFieldMap f).hom := by
  let : Algebra (S.residueField (genericPoint S))
      (f.fiber (genericPoint S)).functionField :=
    SeparableGenericSmoothness.functionFieldAlgebra
    (k := S.residueField (genericPoint S))
    (f.fiberToSpecResidueField (genericPoint S))
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (S.fromSpecStalk (genericPoint S))).mp
  change Spec.map (S.residue (genericPoint S) ≫ CommRingCat.ofHom
      (algebraMap (S.residueField (genericPoint S))
        (f.fiber (genericPoint S)).functionField)) ≫ S.fromSpecStalk (genericPoint S) =
    Spec.map (NormalizationInExtension.functionFieldMap f ≫
      NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))) ≫
        S.fromSpecStalk (genericPoint S)
  rw [Spec.map_comp, Category.assoc, ← Scheme.fromSpecResidueField]
  erw [structureFieldMap_generic (f.fiberToSpecResidueField (genericPoint S))]
  simp only [Spec.map_comp, Category.assoc]
  rw [FiniteBirationalNormal.functionFieldMap_fromSpecStalk f,
    FiniteBirationalNormal.functionFieldMap_fromSpecStalk_assoc (f.fiberι (genericPoint S)),
    Scheme.Hom.fiber_fac]

/-- The canonical generic residue field is genuinely the original generic stalk. -/
def genericResidueIso : S.functionField ≅ S.residueField (genericPoint S) := by
  let : IsIso (S.residue (genericPoint S)) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(S.residue (genericPoint S)).hom.injective, IsLocalRing.residue_surjective⟩
  exact asIso (S.residue (genericPoint S))

/-- The actual original relative function-field degree computes native generic-fibre dimension. -/
theorem exists_dimension_and_trdeg [LocallyOfFiniteType f] :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    ∃ d : ℕ, topologicalKrullDim (f.fiber (genericPoint S)) = d ∧
      Algebra.trdeg S.functionField X.functionField = d := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let T := f.fiber (genericPoint S)
  let K := S.residueField (genericPoint S)
  let p := f.fiberToSpecResidueField (genericPoint S)
  let : Algebra K T.functionField :=
    SeparableGenericSmoothness.functionFieldAlgebra (k := K) p
  let : Algebra S.functionField K := (S.residue (genericPoint S)).hom.toAlgebra
  let : Module.Finite S.functionField K :=
    RingHom.Finite.of_surjective (S.residue (genericPoint S)).hom
      IsLocalRing.residue_surjective
  let : Algebra S.functionField T.functionField :=
    ((NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))).hom.comp
      (NormalizationInExtension.functionFieldMap f).hom).toAlgebra
  let : IsScalarTower S.functionField K T.functionField :=
    .of_algebraMap_eq' (coefficient_triangle f).symm
  let e : X.functionField ≃ₐ[S.functionField] T.functionField :=
    { (GenericFiberFunctionField.functionFieldIso f).commRingCatIsoToRingEquiv with
      commutes' := fun r => rfl }
  have hdeg := trdeg_add_eq S.functionField K (A := T.functionField)
  rw [trdeg_eq_zero (R := S.functionField) (A := K), zero_add] at hdeg
  let : LocallyOfFiniteType p := MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨d, hd, htr⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  exact ⟨d, hd, e.trdeg_eq.trans (hdeg.symm.trans htr)⟩

/-- An actual generic-curve dimension bound yields the canonical relative field bound. -/
theorem trdeg_le_one [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1) :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    Algebra.trdeg S.functionField X.functionField ≤ 1 := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  obtain ⟨d, hd, htr⟩ := exists_dimension_and_trdeg f
  rw [hd] at hdim
  have hdn : d ≤ 1 := by exact_mod_cast hdim
  rw [htr]
  exact_mod_cast hdn

end DeJongAlterations.Geometry.SteinGenericFiber
