import DeJongAlterations.Geometry.FiniteBirationalNormalGenericEvaluation
import DeJongAlterations.Geometry.FiniteBirationalNormalLiftGeneric

/-!
# Exact native generic restriction of the global normalization sections

The previously constructed global section is compared with the actual
generic evaluation on the actual generic-point pullback, through its two
original projections. Normalization finiteness comes from the actual
finite-type structure morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]
  (L : Type u) [Field L] [Algebra S.functionField L] [FiniteDimensional S.functionField L]
  (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (f : T ⟶ S) [IsDominant f] [IsFinite f]

/-- The actual global normalization section restricts to exactly the original generic evaluation. -/
theorem normalizationSection_generic_evaluation
    (U : NormalizationInExtension.NonemptyAffineOpen S)
    (σ : letI := functionFieldAlgebra f;
      letI := functionFieldAlgebra (NormalizationInExtension.normalizationStructure S L);
      T.functionField →ₐ[S.functionField] (NormalizationInExtension.normalization S L).functionField) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra (NormalizationInExtension.normalizationStructure S L)
    letI : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
      NormalizationInExtension.normalizationStructure_isFinite L p
    (NormalizationInExtension.normalization S L).fromSpecStalk
        (genericPoint (NormalizationInExtension.normalization S L)) ≫
      normalizationSection f L ((NormalizationInExtension.functionFieldAlgEquiv L U).toAlgHom.comp σ) =
      genericEvaluationToFiber f (NormalizationInExtension.normalizationStructure S L) σ ≫
        pullback.fst (pullback.snd f (NormalizationInExtension.normalizationStructure S L))
          ((NormalizationInExtension.normalization S L).fromSpecStalk
            (genericPoint (NormalizationInExtension.normalization S L))) := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra (NormalizationInExtension.normalizationStructure S L)
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  let e : Spec (.of L) ≅ Spec (NormalizationInExtension.normalization S L).functionField :=
    Scheme.Spec.mapIso (NormalizationInExtension.functionFieldEquiv L U).toCommRingCatIso.op
  apply (cancel_epi e.hom).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, normalizationSection_fst, genericEvaluationToFiber_fst_fst]
    change Spec.map (CommRingCat.ofHom (NormalizationInExtension.functionFieldEquiv L U).toRingHom) ≫
        (NormalizationInExtension.normalization S L).fromSpecStalk
          (genericPoint (NormalizationInExtension.normalization S L)) ≫
          normalizationLift f L
            ((NormalizationInExtension.functionFieldAlgEquiv L U).toAlgHom.comp σ) =
      Spec.map (CommRingCat.ofHom (NormalizationInExtension.functionFieldEquiv L U).toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ T.fromSpecStalk (genericPoint T)
    rw [normalizationLift_generic L f _ U, ← Spec.map_comp_assoc]
    rfl
  · simp only [Category.assoc, normalizationSection_snd, Category.comp_id,
      genericEvaluationToFiber_fst_snd]

end DeJongAlterations.Geometry.FiniteBirationalNormal
