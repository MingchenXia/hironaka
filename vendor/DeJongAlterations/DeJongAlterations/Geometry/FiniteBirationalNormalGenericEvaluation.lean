import DeJongAlterations.Geometry.FiniteBirationalNormalGenericBaseChange

/-!
# Projections of the actual generic evaluation sections

The original generic evaluation maps really are sections of the native
generic-point pullback, and their composites to the two original schemes
are the original generic-stalk morphisms and chosen field embeddings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T S Y : Scheme.{u}} [IsIntegral T] [IsIntegral S] [IsIntegral Y]
  (f : T ⟶ S) [IsDominant f] [IsFinite f]
  (g : Y ⟶ S) [IsDominant g] [IsFinite g]
  (σ : letI := functionFieldAlgebra f; letI := functionFieldAlgebra g;
    T.functionField →ₐ[S.functionField] Y.functionField)

/-- Evaluation fixes the original generic-field coefficients, giving a genuine section. -/
@[reassoc]
theorem genericEvaluationToFiber_snd :
    genericEvaluationToFiber f g σ ≫
      pullback.snd (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) = 𝟙 _ := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  rw [genericEvaluationToFiber, Category.assoc, genericTensorFiberIso_hom_snd,
    ← Spec.map_comp]
  have H : CommRingCat.ofHom
      (algebraMap Y.functionField (Y.functionField ⊗[S.functionField] T.functionField)) ≫
      CommRingCat.ofHom (Algebra.FiniteBirationalNormalTensor.tensorEvaluation σ).toRingHom =
      𝟙 Y.functionField := by
    apply CommRingCat.hom_ext
    ext k
    exact (Algebra.FiniteBirationalNormalTensor.tensorEvaluation σ).commutes k
  rw [H]
  exact Spec.map_id Y.functionField

/-- The actual component projection is exactly the original embedding on generic spectra. -/
@[reassoc]
theorem genericEvaluationToFiber_fst_fst :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    genericEvaluationToFiber f g σ ≫
      pullback.fst (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ T.fromSpecStalk (genericPoint T) := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  rw [genericEvaluationToFiber, Category.assoc, genericTensorFiberIso_hom_fst_assoc,
    genericTensorInclusion, pullback.lift_fst, ← Spec.map_comp_assoc]
  apply congrArg (fun r : T.functionField →+* Y.functionField =>
    Spec.map (CommRingCat.ofHom r) ≫ T.fromSpecStalk (genericPoint T))
  ext a
  change Algebra.FiniteBirationalNormalTensor.tensorEvaluation σ
    (1 ⊗ₜ[S.functionField] a) = σ a
  simp only [Algebra.FiniteBirationalNormalTensor.tensorEvaluation_tmul, one_mul]

/-- The actual base projection is the original generic-stalk morphism of the actual base. -/
@[reassoc]
theorem genericEvaluationToFiber_fst_snd :
    genericEvaluationToFiber f g σ ≫
      pullback.fst (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) ≫ pullback.snd f g =
      Y.fromSpecStalk (genericPoint Y) := by
  rw [pullback.condition, ← Category.assoc, genericEvaluationToFiber_snd, Category.id_comp]

end DeJongAlterations.Geometry.FiniteBirationalNormal
