import DeJongAlterations.Geometry.FiniteBirationalNormalGenericFiber
import DeJongAlterations.Algebra.FiniteBirationalNormalTensor

/-!
# Actual tensor model of the generic base change of a finite component

All maps use the actual original generic-stalk field maps. The native
generic-point pullback of the actual component base change is identified
with the actual field tensor spectrum, retaining its two projections.
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

/-- The original finite map gives a finite extension of the actual canonical function fields. -/
theorem finite_functionField :
    letI := functionFieldAlgebra f
    FiniteDimensional S.functionField T.functionField := by
  let := functionFieldAlgebra f
  let U : NormalizationInExtension.NonemptyAffineOpen S :=
    (NormalizationInExtension.nonemptyAffineCover S).idx (genericPoint S)
  let := (f.app U.1.1).hom.toAlgebra
  let : Module.Finite Γ(S, U.1.1) Γ(T, f ⁻¹ᵁ U.1.1) := f.finite_app U.1.1 U.1.2
  exact Module.Finite.equiv (finiteGenericAlgEquiv f U).toLinearEquiv

omit [IsFinite f] [IsFinite g] in
/-- The actual tensor coefficient square of the two original generic field maps. -/
theorem isPullback_genericTensor :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField
        (Y.functionField ⊗[S.functionField] T.functionField))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        T.functionField →+* Y.functionField ⊗[S.functionField] T.functionField)))
      (Spec.map (NormalizationInExtension.functionFieldMap g))
      (Spec.map (NormalizationInExtension.functionFieldMap f)) := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct S.functionField Y.functionField T.functionField)

/-- The literal generic tensor map into the original actual component pullback. -/
def genericTensorInclusion :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    Spec (.of (Y.functionField ⊗[S.functionField] T.functionField)) ⟶ pullback f g := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  let q := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField
    (Y.functionField ⊗[S.functionField] T.functionField)))
  let t := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
    T.functionField →+* Y.functionField ⊗[S.functionField] T.functionField))
  refine pullback.lift (t ≫ T.fromSpecStalk (genericPoint T))
    (q ≫ Y.fromSpecStalk (genericPoint Y)) ?_
  calc
    (t ≫ T.fromSpecStalk (genericPoint T)) ≫ f =
        t ≫ (Spec.map (NormalizationInExtension.functionFieldMap f) ≫
          S.fromSpecStalk (genericPoint S)) := by
      rw [Category.assoc, (isPullback_finiteGenericPoint f).w]
    _ = (q ≫ Spec.map (NormalizationInExtension.functionFieldMap g)) ≫
        S.fromSpecStalk (genericPoint S) := by
      rw [← Category.assoc, (isPullback_genericTensor f g).w]
    _ = (q ≫ Y.fromSpecStalk (genericPoint Y)) ≫ g := by
      rw [Category.assoc, (isPullback_finiteGenericPoint g).w, Category.assoc]

/-- The original generic tensor model is the actual scheme-theoretic generic-point base change. -/
theorem isPullback_genericTensorInclusion :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    IsPullback (genericTensorInclusion f g)
      (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField
        (Y.functionField ⊗[S.functionField] T.functionField))))
      (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  have H := (isPullback_genericTensor f g).paste_vert (isPullback_finiteGenericPoint f)
  rw [(isPullback_finiteGenericPoint g).w] at H
  have H' : IsPullback
      (genericTensorInclusion f g ≫ pullback.fst f g)
      (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField
        (Y.functionField ⊗[S.functionField] T.functionField))))
      f (Y.fromSpecStalk (genericPoint Y) ≫ g) := by
    simpa only [genericTensorInclusion, pullback.lift_fst] using H.flip
  exact H'.of_right (by simp only [genericTensorInclusion, pullback.lift_snd])
    (.of_hasPullback f g)

/-- The actual tensor spectrum is canonically the actual native generic-point pullback. -/
def genericTensorFiberIso :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    Spec (.of (Y.functionField ⊗[S.functionField] T.functionField)) ≅
      pullback (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  exact (isPullback_genericTensorInclusion f g).isoPullback

/-- Its original component-pullback projection is exactly the constructed original map. -/
@[reassoc]
theorem genericTensorFiberIso_hom_fst :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    (genericTensorFiberIso f g).hom ≫
      pullback.fst (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) =
        genericTensorInclusion f g := by
  exact (isPullback_genericTensorInclusion f g).isoPullback_hom_fst

/-- Its actual generic-field projection is the original tensor coefficient map. -/
@[reassoc]
theorem genericTensorFiberIso_hom_snd :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    (genericTensorFiberIso f g).hom ≫
      pullback.snd (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) =
        Spec.map (CommRingCat.ofHom (algebraMap Y.functionField
          (Y.functionField ⊗[S.functionField] T.functionField))) := by
  exact (isPullback_genericTensorInclusion f g).isoPullback_hom_snd

/-- The actual generic-fiber map induced by an original compatible field embedding. -/
def genericEvaluationToFiber
    (σ : letI := functionFieldAlgebra f; letI := functionFieldAlgebra g;
      T.functionField →ₐ[S.functionField] Y.functionField) :
    Spec Y.functionField ⟶
      pullback (pullback.snd f g) (Y.fromSpecStalk (genericPoint Y)) := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  exact Spec.map (CommRingCat.ofHom
    (Algebra.FiniteBirationalNormalTensor.tensorEvaluation σ).toRingHom) ≫
      (genericTensorFiberIso f g).hom

/-- All actual conjugate evaluations cover the actual scheme-theoretic generic-point pullback. -/
theorem genericTensorFiber_covered
    (hn : letI := functionFieldAlgebra g; Normal S.functionField Y.functionField)
    (e : letI := functionFieldAlgebra f; letI := functionFieldAlgebra g;
      T.functionField →ₐ[S.functionField] Y.functionField) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    ⋃ σ : T.functionField →ₐ[S.functionField] Y.functionField,
      Set.range (genericEvaluationToFiber f g σ) = Set.univ := by
  let := functionFieldAlgebra f
  let := functionFieldAlgebra g
  let := finite_functionField f
  let := hn
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨σ, hσ⟩ := Algebra.FiniteBirationalNormalTensor.exists_tensorEvaluation_comap e
    ((genericTensorFiberIso f g).inv z)
  refine Set.mem_iUnion.mpr ⟨σ, (⊥ : PrimeSpectrum Y.functionField), ?_⟩
  change (genericTensorFiberIso f g).hom
    (PrimeSpectrum.comap (Algebra.FiniteBirationalNormalTensor.tensorEvaluation σ).toRingHom
      (⊥ : PrimeSpectrum Y.functionField)) = z
  rw [hσ]
  simp only [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

end DeJongAlterations.Geometry.FiniteBirationalNormal
