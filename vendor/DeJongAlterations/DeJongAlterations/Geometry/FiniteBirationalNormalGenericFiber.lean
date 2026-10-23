import DeJongAlterations.Geometry.FiniteBirationalNormalGenericAffine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The actual generic-point square of a finite dominant morphism

The genuine affine tensor comparison identifies the original generic
point spectra as the actual scheme-theoretic base change. Pasting the
original affine-open square retains both native generic-stalk morphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T S : Scheme.{u}} [IsIntegral T] [IsIntegral S]
  (f : T ⟶ S) [IsDominant f] [IsFinite f]

/-- The actual generic finite affine square is Cartesian through the real tensor isomorphism. -/
theorem isPullback_finiteGenericAffine (U : NormalizationInExtension.NonemptyAffineOpen S) :
    IsPullback (Spec.map (NormalizationInExtension.functionFieldMap f))
      (Spec.map (T.germToFunctionField (f ⁻¹ᵁ U.1.1)))
      (Spec.map (S.germToFunctionField U.1.1)) (Spec.map (f.app U.1.1)) := by
  let B := Γ(S, U.1.1)
  let A := Γ(T, f ⁻¹ᵁ U.1.1)
  let := (f.app U.1.1).hom.toAlgebra
  let := functionFieldAlgebra f
  let G := S.functionField ⊗[B] A
  let e : Spec T.functionField ≅ Spec (.of G) :=
    Scheme.Spec.mapIso (finiteGenericAlgEquiv f U).toRingEquiv.toCommRingCatIso.op
  have H : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField G)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* G)))
      (Spec.map (S.germToFunctionField U.1.1)) (Spec.map (f.app U.1.1)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct B S.functionField A)
  apply H.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (finiteGenericAlgEquiv f U).toRingHom) ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext k
    exact (finiteGenericAlgEquiv f U).commutes k
  · change Spec.map (CommRingCat.ofHom (finiteGenericAlgEquiv f U).toRingHom) ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change finiteGenericAlgEquiv f U (1 ⊗ₜ[B] a) = T.germToFunctionField (f ⁻¹ᵁ U.1.1) a
    simpa only [map_one, one_mul] using finiteGenericAlgEquiv_tmul f U 1 a
  · rfl
  · rfl

omit [IsIntegral T] [IsIntegral S] [IsDominant f] in
/-- The original inverse-image affine chart square is native Cartesian geometry. -/
theorem isPullback_finiteComponentAffine (U : NormalizationInExtension.NonemptyAffineOpen S) :
    IsPullback (Spec.map (f.app U.1.1)) (U.1.2.preimage f).fromSpec U.1.2.fromSpec f := by
  apply IsOpenImmersion.isPullback
  · simpa only [← Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f U.1.2 (U.1.2.preimage f) le_rfl).symm
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

/-- The two actual generic-point spectra form the actual base-change square
of the original finite dominant morphism, in arbitrary dimension. -/
theorem isPullback_finiteGenericPoint :
    IsPullback (Spec.map (NormalizationInExtension.functionFieldMap f))
      (T.fromSpecStalk (genericPoint T)) (S.fromSpecStalk (genericPoint S)) f := by
  let U : NormalizationInExtension.NonemptyAffineOpen S :=
    (NormalizationInExtension.nonemptyAffineCover S).idx (genericPoint S)
  have hT : genericPoint T ∈ f ⁻¹ᵁ U.1.1 :=
    ((genericPoint_spec T).mem_open_set_iff (f ⁻¹ᵁ U.1.1).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ U.1.1)))
  have hS : genericPoint S ∈ U.1.1 :=
    ((genericPoint_spec S).mem_open_set_iff U.1.1.isOpen).mpr
      (by simpa using U.2)
  have H := (isPullback_finiteGenericAffine f U).paste_vert
    (isPullback_finiteComponentAffine f U)
  change IsPullback (Spec.map (NormalizationInExtension.functionFieldMap f))
    ((U.1.2.preimage f).fromSpecStalk hT) (U.1.2.fromSpecStalk hS) f at H
  simpa only [IsAffineOpen.fromSpecStalk_eq_fromSpecStalk] using H

end DeJongAlterations.Geometry.FiniteBirationalNormal
