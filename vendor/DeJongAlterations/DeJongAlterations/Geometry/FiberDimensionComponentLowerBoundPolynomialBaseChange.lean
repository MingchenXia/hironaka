import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundBaseChange
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Actual coefficient pullback of an original polynomial projection -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundPolynomialBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (R K A : Type u) [CommRing R] [CommRing K] [CommRing A]
  [Algebra R K] [Algebra R A] (d : ℕ)

/-- The actual coefficient-base-changed projection evaluates the original variables in the tensor algebra. -/
def coefficientMap (f : MvPolynomial (Fin d) R →ₐ[R] A) :
    MvPolynomial (Fin d) K →ₐ[K] (K ⊗[R] A) :=
  aeval (fun i => (1 ⊗ₜ[R] f (X i)))

/-- The literal original polynomial coefficient square commutes as whole ring homomorphisms. -/
theorem coefficientMap_comp (f : MvPolynomial (Fin d) R →ₐ[R] A) :
    (coefficientMap R K A d f).toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      Algebra.TensorProduct.includeRight.toRingHom.comp f.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change coefficientMap R K A d f (MvPolynomial.map (algebraMap R K) (C r)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) (f (C r))
    simp [coefficientMap]
  · intro i
    change coefficientMap R K A d f (MvPolynomial.map (algebraMap R K) (X i)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) (f (X i))
    simp [coefficientMap]

/-- The actual polynomial coefficient-localization square is a native pushout for any coefficient algebra. -/
theorem polynomial_isPushout :
    IsPushout (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin d) R))
      (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (MvPolynomial.map (algebraMap R K) :
        MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) K))
      (CommRingCat.ofHom (C : K →+* MvPolynomial (Fin d) K)) := by
  simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def] using
    CommRingCat.isPushout_of_isPushout R (MvPolynomial (Fin d) R) K (MvPolynomial (Fin d) K)

/-- The original projection and its actual coefficient base change form a native scheme pullback. -/
theorem coefficientMap_isPullback (f : MvPolynomial (Fin d) R →ₐ[R] A) :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* K ⊗[R] A)))
      (Spec.map (CommRingCat.ofHom (coefficientMap R K A d f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R K) :
        MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) K))) := by
  have hfull : IsPushout
      (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin d) R) ≫ CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* K ⊗[R] A))
      (CommRingCat.ofHom (C : K →+* MvPolynomial (Fin d) K) ≫
        CommRingCat.ofHom (coefficientMap R K A d f).toRingHom) := by
    have hc : CommRingCat.ofHom (C : R →+* MvPolynomial (Fin d) R) ≫
        CommRingCat.ofHom f.toRingHom = CommRingCat.ofHom (algebraMap R A) := by
      apply CommRingCat.hom_ext
      exact f.comp_algebraMap
    have hk : CommRingCat.ofHom (C : K →+* MvPolynomial (Fin d) K) ≫
        CommRingCat.ofHom (coefficientMap R K A d f).toRingHom =
          CommRingCat.ofHom (algebraMap K (K ⊗[R] A)) := by
      apply CommRingCat.hom_ext
      exact (coefficientMap R K A d f).comp_algebraMap
    rw [hc, hk]
    exact (CommRingCat.isPushout_tensorProduct R K A).flip
  have hw : CommRingCat.ofHom f.toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* K ⊗[R] A) =
        CommRingCat.ofHom (MvPolynomial.map (algebraMap R K) :
          MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) K) ≫
          CommRingCat.ofHom (coefficientMap R K A d f).toRingHom :=
    CommRingCat.hom_ext (coefficientMap_comp R K A d f).symm
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (hfull.of_left hw (polynomial_isPushout R K d))

/-- The actual spectrum map of a residue-field coefficient homomorphism is a preimmersion. -/
theorem residueField_coefficient_isPreimmersion (p : Ideal R) [p.IsPrime] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) := by
  apply (MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion
    (Spec.map (Scheme.Spec.residueFieldIso (.of R) ⟨p, inferInstance⟩).inv) _).mp
  rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  infer_instance

/-- Actual polynomial residue-field coefficient base change is a preimmersion. -/
theorem polynomial_residueField_coefficient_isPreimmersion (p : Ideal R) [p.IsPrime] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R p.ResidueField) :
      MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) p.ResidueField))) := by
  have := residueField_coefficient_isPreimmersion R p
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion)
    (isPullback_SpecMap_of_isPushout _ _ _ _ (polynomial_isPushout R p.ResidueField d)).flip
    inferInstance

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundPolynomialBaseChange
