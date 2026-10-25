import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingAffine
import DeJongAlterations.Geometry.ProjectiveIdentity
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual blowup of the unit ideal over any commutative ring

The literal one-generator Rees presentation is a graded isomorphism. Its
native Proj map identifies the actual blowup with projective zero-space,
so the original affine blowup structure morphism is itself an isomorphism.
No domain or nontriviality hypothesis is used.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations.Algebra.ReesPresentation
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding

noncomputable section

namespace DeJongAlterations.Geometry.UnitIdealBlowup

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type u) [CommRing A]

/-- The literal singleton family of units spans the actual unit ideal. -/
theorem one_span : Ideal.span (Set.range (fun _ : Fin 1 => (1 : A))) = ⊤ := by
  have h : (1 : A) ∈ Ideal.span (Set.range (fun _ : Fin 1 => (1 : A))) :=
    Ideal.subset_span ⟨0, rfl⟩
  exact Ideal.eq_top_of_isUnit_mem _ h isUnit_one

/-- The actual one-generator presentation of the unit-ideal Rees algebra. -/
def unitPresentation :
    GradedAlgHom A (projectiveSpaceGrading A 0) (reesGrading (⊤ : Ideal A)) :=
  generatorPolynomialMap ⊤ (fun _ : Fin 1 => 1) (one_span A)

/-- Its composite into the ambient polynomial ring is the genuine one-variable equivalence. -/
theorem unitPresentation_val :
    (reesAlgebra (⊤ : Ideal A)).val.comp (unitPresentation A).toAlgHom =
      (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [unitPresentation, generatorPolynomialMap, reesPolynomialMap, reesPolynomialEval,
    reesDegreeOne, MvPolynomial.uniqueAlgEquiv, Polynomial.monomial_one_one_eq_X]

/-- The actual unit-ideal presentation is injective over arbitrary coefficient rings. -/
theorem unitPresentation_injective : Function.Injective (unitPresentation A) := by
  intro P Q hPQ
  apply (MvPolynomial.uniqueAlgEquiv A (Fin 1)).injective
  have h := congrArg (fun p : reesAlgebra (⊤ : Ideal A) => (p : Polynomial A)) hPQ
  exact (AlgHom.congr_fun (unitPresentation_val A) P).symm.trans
    (h.trans (AlgHom.congr_fun (unitPresentation_val A) Q))

/-- The actual unit-ideal presentation is surjective because its generator spans the ideal. -/
theorem unitPresentation_surjective : Function.Surjective (unitPresentation A) :=
  generatorPolynomialMap_surjective ⊤ (fun _ : Fin 1 => 1) (one_span A)

/-- The genuine underlying ring equivalence, with no supplied comparison witness. -/
def unitPresentationEquiv :
    MvPolynomial (Fin 1) A ≃+* reesAlgebra (⊤ : Ideal A) :=
  RingEquiv.ofBijective (unitPresentation A).toRingHom
    ⟨unitPresentation_injective A, unitPresentation_surjective A⟩

/-- The actual inverse preserves the homogeneous pieces by native homogeneous lifting. -/
def unitPresentationInverse :
    reesGrading (⊤ : Ideal A) →+*ᵍ projectiveSpaceGrading A 0 where
  __ := (unitPresentationEquiv A).symm.toRingHom
  map_mem {i q} hq := by
    obtain ⟨P, hP, heq⟩ := exists_homogeneous_preimage_monomial (⊤ : Ideal A)
      (fun _ : Fin 1 => 1) (generator_mem ⊤ (fun _ : Fin 1 => 1) (one_span A))
      (one_span A) i ((q : Polynomial A).coeff i) (q.2 i)
    have heq' : unitPresentation A P = q := by
      apply Subtype.ext
      exact heq.trans ((mem_reesGrading_iff _ _ q).mp hq).symm
    change (unitPresentationEquiv A).symm q ∈ projectiveSpaceGrading A 0 i
    rw [← heq']
    change (unitPresentationEquiv A).symm (unitPresentationEquiv A P) ∈ _
    simpa only [RingEquiv.symm_apply_apply, projectiveSpaceGrading,
      MvPolynomial.mem_homogeneousSubmodule] using hP

/-- The constructed inverse is a left inverse of the literal presentation. -/
theorem inverse_comp_presentation :
    (unitPresentationInverse A).comp (unitPresentation A).toGradedRingHom =
      GradedRingHom.id (projectiveSpaceGrading A 0) := by
  apply GradedRingHom.ext
  intro P
  exact (unitPresentationEquiv A).symm_apply_apply P

/-- The constructed inverse is a right inverse of the literal presentation. -/
theorem presentation_comp_inverse :
    (unitPresentation A).toGradedRingHom.comp (unitPresentationInverse A) =
      GradedRingHom.id (reesGrading (⊤ : Ideal A)) := by
  apply GradedRingHom.ext
  intro q
  exact (unitPresentationEquiv A).apply_symm_apply q

/-- The literal generator embedding identifies the actual unit-ideal blowup with projective zero-space. -/
def blowupProjectiveZeroIso : affineBlowup (⊤ : Ideal A) ≅ projectiveSpace A 0 where
  hom := affineGeneratorEmbedding ⊤ (fun _ : Fin 1 => 1) (one_span A)
  inv := Proj.map (unitPresentationInverse A)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _ (unitPresentationEquiv A).symm.surjective)
  hom_inv_id := by
    change Proj.map (unitPresentation A).toGradedRingHom _ ≫
      Proj.map (unitPresentationInverse A) _ = 𝟙 (Proj (reesGrading (⊤ : Ideal A)))
    rw [← Proj.map_comp]
    simpa only [presentation_comp_inverse] using
      (Proj.map_id (𝒜 := reesGrading (⊤ : Ideal A)))
  inv_hom_id := by
    change Proj.map (unitPresentationInverse A) _ ≫
      Proj.map (unitPresentation A).toGradedRingHom _ = 𝟙 (Proj (projectiveSpaceGrading A 0))
    rw [← Proj.map_comp]
    simpa only [inverse_comp_presentation] using
      (Proj.map_id (𝒜 := projectiveSpaceGrading A 0))

/-- The original blowup structure morphism of the unit ideal is an isomorphism over every ring. -/
instance affineBlowupStructure_top_isIso : IsIso (affineBlowupStructure (⊤ : Ideal A)) := by
  have : IsIso ((blowupProjectiveZeroIso A).hom ≫ projectiveSpaceStructure A 0) := by
    infer_instance
  exact (show (blowupProjectiveZeroIso A).hom ≫ projectiveSpaceStructure A 0 =
    affineBlowupStructure (⊤ : Ideal A) from
      affineGeneratorEmbedding_structure ⊤ (fun _ : Fin 1 => 1) (one_span A)) ▸ this

/-- This isomorphism has the literal original structure morphism as its forward map. -/
def unitIdealBlowupIso : affineBlowup (⊤ : Ideal A) ≅ Spec (CommRingCat.of A) :=
  asIso (affineBlowupStructure (⊤ : Ideal A))

@[simp]
theorem unitIdealBlowupIso_hom :
    (unitIdealBlowupIso A).hom = affineBlowupStructure (⊤ : Ideal A) := rfl

end DeJongAlterations.Geometry.UnitIdealBlowup
