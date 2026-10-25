import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingCoefficients
import DeJongAlterations.Geometry.AffineBlowupProjective
import DeJongAlterations.Geometry.AffineBlowupFunctor

/-!
# Controlled native affine blowup maps from actual ideal generators

The specified finite generators, rather than a separately chosen presentation,
define the actual graded Rees map and projective morphism. Coefficient extension
preserves these morphisms as scheme morphisms with their original bases.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations.Algebra.ReesPresentation DeJongAlterations.Algebra.ReesLocalization

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {m : ℕ}

/-- Membership of the specified generators follows from their actual span identity. -/
theorem generator_mem (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (i : Fin (m + 1)) : g i ∈ I := by
  rw [← hspan]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The actual graded presentation determined by the specified ideal generators. -/
def generatorPolynomialMap (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    GradedAlgHom A (projectiveSpaceGrading A m) (reesGrading I) :=
  reesPolynomialMap I g (generator_mem I g hspan)

/-- The given span identity makes this actual polynomial map surjective. -/
theorem generatorPolynomialMap_surjective (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    Function.Surjective (generatorPolynomialMap I g hspan) :=
  reesPolynomialMap_surjective I g (generator_mem I g hspan) hspan

/-- The native affine blowup embedding determined by those exact generators. -/
def affineGeneratorEmbedding (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) : affineBlowup I ⟶ projectiveSpace A m :=
  Proj.map (generatorPolynomialMap I g hspan).toGradedRingHom
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _
      (generatorPolynomialMap_surjective I g hspan))

instance affineGeneratorEmbedding_isClosedImmersion (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    IsClosedImmersion (affineGeneratorEmbedding I g hspan) :=
  ProjClosedImmersion.isClosedImmersion_map _ (generatorPolynomialMap_surjective I g hspan) _

/-- The specified native affine embedding preserves the original affine base morphism. -/
@[reassoc]
theorem affineGeneratorEmbedding_structure (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    affineGeneratorEmbedding I g hspan ≫ projectiveSpaceStructure A m = affineBlowupStructure I :=
  reesPolynomialMap_projStructure I (generatorPolynomialMap I g hspan) _

/-- The actual affine generator map into projective space over the original coefficient ring. -/
def affineProjectiveMap (r : R →+* A) (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) : affineBlowup I ⟶ projectiveSpace R m :=
  affineGeneratorEmbedding I g hspan ≫ projectiveCoefficientMap r m

/-- Its native structure triangle is the original coefficient-ring triangle. -/
@[reassoc]
theorem affineProjectiveMap_structure (r : R →+* A) (I : Ideal A)
    (g : Fin (m + 1) → A) (hspan : Ideal.span (Set.range g) = I) :
    affineProjectiveMap r I g hspan ≫ projectiveSpaceStructure R m =
      affineBlowupStructure I ≫ Spec.map (CommRingCat.ofHom r) := by
  rw [affineProjectiveMap, Category.assoc, projectiveCoefficientMap_structure,
    ← Category.assoc, affineGeneratorEmbedding_structure]

/-- Extension of the actual generator family generates the actual extended ideal. -/
theorem generator_span_map (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (f : A →+* B) :
    Ideal.span (Set.range (fun i => f (g i))) = I.map f := by
  rw [← hspan, Ideal.map_span, ← Set.range_comp]
  rfl

/-- The graded presentations commute with the actual Rees coefficient homomorphism. -/
theorem generatorPolynomialMap_naturality (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (f : A →+* B) :
    (reesGradedMap I f).comp (generatorPolynomialMap I g hspan).toGradedRingHom =
      (generatorPolynomialMap (I.map f) (fun i => f (g i))
        (generator_span_map I g hspan f)).toGradedRingHom.comp (polynomialCoefficientMap f m) := by
  have H : (reesGradedMap I f).toRingHom.comp
      (generatorPolynomialMap I g hspan).toRingHom =
      (generatorPolynomialMap (I.map f) (fun i => f (g i))
        (generator_span_map I g hspan f)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change reesMap I f (reesPolynomialEval I g (generator_mem I g hspan) (C a)) =
        reesPolynomialEval (I.map f) (fun i => f (g i))
          (generator_mem _ _ (generator_span_map I g hspan f)) (MvPolynomial.map f (C a))
      simp only [reesPolynomialEval, MvPolynomial.aeval_C, MvPolynomial.map_C]
      exact reesMap_algebraMap I f a
    · intro i
      change reesMap I f (reesPolynomialEval I g (generator_mem I g hspan) (X i)) =
        reesPolynomialEval (I.map f) (fun i => f (g i))
          (generator_mem _ _ (generator_span_map I g hspan f)) (MvPolynomial.map f (X i))
      simp only [reesPolynomialEval, MvPolynomial.aeval_X, MvPolynomial.map_X]
      apply Subtype.ext
      change Polynomial.map f (Polynomial.monomial 1 (g i)) = Polynomial.monomial 1 (f (g i))
      exact Polynomial.map_monomial f
  apply GradedRingHom.ext
  intro P
  exact RingHom.congr_fun H P

/-- The actual native generator embeddings commute with coefficient extension. -/
@[reassoc]
theorem affineGeneratorEmbedding_naturality (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (f : A →+* B) :
    affineBlowupMap I f ≫ affineGeneratorEmbedding I g hspan =
      affineGeneratorEmbedding (I.map f) (fun i => f (g i)) (generator_span_map I g hspan f) ≫
        projectiveCoefficientMap f m := by
  dsimp only [affineBlowupMap, affineGeneratorEmbedding, projectiveCoefficientMap]
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact projMap_congr (generatorPolynomialMap_naturality I g hspan f) _ _

/-- Native affine maps into the fixed original projective space commute with restriction. -/
@[reassoc]
theorem affineProjectiveMap_naturality (r : R →+* A) (I : Ideal A)
    (g : Fin (m + 1) → A) (hspan : Ideal.span (Set.range g) = I) (f : A →+* B) :
    affineBlowupMap I f ≫ affineProjectiveMap r I g hspan =
      affineProjectiveMap (f.comp r) (I.map f) (fun i => f (g i))
        (generator_span_map I g hspan f) := by
  dsimp only [affineProjectiveMap]
  rw [← Category.assoc, affineGeneratorEmbedding_naturality, Category.assoc,
    projectiveCoefficientMap_comp]

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
