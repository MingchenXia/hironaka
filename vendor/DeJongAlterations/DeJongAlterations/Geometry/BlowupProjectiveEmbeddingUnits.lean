import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingAffine
import DeJongAlterations.Geometry.ProjUnitScaling

/-!
# Independence of the actual blowup projective map under unit scaling

Multiplying all actual ideal generators by one unit preserves their span.
The resulting graded presentation is the degreewise unit automorphism composed
with the original presentation. The native Proj identity for that automorphism
therefore proves equality of actual scheme morphisms.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations.Algebra.ReesPresentation

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

/-- Unit multiplication preserves the span of the entire specified family. -/
theorem generator_span_unit (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (u : Aˣ) :
    Ideal.span (Set.range (fun i => (u : A) * g i)) = I := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact I.mul_mem_left _ (generator_mem I g hspan i)
  · rw [← hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have h := (Ideal.span (Set.range (fun i => (u : A) * g i))).mul_mem_left
      (u⁻¹ : Aˣ) (Ideal.subset_span ⟨i, rfl⟩)
    change g i ∈ Ideal.span (Set.range (fun i => (u : A) * g i))
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using h

/-- The coefficient unit as a genuine unit of degree zero of the actual Rees algebra. -/
def reesConstantUnit (I : Ideal A) (u : Aˣ) : (reesGrading I 0)ˣ :=
  Units.map (reesConstants I).toMonoidHom u

/-- The actual graded generator maps differ by the genuine Rees degreewise automorphism. -/
theorem generatorPolynomialMap_unit (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (u : Aˣ) :
    (generatorPolynomialMap I (fun i => (u : A) * g i)
      (generator_span_unit I g hspan u)).toGradedRingHom =
      (ProjUnitScaling.scaleAut (reesGrading I) (reesConstantUnit I u)).comp
        (generatorPolynomialMap I g hspan).toGradedRingHom := by
  apply GradedRingHom.ext
  have H : (generatorPolynomialMap I (fun i => (u : A) * g i)
      (generator_span_unit I g hspan u)).toRingHom =
      (ProjUnitScaling.scaleAut (reesGrading I) (reesConstantUnit I u)).toRingHom.comp
        (generatorPolynomialMap I g hspan).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change reesPolynomialEval I (fun i => (u : A) * g i) _ (C a) =
        ProjUnitScaling.scaleAut (reesGrading I) (reesConstantUnit I u)
          (reesPolynomialEval I g _ (C a))
      simp only [reesPolynomialEval, MvPolynomial.aeval_C]
      rw [ProjUnitScaling.scaleAut_apply_of_mem _ _
        (SetLike.algebraMap_mem_graded (reesGrading I) a)]
      simp
    · intro i
      change reesPolynomialEval I (fun i => (u : A) * g i) _ (X i) =
        ProjUnitScaling.scaleAut (reesGrading I) (reesConstantUnit I u)
          (reesPolynomialEval I g _ (X i))
      simp only [reesPolynomialEval, MvPolynomial.aeval_X]
      rw [ProjUnitScaling.scaleAut_apply_of_mem _ _ (reesDegreeOne_mem I _ _)]
      apply Subtype.ext
      change Polynomial.monomial 1 ((u : A) * g i) =
        Polynomial.C (u : A) ^ 1 * Polynomial.monomial 1 (g i)
      simp
  intro P
  exact RingHom.congr_fun H P

/-- Multiplying all generators by one unit leaves the native closed immersion unchanged. -/
theorem affineGeneratorEmbedding_unit (I : Ideal A) (g : Fin (m + 1) → A)
    (hspan : Ideal.span (Set.range g) = I) (u : Aˣ) :
    affineGeneratorEmbedding I (fun i => (u : A) * g i)
        (generator_span_unit I g hspan u) = affineGeneratorEmbedding I g hspan := by
  let hp := ProjClosedImmersion.irrelevant_le_map_of_surjective
    (generatorPolynomialMap I g hspan).toGradedRingHom
    (generatorPolynomialMap_surjective I g hspan)
  let hs := ProjUnitScaling.irrelevant_le_map (reesGrading I) (reesConstantUnit I u)
  dsimp only [affineGeneratorEmbedding]
  calc
    _ = Proj.map ((ProjUnitScaling.scaleAut (reesGrading I) (reesConstantUnit I u)).comp
        (generatorPolynomialMap I g hspan).toGradedRingHom)
        (HomogeneousIdeal.irrelevant_le_map_comp hp hs) :=
      projMap_congr (generatorPolynomialMap_unit I g hspan u) _ _
    _ = Proj.map (ProjUnitScaling.scaleAut (reesGrading I) (reesConstantUnit I u)) hs ≫
        Proj.map (generatorPolynomialMap I g hspan).toGradedRingHom hp := Proj.map_comp _ _ _ _
    _ = _ := by rw [ProjUnitScaling.map_eq_id, Category.id_comp]

/-- Unit change of a homogeneous trivialization preserves the actual projective morphism. -/
theorem affineProjectiveMap_unit (r : R →+* A) (I : Ideal A)
    (g : Fin (m + 1) → A) (hspan : Ideal.span (Set.range g) = I) (u : Aˣ) :
    affineProjectiveMap r I (fun i => (u : A) * g i)
      (generator_span_unit I g hspan u) = affineProjectiveMap r I g hspan := by
  rw [affineProjectiveMap, affineProjectiveMap, affineGeneratorEmbedding_unit I g hspan u]

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
