import DeJongAlterations.Geometry.ProjectiveIdeal
import DeJongAlterations.Geometry.ProjStructureMap

/-!
# Actual coefficient maps of native projective spaces

The actual polynomial coefficient homomorphism supplies the native projective
morphism and preserves the original coefficient-ring structure maps.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Equality of graded maps identifies the actual native Proj maps, including their
irrelevant-containment proofs. -/
theorem projMap_congr {C D σ τ : Type u} [CommRing C] [CommRing D]
    [SetLike σ C] [AddSubgroupClass σ C] [SetLike τ D] [AddSubgroupClass τ D]
    {𝒞 : ℕ → σ} {𝒟 : ℕ → τ} [GradedRing 𝒞] [GradedRing 𝒟]
    {f g : 𝒞 →+*ᵍ 𝒟} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒞).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒞).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- The genuine coefficientwise graded polynomial homomorphism. -/
def polynomialCoefficientMap (f : R →+* A) (m : ℕ) :
    projectiveSpaceGrading R m →+*ᵍ projectiveSpaceGrading A m where
  __ := MvPolynomial.map f
  map_mem h := h.map f

/-- The actual coefficient map itself supplies the native irrelevant containment. -/
theorem polynomialCoefficientMap_irrelevant (f : R →+* A) (m : ℕ) :
    HomogeneousIdeal.irrelevant (projectiveSpaceGrading A m) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).map
        (polynomialCoefficientMap f m) := by
  change (HomogeneousIdeal.irrelevant (projectiveSpaceGrading A m)).toIdeal ≤
    Ideal.map (polynomialCoefficientMap f m).toRingHom
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).toIdeal
  rw [ProjectiveIdeal.irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h : (X i : MvPolynomial (Fin (m + 1)) R) ∈
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X R i)
  change X i ∈ Ideal.map (MvPolynomial.map f)
    (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).toIdeal
  simpa only [MvPolynomial.map_X] using Ideal.mem_map_of_mem (MvPolynomial.map f) h

/-- The actual native projective coefficient morphism. -/
def projectiveCoefficientMap (f : R →+* A) (m : ℕ) :
    projectiveSpace A m ⟶ projectiveSpace R m :=
  Proj.map (polynomialCoefficientMap f m) (polynomialCoefficientMap_irrelevant f m)

/-- Degree zero of the actual coefficient homomorphism is the original ring map. -/
theorem polynomialCoefficientMap_degreeZero (f : R →+* A) (m : ℕ) :
    (polynomialCoefficientMap f m).gradedZeroRingHom.comp
      (projectiveSpaceDegreeZeroEquiv R m).toRingHom =
    (projectiveSpaceDegreeZeroEquiv A m).toRingHom.comp f := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change MvPolynomial.map f (C r) = C (f r)
  exact MvPolynomial.map_C f r

/-- The coefficient morphism preserves the actual original structure maps. -/
@[reassoc]
theorem projectiveCoefficientMap_structure (f : R →+* A) (m : ℕ) :
    projectiveCoefficientMap f m ≫ projectiveSpaceStructure R m =
      projectiveSpaceStructure A m ≫ Spec.map (CommRingCat.ofHom f) := by
  have H := ProjStructureMap.map_toSpec_base (polynomialCoefficientMap f m)
    (polynomialCoefficientMap_irrelevant f m)
    (projectiveSpaceDegreeZeroEquiv R m).toRingHom
    ((projectiveSpaceDegreeZeroEquiv A m).toRingHom.comp f)
    (polynomialCoefficientMap_degreeZero f m)
  change Proj.map (polynomialCoefficientMap f m) (polynomialCoefficientMap_irrelevant f m) ≫
      (Proj.toSpecZero (projectiveSpaceGrading R m) ≫
        Spec.map (CommRingCat.ofHom (projectiveSpaceDegreeZeroEquiv R m).toRingHom)) =
    Proj.toSpecZero (projectiveSpaceGrading A m) ≫
      Spec.map (CommRingCat.ofHom (projectiveSpaceDegreeZeroEquiv A m).toRingHom) ≫
        Spec.map (CommRingCat.ofHom f)
  simpa only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using H

/-- Polynomial coefficient mapping preserves the literal identity. -/
theorem polynomialCoefficientMap_id (m : ℕ) :
    polynomialCoefficientMap (RingHom.id R) m = GradedRingHom.id (projectiveSpaceGrading R m) := by
  apply GradedRingHom.ext
  intro P
  exact MvPolynomial.map_id P

variable {B : Type u} [CommRing B]

/-- Polynomial coefficient mapping preserves the literal coefficient composition. -/
theorem polynomialCoefficientMap_comp (f : R →+* A) (g : A →+* B) (m : ℕ) :
    (polynomialCoefficientMap g m).comp (polynomialCoefficientMap f m) =
      polynomialCoefficientMap (g.comp f) m := by
  apply GradedRingHom.ext
  intro P
  exact MvPolynomial.map_map f g P

/-- The native projective coefficient morphism preserves identities. -/
theorem projectiveCoefficientMap_id (m : ℕ) :
    projectiveCoefficientMap (RingHom.id R) m = 𝟙 (projectiveSpace R m) := by
  dsimp only [projectiveCoefficientMap]
  exact (projMap_congr (polynomialCoefficientMap_id m) _ (by simp)).trans Proj.map_id

/-- The native projective coefficient morphism preserves coefficient composition. -/
theorem projectiveCoefficientMap_comp (f : R →+* A) (g : A →+* B) (m : ℕ) :
    projectiveCoefficientMap g m ≫ projectiveCoefficientMap f m =
      projectiveCoefficientMap (g.comp f) m := by
  dsimp only [projectiveCoefficientMap]
  rw [← Proj.map_comp]
  exact projMap_congr (polynomialCoefficientMap_comp f g m) _ _

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
