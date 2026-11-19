import Hironaka.Geometry.ProjectiveSecantProjectionScalarGraded

/-!
# Actual whole original source coefficient triangles retain actual whole source-representative coefficient triangles
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveSpaceBaseChange BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (n : ℕ)
  {X XL : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (j : XL ⟶ projectiveSpace L (n + 1)) [IsClosedImmersion j] (a : XL ⟶ X)

/-- The SAME actual original source representative inverse retains the literal whole original closed embedding. -/
theorem originalRepresentativeIso_inv_inclusion :
    (representativeIso k n i).inv ≫ i = originalInclusion k n (representativeIdeal k n i) := by
  let e := representativeIso k n i
  have h := congrArg (fun m => e.inv ≫ m) (representativeIso_hom_inclusion k n i)
  change e.inv ≫ (e.hom ≫ originalInclusion k n (representativeIdeal k n i)) = e.inv ≫ i at h
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

/-- The actual whole original source morphism internally gives its actual morphism of the SAME two native source representatives. -/
def originalSourceRepresentativeCoefficientMap :
    originalScheme L n (representativeIdeal L n j) ⟶ originalScheme k n (representativeIdeal k n i) :=
  (representativeIso L n j).inv ≫ a ≫ (representativeIso k n i).hom

variable (φ : k →+* L) (H : a ≫ i = j ≫ projectiveCoefficientMap φ (n + 1))

include H in
/-- The actual entire original ambient coefficient triangle internally produces the exact whole native source-representative coefficient square, without any defining-ideal scalar equality. -/
theorem originalSourceRepresentativeCoefficientMap_embedding :
    originalSourceRepresentativeCoefficientMap k L n i j a ≫
      General.Morph.map
        (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal)
        (General.Morph.relevant_of_irrelevant_le _ (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n i))) =
    General.Morph.map
      ((GradedQuotient.gradedMk (ProjectiveGrading L (n + 1)) (representativeIdeal L n j).toIdeal).comp
        (coefficientGradedMap φ))
      (General.Morph.relevant_comp (coefficientGradedMap φ)
        (GradedQuotient.gradedMk (ProjectiveGrading L (n + 1)) (representativeIdeal L n j).toIdeal)
        (General.Morph.relevant_of_irrelevant_le _ (coefficientGradedMap_irrelevant_le φ))
        (General.Morph.relevant_of_irrelevant_le _ (GradedQuotient.irrelevant_le_map _ (representativeIdeal L n j)))) := by
  rw [General.Morph.map_comp (coefficientGradedMap φ)
    (GradedQuotient.gradedMk (ProjectiveGrading L (n + 1)) (representativeIdeal L n j).toIdeal)
    (General.Morph.relevant_of_irrelevant_le _ (coefficientGradedMap_irrelevant_le φ))
    (General.Morph.relevant_of_irrelevant_le _ (GradedQuotient.irrelevant_le_map _ (representativeIdeal L n j)))]
  rw [General.Morph.map_eq_native, General.Morph.map_eq_native, General.Morph.map_eq_native]
  change ((representativeIso L n j).inv ≫ a ≫ (representativeIso k n i).hom) ≫
      originalInclusion k n (representativeIdeal k n i) =
    originalInclusion L n (representativeIdeal L n j) ≫ projectiveCoefficientMap φ (n + 1)
  calc
    _ = (representativeIso L n j).inv ≫ a ≫ i := by
      rw [Category.assoc, Category.assoc, representativeIso_hom_inclusion]
    _ = (representativeIso L n j).inv ≫ j ≫ projectiveCoefficientMap φ (n + 1) := by rw [H]
    _ = _ := by rw [← Category.assoc, originalRepresentativeIso_inv_inclusion]

end Hironaka.Geometry.ProjectiveSecant
