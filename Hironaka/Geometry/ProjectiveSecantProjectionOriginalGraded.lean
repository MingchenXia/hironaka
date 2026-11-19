import Hironaka.Geometry.ProjectiveProjectionMapNaturality
import Hironaka.Geometry.ProjectiveProjectionCenterFinite

/-!
# The SAME actual original finite projection is its literal whole original homogeneous-coordinate map
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter
open Algebra.ProjectiveProjectionFinite Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The exact whole original remaining-variable inclusion, with its original homogeneous degrees. -/
def remainingVariableGradedMap : ProjectiveGrading k n →+*ᵍ ProjectiveGrading k (n + 1) where
  __ := (MvPolynomial.rename Fin.succ).toRingHom
  map_mem hF := hF.rename_isHomogeneous

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (v : Fin (n + 2) → k) (hv : v ≠ 0)

/-- The entire actual original ambient map is the SAME original quotient after the SAME internally chosen original coordinate normalization. -/
def originalCoordinateAmbientGradedMap : ProjectiveGrading k (n + 1) →+*ᵍ
    GradedQuotient.grading (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal :=
  (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal).comp
    (coordinateGradedMap k n v hv)

omit [IsClosedImmersion i] in
/-- The entire actual original quotient and actual coordinate inverse internally prove the original native ambient irrelevant containment. -/
theorem originalCoordinateAmbientGradedMap_irrelevant_le :
    HomogeneousIdeal.irrelevant
      (GradedQuotient.grading (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal) ≤
    (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).map
      (originalCoordinateAmbientGradedMap k n i v hv) :=
  HomogeneousIdeal.irrelevant_le_map_comp (coordinateGradedMap_irrelevant_le k n v hv)
    (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n i))

/-- The whole actual source comparison is internally constructed from the SAME original source and its two actual representative isomorphisms. -/
def representativeCoordinateChange :
    originalScheme k n (representativeIdeal k n i) ⟶
      originalScheme k n (representativeIdeal k n (transformedInclusion k n i v hv)) :=
  (representativeIso k n i).inv ≫ (representativeIso k n (transformedInclusion k n i v hv)).hom

/-- The actual source comparison retains the literal ENTIRE original normalized ambient embedding, without identifying the two original defining ideals. -/
theorem representativeCoordinateChange_embedding :
    representativeCoordinateChange k n i v hv ≫
      originalInclusion k n (representativeIdeal k n (transformedInclusion k n i v hv)) =
    Proj.map (originalCoordinateAmbientGradedMap k n i v hv)
      (originalCoordinateAmbientGradedMap_irrelevant_le k n i v hv) := by
  let e := representativeIso k n i
  have hi : e.inv ≫ i = originalInclusion k n (representativeIdeal k n i) := by
    have h := congrArg (fun m => e.inv ≫ m) (representativeIso_hom_inclusion k n i)
    change e.inv ≫ (e.hom ≫ originalInclusion k n (representativeIdeal k n i)) = e.inv ≫ i at h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm
  change representativeCoordinateChange k n i v hv ≫
      originalInclusion k n (representativeIdeal k n (transformedInclusion k n i v hv)) =
    Proj.map ((GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal).comp
      (coordinateGradedMap k n v hv)) _
  rw [Proj.map_comp]
  change representativeCoordinateChange k n i v hv ≫
      originalInclusion k n (representativeIdeal k n (transformedInclusion k n i v hv)) =
    originalInclusion k n (representativeIdeal k n i) ≫ (coordinateAutomorphism k n v hv).hom
  rw [representativeCoordinateChange, Category.assoc, representativeIso_hom_inclusion]
  change e.inv ≫ (i ≫ (coordinateAutomorphism k n v hv).hom) = _
  rw [← Category.assoc, hi]

/-- The same entire original embedding triangle holds for the genuine prime-relevant native maps used in the projection construction. -/
theorem representativeCoordinateChange_general_embedding :
    representativeCoordinateChange k n i v hv ≫
      General.Morph.map
        (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1))
          (representativeIdeal k n (transformedInclusion k n i v hv)).toIdeal)
        (General.Morph.relevant_of_irrelevant_le _
          (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n (transformedInclusion k n i v hv)))) =
    General.Morph.map (originalCoordinateAmbientGradedMap k n i v hv)
      (General.Morph.relevant_of_irrelevant_le _ (originalCoordinateAmbientGradedMap_irrelevant_le k n i v hv)) := by
  rw [General.Morph.map_eq_native, General.Morph.map_eq_native]
  exact representativeCoordinateChange_embedding k n i v hv

/-- Original outside-ness internally gives genuine relevance of the literal original quotient-normalization-remaining-variable graded map on the SAME original representative. -/
theorem originalVectorProjectionGraded_relevant
    (hout : vectorPoint k n v hv ∉ Set.range i) :
    ∀ p : ProjectiveSpectrum
      (GradedQuotient.grading (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal),
    ¬ HomogeneousIdeal.irrelevant (ProjectiveGrading k n) ≤ p.asHomogeneousIdeal.comap
      ((originalCoordinateAmbientGradedMap k n i v hv).comp (remainingVariableGradedMap k n)) := by
  exact General.Morph.relevant_of_ambient_triangle (remainingVariableGradedMap k n)
    (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1))
      (representativeIdeal k n (transformedInclusion k n i v hv)).toIdeal)
    (originalCoordinateAmbientGradedMap k n i v hv)
    (General.Morph.relevant_of_irrelevant_le _
      (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n (transformedInclusion k n i v hv))))
    (General.Morph.relevant_of_irrelevant_le _ (originalCoordinateAmbientGradedMap_irrelevant_le k n i v hv))
    (partialGradedMap_relevant k n (representativeIdeal k n (transformedInclusion k n i v hv))
      (representative_centre_outside k n (transformedInclusion k n i v hv)
        (transformedInclusion_centre_outside k n i v hv hout)))
    (representativeCoordinateChange k n i v hv) (representativeCoordinateChange_general_embedding k n i v hv)

/-- The SAME already constructed original finite projection is exactly its literal original entire coordinate graded map, on the ORIGINAL source, including all nilpotents. No map-comparison or representative-ideal equality certificate is supplied. -/
theorem projectionFromVector_eq_originalGradedMap
    (hout : vectorPoint k n v hv ∉ Set.range i) :
    projectionFromVector k n i v hv hout = (representativeIso k n i).hom ≫
      General.Morph.map ((originalCoordinateAmbientGradedMap k n i v hv).comp (remainingVariableGradedMap k n))
        (originalVectorProjectionGraded_relevant k n i v hv hout) := by
  have h := General.Morph.map_naturality (remainingVariableGradedMap k n)
    (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1))
      (representativeIdeal k n (transformedInclusion k n i v hv)).toIdeal)
    (originalCoordinateAmbientGradedMap k n i v hv)
    (General.Morph.relevant_of_irrelevant_le _
      (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n (transformedInclusion k n i v hv))))
    (General.Morph.relevant_of_irrelevant_le _ (originalCoordinateAmbientGradedMap_irrelevant_le k n i v hv))
    (partialGradedMap_relevant k n (representativeIdeal k n (transformedInclusion k n i v hv))
      (representative_centre_outside k n (transformedInclusion k n i v hv)
        (transformedInclusion_centre_outside k n i v hv hout)))
    (representativeCoordinateChange k n i v hv) (representativeCoordinateChange_general_embedding k n i v hv)
  let hout' := representative_centre_outside k n (transformedInclusion k n i v hv)
    (transformedInclusion_centre_outside k n i v hv hout)
  rw [h]
  change (representativeIso k n (transformedInclusion k n i v hv)).hom ≫
      projection k n (representativeIdeal k n (transformedInclusion k n i v hv)) hout' =
    (representativeIso k n i).hom ≫ representativeCoordinateChange k n i v hv ≫
      projection k n (representativeIdeal k n (transformedInclusion k n i v hv)) hout'
  simp only [representativeCoordinateChange, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end Hironaka.Geometry.ProjectiveSecant
