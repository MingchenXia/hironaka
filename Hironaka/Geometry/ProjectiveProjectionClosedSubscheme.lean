import Hironaka.Geometry.ProjectiveProjectionFinite
import Hironaka.Geometry.ProjectiveIdealRepresentation

/-!
# Finite projection of any actual projective closed subscheme avoiding the standard centre

The actual homogeneous ideal is internally represented from the original
closed immersion's entire kernel. The resulting native closed-subscheme
isomorphism preserves that literal original immersion. Thus the finite
projection is a morphism from the original source, not a replacement model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveProjection

open ProjectiveIdeal Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The internally represented whole original homogeneous ideal of the given closed immersion. -/
def representativeIdeal : HomogeneousIdeal (ProjectiveGrading k (n + 1)) :=
  nativeHomogeneousRepresentative i.ker

omit [IsClosedImmersion i] in
/-- The representative quotient closed immersion has exactly the original whole kernel. -/
theorem representativeInclusion_ker :
    (originalInclusion k n (representativeIdeal k n i)).ker = i.ker :=
  nativeHomogeneousRepresentative_quotientIdealSheaf i.ker

/-- The original source is canonically isomorphic to its internally represented native Proj quotient. -/
def representativeIso : X ≅ originalScheme k n (representativeIdeal k n i) := by
  let q := originalInclusion k n (representativeIdeal k n i)
  let h : q.ker = i.ker := representativeInclusion_ker k n i
  let : IsIso (IsClosedImmersion.lift q i h.le) := IsClosedImmersion.isIso_lift q i h
  exact asIso (IsClosedImmersion.lift q i h.le)

/-- The actual homogeneous representative preserves the literal original closed immersion. -/
@[reassoc (attr := simp)]
theorem representativeIso_hom_inclusion :
    (representativeIso k n i).hom ≫ originalInclusion k n (representativeIdeal k n i) = i :=
  IsClosedImmersion.lift_fac _ _ _

/-- Outside-ness is transported from the original closed source, not supplied for a model. -/
theorem representative_centre_outside (hout : centrePoint k n ∉ Set.range i) :
    centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ ((representativeIdeal k n i).toIdeal : Set _) := by
  have hsupport : ProjectiveSpectrum.zeroLocus _ ((representativeIdeal k n i).toIdeal : Set _) =
      Set.range i := by
    rw [← GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus]
    change ((originalInclusion k n (representativeIdeal k n i)).ker.support :
      Set (projectiveSpace k (n + 1))) = Set.range i
    rw [representativeInclusion_ker, Scheme.Hom.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq]
  rwa [hsupport]

/-- The actual finite projection from the original given closed projective source. -/
def closedProjection (hout : centrePoint k n ∉ Set.range i) : X ⟶ projectiveSpace k n :=
  (representativeIso k n i).hom ≫ projection k n (representativeIdeal k n i)
    (representative_centre_outside k n i hout)

/-- Finiteness holds for the literal morphism from the original closed subscheme. -/
theorem closedProjection_isFinite (hout : centrePoint k n ∉ Set.range i) :
    IsFinite (closedProjection k n i hout) := by
  let : IsFinite (projection k n (representativeIdeal k n i)
      (representative_centre_outside k n i hout)) := projection_isFinite _ _ _ _
  dsimp only [closedProjection]
  infer_instance

/-- The finite projection of the original source retains its actual coefficient triangle. -/
@[reassoc]
theorem closedProjection_structure (hout : centrePoint k n ∉ Set.range i) :
    closedProjection k n i hout ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) := by
  simp only [closedProjection, Category.assoc, projection_structure,
    representativeIso_hom_inclusion_assoc]

/-- Exact coordinate-open pullbacks on the original given closed subscheme. -/
@[simp]
theorem closedProjection_preimage_coordinate (hout : centrePoint k n ∉ Set.range i)
    (j : Fin (n + 1)) :
    closedProjection k n i hout ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) (MvPolynomial.X j) =
      i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j.succ) := by
  conv_rhs => rw [← representativeIso_hom_inclusion k n i]
  simp only [closedProjection, Scheme.Hom.comp_preimage, projection_preimage_basicOpen,
    partialGradedMap_X, originalInclusion, GradedQuotient.quotientSchemeMap,
    Proj.map_preimage_basicOpen, GradedQuotient.gradedMk_apply]

/-- The finite projection retains projectivity of the actual original source over the field. -/
theorem closedProjection_source_isProjectiveOver (hout : centrePoint k n ∉ Set.range i) :
    IsProjectiveOver (closedProjection k n i hout ≫ projectiveSpaceStructure k n) :=
  ⟨n + 1, i, inferInstance, (closedProjection_structure k n i hout).symm⟩

end Hironaka.Geometry.ProjectiveProjection
