import Hironaka.Algebra.ProjectiveProjectionFiniteRelevance
import Hironaka.Geometry.ProjectiveProjectionStructure
import Hironaka.Geometry.ProjectiveModification

/-!
# The actual projective projection from the original standard outside centre

The scheme is the native Proj of the entire original homogeneous quotient.
The map is induced by the original partial-coordinate graded map and its
internally proved true relevance. Coordinate preimages and the original
coefficient triangle are exact.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveProjection

open ProjectiveIdeal Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1)))
  (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _))

/-- The actual original projective closed subscheme, without a radical replacement. -/
abbrev originalScheme : Scheme.{u} :=
  Proj (GradedQuotient.grading (ProjectiveGrading k (n + 1)) J.toIdeal)

/-- Its actual original closed immersion in projective space. -/
abbrev originalInclusion : originalScheme k n J ⟶ projectiveSpace k (n + 1) :=
  GradedQuotient.quotientSchemeMap (ProjectiveGrading k (n + 1)) J

/-- The literal projection induced by the original remaining homogeneous coordinates. -/
def projection : originalScheme k n J ⟶ projectiveSpace k n :=
  General.Morph.map (partialGradedMap k n J) (partialGradedMap_relevant k n J hout)

/-- Exact coordinate pullbacks of the actual projective projection. -/
@[simp]
theorem projection_preimage_basicOpen (F : MvPolynomial (Fin (n + 1)) k) :
    projection k n J hout ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) F =
      Proj.basicOpen (GradedQuotient.grading (ProjectiveGrading k (n + 1)) J.toIdeal)
        (partialGradedMap k n J F) := rfl

/-- The actual coordinate localization square is Cartesian for the same projection. -/
theorem projection_isPullback_awayMap {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hd : 0 < d) (hF : F.IsHomogeneous d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (partialGradedMap k n J) F)))
      (Proj.awayι _ (partialGradedMap k n J F) ((partialGradedMap k n J).map_mem hF) hd)
      (Proj.awayι (ProjectiveGrading k n) F hF hd) (projection k n J hout) :=
  General.Morph.isPullback_awayMap (partialGradedMap k n J)
    (partialGradedMap_relevant k n J hout) hd hF

/-- The actual projection retains the original coefficient structure over the field. -/
@[reassoc]
theorem projection_structure :
    projection k n J hout ≫ projectiveSpaceStructure k n =
      originalInclusion k n J ≫ projectiveSpaceStructure k (n + 1) := by
  let q := GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal
  let β := (ProjStructureMap.degreeZeroMap q).comp (projectiveSpaceDegreeZeroEquiv k (n + 1)).toRingHom
  have hc : (ProjStructureMap.degreeZeroMap (partialGradedMap k n J)).comp
      (projectiveSpaceDegreeZeroEquiv k n).toRingHom = β := by
    apply RingHom.ext
    intro a
    apply Subtype.ext
    change Ideal.Quotient.mk J.toIdeal (MvPolynomial.rename Fin.succ (C a)) =
      Ideal.Quotient.mk J.toIdeal (C a)
    rw [MvPolynomial.rename_C]
  have hp := General.Morph.map_toSpec_base (partialGradedMap k n J)
    (partialGradedMap_relevant k n J hout) (projectiveSpaceDegreeZeroEquiv k n).toRingHom β hc
  have hq := ProjStructureMap.map_toSpec_base q (GradedQuotient.irrelevant_le_map _ J)
    (projectiveSpaceDegreeZeroEquiv k (n + 1)).toRingHom β rfl
  exact hp.trans hq.symm

end Hironaka.Geometry.ProjectiveProjection
