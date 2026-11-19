import Hironaka.Geometry.ProjectiveProjection
import Hironaka.Algebra.ProjectiveProjectionFiniteChartRelation
import Hironaka.Algebra.ProjectiveProjectionFiniteChartCompatibility

/-!
# Actual finite projective projection from the standard outside centre

This proves finiteness of the literal native scheme projection, with its
original homogeneous coordinate quotient and coefficient triangle.
General-position birationality and generic etaleness are separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open TopologicalSpace

namespace Hironaka.Geometry.ProjectiveProjection

open ProjectiveIdeal Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1)))
  (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _))

/-- The original target is covered by the actual homogeneous coordinate spectra. -/
@[simps! I₀ X f]
def coordinateCover : (projectiveSpace k n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1)) (fun j => Spec (.of (HomogeneousChartRing k j)))
    (fun j => Proj.awayι (ProjectiveGrading k n) (X j) (MvPolynomial.isHomogeneous_X k j)
      (by decide : 0 < (1 : ℕ))) (by
      intro p
      have hp : p ∈ ⨆ j : Fin (n + 1), nativeCoordinateOpen (R := k) j := by
        rw [iSup_nativeCoordinateOpen_eq_top]
        trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hp
      refine ⟨j, ?_⟩
      change p ∈ (Proj.awayι (ProjectiveGrading k n) (X j)
        (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ))).opensRange
      rwa [Proj.opensRange_awayι])

/-- The actual finite coordinate map is an actual Cartesian chart of this same projection. -/
theorem projection_isPullback_coordinate (j : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (projectionChartMap k n J j)))
      (Proj.awayι (GradedQuotient.grading (ProjectiveGrading k (n + 1)) J.toIdeal)
        (Ideal.Quotient.mk J.toIdeal (X j.succ))
        ((GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal).map_mem
          (MvPolynomial.isHomogeneous_X k j.succ)) (by decide : 0 < (1 : ℕ)))
      (Proj.awayι (ProjectiveGrading k n) (X j) (MvPolynomial.isHomogeneous_X k j)
        (by decide : 0 < (1 : ℕ))) (projection k n J hout) := by
  rw [projectionChartMap_eq_native]
  exact General.Morph.isPullback_awayMap_of_eq (partialGradedMap k n J)
    (partialGradedMap_relevant k n J hout) (by decide : 0 < (1 : ℕ))
    (MvPolynomial.isHomogeneous_X k j)
    ((GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal).map_mem
      (MvPolynomial.isHomogeneous_X k j.succ)) (partialGradedMap_X k n J j) _

/-- Source 2.11, finiteness from an actual standard outside centre: the literal
projection on the actual original homogeneous quotient is finite. No monic
relation, finite map, chart comparison or projection certificate is supplied. -/
theorem projection_isFinite : IsFinite (projection k n J hout) := by
  apply IsZariskiLocalAtTarget.of_openCover (coordinateCover k n)
  intro j
  let H := (projection_isPullback_coordinate k n J hout j).flip
  change IsFinite (pullback.snd (projection k n J hout)
    (Proj.awayι (ProjectiveGrading k n) (X j) (MvPolynomial.isHomogeneous_X k j)
      (by decide : 0 < (1 : ℕ))))
  apply (MorphismProperty.cancel_left_of_respectsIso @IsFinite H.isoPullback.hom _).mp
  rw [H.isoPullback_hom_snd]
  exact (IsFinite.SpecMap_iff _).mpr (projectionChartMap_finite k n J j hout)

/-- The actual original projective source retains its projectivity over the field. -/
theorem projection_source_isProjectiveOver :
    IsProjectiveOver (projection k n J hout ≫ projectiveSpaceStructure k n) := by
  refine ⟨n + 1, originalInclusion k n J, inferInstance, ?_⟩
  exact (projection_structure k n J hout).symm

end Hironaka.Geometry.ProjectiveProjection
