import Hironaka.Geometry.ProjectiveSecantSeparableCenterLift
import Hironaka.Geometry.ProjectiveSecantProjectionScalarComparison

/-!
# Actual original parameter centres avoid the unchanged scalar source and have integral closure coefficients
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original entire image avoidance internally supplies actual scalar-source centre outside-ness. -/
theorem scalarCenter_outside_of_original_image
    (k L : Type u) [Field k] [Field L] [Algebra k L] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1))
    (p : Spec (.of L) ⟶ projectiveSpace L (n + 1))
    (hout : projectiveCoefficientMap (algebraMap k L) (n + 1) (pointImage L n p) ∉ Set.range i) :
    pointImage L n p ∉ Set.range (scalarClosedInclusion k L (algebraMap k L) n i) := by
  rintro ⟨x, hx⟩
  apply hout
  refine ⟨pullback.fst (i ≫ projectiveSpaceStructure k (n + 1))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) x, ?_⟩
  have H := congrArg (fun m => m x) (scalarClosedInclusion_original k L (algebraMap k L) n i)
  simpa only [Scheme.Hom.comp_apply, hx] using H.symm

/-- The actual internally chosen original separable-closure embedding is integral by its actual coefficient tower. -/
theorem originalSeparableClosureEmbedding_isIntegral
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L] :
    (originalSeparableClosureEmbedding k L).toRingHom.IsIntegral := by
  let K := SeparableClosure k
  let χ := originalSeparableClosureEmbedding k L
  let : Algebra L K := χ.toRingHom.toAlgebra
  let : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => (χ.commutes c).symm
  let : Algebra.IsAlgebraic L K := Algebra.IsAlgebraic.tower_top (K := k) (L := L)
  exact algebraMap_isIntegral_iff.mpr inferInstance

end Hironaka.Geometry.ProjectiveSecant
