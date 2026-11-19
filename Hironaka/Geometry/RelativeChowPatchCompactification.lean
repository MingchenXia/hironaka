import Hironaka.Geometry.RelativeChowProjectiveSpace
import Hironaka.Geometry.RelativeChowCompactification

/-!
# Genuine projective closures of actual subordinate affine patches

The actual affine finite-type immersion is followed by the actual open
projective coefficient patch map. Its native schematic image produces
the actual integral relative projective compactification over the original
scheme, including its actual open immersion and literal structure triangle.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}}

/-- Every actual nonempty affine patch subordinate to an actual affine
base patch has an internally constructed integral projective closure over S. -/
theorem exists_subordinate_compactification
    (p : X ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian S]
    [LocallyOfFiniteType p] (U : X.affineOpens) (V : S.affineOpens)
    [Nonempty U.1] (hUV : U.1 ≤ p ⁻¹ᵁ V.1) :
    ∃ (C : Scheme.{u}) (q : C ⟶ S) (j : U.1.toScheme ⟶ C)
      (d : ℕ) (b : C ⟶ relativeSpace S d),
      IsIntegral C ∧ IsOpenImmersion j ∧ IsDominant j ∧ j ≫ q = U.1.ι ≫ p ∧
      IsClosedImmersion b ∧ b ≫ relativeStructure S d = q := by
  let a : U.1.toScheme ⟶ Spec Γ(S, V.1) :=
    p.resLE V.1 U.1 hUV ≫ V.2.isoSpec.hom
  obtain ⟨d, e, he, hbase⟩ := AffineQuasiProjective.exists_projective_immersion_of_isAffine a
  let := he
  let F := e ≫ affineProjectiveMap V.2.fromSpec d
  let : QuasiCompact F := inferInstance
  let C := F.image
  let q : C ⟶ S := F.imageι ≫ relativeStructure S d
  let j : U.1.toScheme ⟶ C := F.toImage
  refine ⟨C, q, j, d, F.imageι, ProjectiveCompactification.image_isIntegral F,
    inferInstance, inferInstance, ?_, inferInstance, rfl⟩
  calc
    j ≫ q = F ≫ relativeStructure S d := by
      dsimp [j, q]
      rw [← Category.assoc, F.toImage_imageι]
    _ = U.1.ι ≫ p := by
      dsimp [F]
      rw [Category.assoc, affineProjectiveMap_structure, ← Category.assoc, hbase]
      dsimp [a]
      rw [Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, Scheme.Hom.resLE_comp_ι]

end Hironaka.Geometry.RelativeChow
