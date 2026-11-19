import Hironaka.Geometry.AffineQuasiProjective

/-!
# Actual affine projective compactifications over arbitrary rings

The released image construction already works over any commutative ring.
This derives the quasi-compactness needed for its actual open immersion
and assembles the arbitrary-ring affine compactification internally.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual coefficient structure's quasi-compactness gives the
quasi-compactness of every actual projective morphism from the same source. -/
theorem projectiveMap_isQuasiCompact
    (p : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact p]
    {n : ℕ} (e : X ⟶ projectiveSpace R n) : QuasiCompact e := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace (projectiveSpace R n) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceStructure R n)
  infer_instance

/-- An actual projective immersion of an integral quasi-compact source has
its actual integral projective image compactification over the original ring. -/
theorem exists_projective_compactification
    (p : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X] [QuasiCompact p]
    {n : ℕ} (e : X ⟶ projectiveSpace R n) [IsImmersion e]
    (he : e ≫ projectiveSpaceStructure R n = p) :
    ∃ (C : Scheme.{u}) (q : C ⟶ Spec (CommRingCat.of R)) (j : X ⟶ C),
      IsIntegral C ∧ IsProjectiveOver q ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ q = p := by
  let := projectiveMap_isQuasiCompact p e
  exact ⟨ProjectiveCompactification.closure e, ProjectiveCompactification.closureStructure e,
    ProjectiveCompactification.inclusion e, ProjectiveCompactification.closure_isIntegral e,
    ProjectiveCompactification.structure_isProjective e, inferInstance, inferInstance,
    (ProjectiveCompactification.inclusion_structure e).trans he⟩

/-- A genuine actual affine finite-type source has an internally constructed
integral projective compactification, with no field or Noetherian assumption. -/
theorem exists_affine_projective_compactification
    [IsAffine X] [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType p] :
    ∃ (C : Scheme.{u}) (q : C ⟶ Spec (CommRingCat.of R)) (j : X ⟶ C),
      IsIntegral C ∧ IsProjectiveOver q ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ q = p := by
  obtain ⟨n, e, he, hbase⟩ :=
    AffineQuasiProjective.exists_projective_immersion_of_isAffine p
  let := he
  exact exists_projective_compactification p e hbase

end Hironaka.Geometry.RelativeChow
