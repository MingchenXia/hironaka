import Hironaka.Geometry.ProjectiveRationalPointCoordinatesLift
import Hironaka.Algebra.ProjectiveSecantTangentAffine

/-!
# Actual original coordinate presentations of a projective closed immersion
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual coordinate-section ring isomorphism is recovered from the two actual native scheme chart isomorphisms. -/
def tangentCoordinateRingIso (j : Fin (n + 2)) :
    CommRingCat.of (CoordinateRing k j) ≅ Γ(projectiveSpace k (n + 1), nativeCoordinateOpen j) where
  hom := Spec.preimage ((nativeCoordinateOpen_isAffine (R := k) j).isoSpec.inv ≫
    (Segre.coordinateChartIso (R := k) j).hom)
  inv := Spec.preimage ((Segre.coordinateChartIso (R := k) j).inv ≫
    (nativeCoordinateOpen_isAffine (R := k) j).isoSpec.hom)
  hom_inv_id := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    simp
  inv_hom_id := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    simp

/-- The whole original native coordinate-section isomorphism retains the actual original scheme chart triangle. -/
@[reassoc]
theorem tangentCoordinateRingIso_spec (j : Fin (n + 2)) :
    Spec.map (tangentCoordinateRingIso k n j).hom ≫ Segre.coordinateChartInclusion (R := k) j =
      (nativeCoordinateOpen_isAffine (R := k) j).fromSpec := by
  rw [tangentCoordinateRingIso, Spec.map_preimage, Segre.coordinateChartInclusion, Category.assoc,
    Iso.hom_inv_id_assoc]
  rfl

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The actual original inverse-image coordinate open is affine by the original closed immersion. -/
theorem tangentSourceChart_isAffine (j : Fin (n + 2)) : IsAffineOpen (i ⁻¹ᵁ nativeCoordinateOpen j) :=
  (nativeCoordinateOpen_isAffine (R := k) j).preimage i

/-- The entire original polynomial presentation is the actual original coordinate-section map. -/
def tangentChartPolynomialMap (j : Fin (n + 2)) :
    CoordinateRing k j →+* Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j) :=
  (i.app (nativeCoordinateOpen j)).hom.comp (tangentCoordinateRingIso k n j).hom.hom

/-- The original closed immersion proves whole-ring surjectivity internally. -/
theorem tangentChartPolynomialMap_surjective (j : Fin (n + 2)) :
    Function.Surjective (tangentChartPolynomialMap k n i j) :=
  (i.app_surjective _ (nativeCoordinateOpen_isAffine (R := k) j)).comp
    (ConcreteCategory.bijective_of_isIso (tangentCoordinateRingIso k n j).hom).surjective

/-- The actual original affine coordinate map retains the whole original scheme embedding triangle. -/
@[reassoc]
theorem tangentChartPolynomialMap_spec (j : Fin (n + 2)) :
    Spec.map (CommRingCat.ofHom (tangentChartPolynomialMap k n i j)) ≫
      Segre.coordinateChartInclusion (R := k) j =
        (tangentSourceChart_isAffine k n i j).fromSpec ≫ i := by
  change Spec.map ((tangentCoordinateRingIso k n j).hom ≫ i.app (nativeCoordinateOpen j)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, tangentCoordinateRingIso_spec]
  simpa only [Scheme.Hom.appLE_eq_app] using
    (IsAffineOpen.SpecMap_appLE_fromSpec i (nativeCoordinateOpen_isAffine (R := k) j)
      (tangentSourceChart_isAffine k n i j) le_rfl)

/-- The entire actual coordinate polynomial kernel is literally the original ideal sheaf's affine ideal in the actual coordinates. -/
theorem tangentChartPolynomialMap_ker (j : Fin (n + 2)) :
    RingHom.ker (tangentChartPolynomialMap k n i j) =
      (i.ker.ideal ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine (R := k) j⟩).comap
        (tangentCoordinateRingIso k n j).hom.hom := by
  rw [Scheme.Hom.ker_apply]
  rfl

end Hironaka.Geometry.ProjectiveSecant
