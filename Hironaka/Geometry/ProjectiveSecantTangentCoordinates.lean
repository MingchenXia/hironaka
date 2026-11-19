import Hironaka.Geometry.ProjectiveSecantTangentChart
import Hironaka.Geometry.ProjectiveProjectionClosedSubscheme

/-!
# The entire original tangent coordinate map is the native homogeneous-fraction coordinate map
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

private local instance tangentNativeHomogeneousChartAlgebra (j : Fin (n + 2)) :
    Algebra k (HomogeneousChartRing k j) := homogeneousChartAlgebra j

/-- Native homogeneous fraction sections retain the entire actual affine chart immersion triangle. -/
@[reassoc]
theorem nativeAwayToSection_spec (j : Fin (n + 2)) :
    Spec.map (Proj.awayToSection (ProjectiveGrading k (n + 1)) (X j)) ≫
      Proj.awayι (ProjectiveGrading k (n + 1)) (X j) (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ)) =
        (nativeCoordinateOpen_isAffine (R := k) j).fromSpec := by
  let U := nativeCoordinateOpen (R := k) j
  let hU := nativeCoordinateOpen_isAffine (R := k) j
  let : IsIso U.toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  apply (cancel_epi U.toSpecΓ).mp
  rw [← Category.assoc]
  change (Proj.basicOpenIsoSpec (ProjectiveGrading k (n + 1)) (X j)
    (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ))).hom ≫
      ((Proj.basicOpenIsoSpec (ProjectiveGrading k (n + 1)) (X j)
        (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ))).inv ≫ U.ι) = U.toSpecΓ ≫ hU.fromSpec
  rw [Iso.hom_inv_id_assoc, hU.toSpecΓ_fromSpec]

/-- The actual native homogeneous coordinate-section isomorphism retains the same literal original polynomial chart. -/
@[reassoc]
theorem nativeCoordinateSectionsIso_spec (j : Fin (n + 2)) :
    Spec.map (nativeCoordinateSectionsIso (R := k) j).hom ≫
      Segre.coordinateChartInclusion (R := k) j =
        (nativeCoordinateOpen_isAffine (R := k) j).fromSpec := by
  rw [nativeCoordinateSectionsIso, Iso.trans_hom, nativeHomogeneousChartSectionsIso_hom]
  change Spec.map ((homogeneousChartEquiv (R := k) j).toRingEquiv.toCommRingCatIso.inv ≫
    Proj.awayToSection (ProjectiveGrading k (n + 1)) (X j)) ≫ Segre.coordinateChartInclusion (R := k) j = _
  have he : Spec.map (homogeneousChartEquiv (R := k) j).toRingEquiv.toCommRingCatIso.inv ≫
      Spec.map (homogeneousChartEquiv (R := k) j).toRingEquiv.toCommRingCatIso.hom = 𝟙 _ := by
    rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  rw [Spec.map_comp, Segre.coordinateChartInclusion_eq, Category.assoc,
    ← Category.assoc (Spec.map (homogeneousChartEquiv (R := k) j).toRingEquiv.toCommRingCatIso.inv),
    he, Category.id_comp]
  exact nativeAwayToSection_spec k n j

/-- The two whole original coordinate ring isomorphisms agree by actual scheme monomorphy and native Spec faithfulness. -/
theorem tangentCoordinateRingIso_eq_native (j : Fin (n + 2)) :
    tangentCoordinateRingIso k n j = nativeCoordinateSectionsIso (R := k) j := by
  apply Iso.ext
  apply Spec.map_injective
  apply (cancel_mono (Segre.coordinateChartInclusion (R := k) j)).mp
  rw [tangentCoordinateRingIso_spec, nativeCoordinateSectionsIso_spec]

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- The actual whole original affine defining ideal is the actual whole original homogeneous representative's dehomogenized ideal. -/
theorem tangent_coordinateIdeal_eq (j : Fin (n + 2)) :
    (i.ker.ideal ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine (R := k) j⟩).comap
      (tangentCoordinateRingIso k n j).hom.hom =
        (representativeIdeal k n i).toIdeal.map (coordinateDehom j).toRingHom := by
  rw [tangentCoordinateRingIso_eq_native, ← representativeInclusion_ker k n i]
  exact homogeneousQuotient_coordinateSectionIdeal (representativeIdeal k n i) j

end Hironaka.Geometry.ProjectiveSecant
