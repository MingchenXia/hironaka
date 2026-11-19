import Hironaka.Geometry.ProjectiveSecantProjectionChartRelation
import Hironaka.Algebra.ProjectiveSecantProjectionChartAlgebra

/-!
# Actual original affine source maps to its native whole representative coordinate chart
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection
open Algebra.ProjectiveSecant Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual native homogeneous representative's original source coordinate-chart immersion. -/
abbrev quotientSourceChartι (J : HomogeneousIdeal (ProjectiveGrading k (n + 1))) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (QuotientChart k n J j)) ⟶ originalScheme k n J :=
  Proj.awayι (GradedQuotient.grading (ProjectiveGrading k (n + 1)) J.toIdeal)
    (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j.succ))
    ((GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal).map_mem
      (MvPolynomial.isHomogeneous_X k j.succ)) (by decide : 0 < (1 : ℕ))

/-- The whole native quotient source-chart polynomial presentation retains the actual original quotient immersion triangle. -/
@[reassoc]
theorem quotientSourceChart_polynomial_triangle
    (J : HomogeneousIdeal (ProjectiveGrading k (n + 1))) (j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (fullChartPolynomialMap k n J j)) ≫
      Segre.coordinateChartInclusion (R := k) j.succ =
        quotientSourceChartι k n J j ≫ originalInclusion k n J := by
  have hr : (fullChartPolynomialMap k n J j).comp
      (homogeneousChartEquiv (R := k) j.succ).toRingHom =
        Away.map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal) (MvPolynomial.X j.succ) := by
    apply RingHom.ext
    intro z
    change Away.map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal) (MvPolynomial.X j.succ)
      (homogeneousChartRatioHom j.succ (homogeneousChartDehom j.succ z)) = _
    have he := AlgHom.congr_fun (homogeneousChartRatioHom_comp_dehom (R := k) j.succ) z
    change homogeneousChartRatioHom j.succ (homogeneousChartDehom j.succ z) = z at he
    rw [he]
    rfl
  rw [Segre.coordinateChartInclusion_eq, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((fullChartPolynomialMap k n J j).comp
    (homogeneousChartEquiv (R := k) j.succ).toRingHom)) ≫ _ = _
  rw [hr]
  exact (Proj.awayι_comp_map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal)
    (GradedQuotient.irrelevant_le_map _ J) (by decide : 0 < (1 : ℕ))
      (MvPolynomial.X j.succ) (MvPolynomial.isHomogeneous_X k j.succ)).symm

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The actual original whole affine source range lies in the corresponding actual native homogeneous representative chart. -/
theorem sourceChart_range_subset_representativeChart (j : Fin (n + 1)) :
    Set.range ((tangentSourceChart_isAffine k n i j.succ).fromSpec ≫ (representativeIso k n i).hom) ⊆
      Set.range (quotientSourceChartι k n (representativeIdeal k n i) j) := by
  rintro _ ⟨z, rfl⟩
  change ((tangentSourceChart_isAffine k n i j.succ).fromSpec ≫ (representativeIso k n i).hom) z ∈
    (quotientSourceChartι k n (representativeIdeal k n i) j).opensRange
  rw [Proj.opensRange_awayι]
  change ((representativeIso k n i).hom ≫ originalInclusion k n (representativeIdeal k n i))
    ((tangentSourceChart_isAffine k n i j.succ).fromSpec z) ∈ nativeCoordinateOpen j.succ
  rw [representativeIso_hom_inclusion]
  have hz : (tangentSourceChart_isAffine k n i j.succ).fromSpec z ∈
      i ⁻¹ᵁ nativeCoordinateOpen j.succ := by
    exact (congrArg (fun Z : Set X =>
      (tangentSourceChart_isAffine k n i j.succ).fromSpec z ∈ Z)
        (tangentSourceChart_isAffine k n i j.succ).range_fromSpec).mp ⟨z, rfl⟩
  exact hz

/-- The native open-immersion universal property constructs the whole actual original affine source's representative-chart lift internally. -/
def originalRepresentativeChartLift (j : Fin (n + 1)) :
    Spec (CommRingCat.of Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j.succ)) ⟶
      Spec (CommRingCat.of (QuotientChart k n (representativeIdeal k n i) j)) :=
  IsOpenImmersion.lift (quotientSourceChartι k n (representativeIdeal k n i) j)
    ((tangentSourceChart_isAffine k n i j.succ).fromSpec ≫ (representativeIso k n i).hom)
      (sourceChart_range_subset_representativeChart k n i j)

/-- The internally constructed actual lift retains the entire original affine-source/representative triangle. -/
@[reassoc]
theorem originalRepresentativeChartLift_fac (j : Fin (n + 1)) :
    originalRepresentativeChartLift k n i j ≫ quotientSourceChartι k n (representativeIdeal k n i) j =
      (tangentSourceChart_isAffine k n i j.succ).fromSpec ≫ (representativeIso k n i).hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- Native Spec faithfulness reads the actual whole original representative-chart ring map. -/
def originalRepresentativeChartRingMap (j : Fin (n + 1)) :
    QuotientChart k n (representativeIdeal k n i) j →+* Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j.succ) :=
  (Spec.preimage (originalRepresentativeChartLift k n i j)).hom

/-- The internally produced whole original ring map is exactly the actual original scheme chart lift. -/
theorem originalRepresentativeChartRingMap_spec (j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (originalRepresentativeChartRingMap k n i j)) =
      originalRepresentativeChartLift k n i j := Spec.map_preimage _

/-- The WHOLE actual representative-chart ring map composed with the whole native polynomial presentation is exactly the WHOLE original affine source polynomial map. -/
theorem originalRepresentativeChartRingMap_comp_polynomial (j : Fin (n + 1)) :
    (originalRepresentativeChartRingMap k n i j).comp
      (fullChartPolynomialMap k n (representativeIdeal k n i) j) =
        tangentChartPolynomialMap k n i j.succ := by
  have he : CommRingCat.ofHom (fullChartPolynomialMap k n (representativeIdeal k n i) j) ≫
      CommRingCat.ofHom (originalRepresentativeChartRingMap k n i j) =
        CommRingCat.ofHom (tangentChartPolynomialMap k n i j.succ) := by
    apply Spec.map_injective
    apply (cancel_mono (Segre.coordinateChartInclusion (R := k) j.succ)).mp
    rw [Spec.map_comp, originalRepresentativeChartRingMap_spec, Category.assoc,
      quotientSourceChart_polynomial_triangle, ← Category.assoc, originalRepresentativeChartLift_fac,
      Category.assoc, representativeIso_hom_inclusion, tangentChartPolynomialMap_spec]
  exact congrArg (fun f : CommRingCat.of (CoordinateRing k j.succ) ⟶
    CommRingCat.of Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j.succ) => f.hom) he

/-- The WHOLE actual representative chart map carries the WHOLE native projection chart map to exactly the literal original remaining-ratio algebra map. -/
theorem originalRepresentativeChartRingMap_comp_projection (j : Fin (n + 1)) :
    (originalRepresentativeChartRingMap k n i j).comp
      (projectionChartMap k n (representativeIdeal k n i) j) =
        sourceProjectionChartMap k n j (tangentChartPolynomialMap k n i j.succ) := by
  apply RingHom.ext
  intro z
  change originalRepresentativeChartRingMap k n i j
    (fullChartPolynomialMap k n (representativeIdeal k n i) j
      (MvPolynomial.rename (chartIndexLift n j) (homogeneousChartDehom j z))) =
    tangentChartPolynomialMap k n i j.succ
      (MvPolynomial.rename (chartIndexLift n j) (homogeneousChartDehom j z))
  exact RingHom.congr_fun (originalRepresentativeChartRingMap_comp_polynomial k n i j) _

/-- The SAME actual original finite scheme projection has exactly the literal original remaining-ratio chart map on the WHOLE actual source section ring. -/
@[reassoc]
theorem original_closedProjection_sourceChart_triangle
    (hout : Algebra.ProjectiveProjectionFinite.centrePoint k n ∉ Set.range i) (j : Fin (n + 1)) :
    (tangentSourceChart_isAffine k n i j.succ).fromSpec ≫ closedProjection k n i hout =
      Spec.map (CommRingCat.ofHom (sourceProjectionChartMap k n j (tangentChartPolynomialMap k n i j.succ))) ≫
        Proj.awayι (ProjectiveGrading k n) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)
          (by decide : 0 < (1 : ℕ)) := by
  calc
    _ = originalRepresentativeChartLift k n i j ≫ quotientSourceChartι k n (representativeIdeal k n i) j ≫
        projection k n (representativeIdeal k n i) (representative_centre_outside k n i hout) := by
      rw [originalRepresentativeChartLift_fac_assoc]
      rfl
    _ = originalRepresentativeChartLift k n i j ≫
        Spec.map (CommRingCat.ofHom (projectionChartMap k n (representativeIdeal k n i) j)) ≫
          Proj.awayι (ProjectiveGrading k n) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)
            (by decide : 0 < (1 : ℕ)) := by
      exact congrArg (fun f => originalRepresentativeChartLift k n i j ≫ f)
        (projection_isPullback_coordinate k n (representativeIdeal k n i)
          (representative_centre_outside k n i hout) j).w.symm
    _ = _ := by
      rw [← originalRepresentativeChartRingMap_spec, ← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((originalRepresentativeChartRingMap k n i j).comp
        (projectionChartMap k n (representativeIdeal k n i) j))) ≫ _ = _
      rw [originalRepresentativeChartRingMap_comp_projection]

end Hironaka.Geometry.ProjectiveSecant
