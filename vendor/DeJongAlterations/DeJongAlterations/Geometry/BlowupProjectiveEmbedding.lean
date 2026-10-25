import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingLocal
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingCover
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingRepresentation

/-!
# The actual global projective morphism of the native ideal-sheaf blowup

Equal-degree homogeneous generators give native affine Rees projective maps.
Their genuine coefficient restriction and unit-change identities make them
compatible on the actual locally directed subordinate affine-site cover.
Native scheme gluing constructs the global morphism over the original base.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

open ProjectiveIdeal BlowupGluing

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n m : ℕ}

/-- The chosen genuine projective coordinate containing a subordinate affine open. -/
def subordinateCoordinate (j : X ⟶ projectiveSpace R n) (U : SubordinateAffineSite j) :
    Fin (n + 1) := U.2.choose

/-- Its actual coordinate-containment property. -/
theorem subordinateCoordinate_le (j : X ⟶ projectiveSpace R n)
    (U : SubordinateAffineSite j) :
    U.1.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen (subordinateCoordinate j U) := U.2.choose_spec

/-- The actual native local morphisms on the genuine subordinate Rees charts. -/
def formsChartMap (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (U : SubordinateAffineSite j) :
    (subordinateCover ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j) j).X U ⟶
      projectiveSpace R m :=
  localProjectiveMap p j J F hspan ⟨U.1.1, U.1.2⟩
    (subordinateCoordinate j U) (subordinateCoordinate_le j U)

/-- Actual local morphisms agree under every transition of the native subordinate cover. -/
theorem formsChartMap_compatible (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d)
    {U V : SubordinateAffineSite j} (h : U ⟶ V) :
    (subordinateCover ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j) j).trans h ≫
      formsChartMap p j J F hspan V = formsChartMap p j J F hspan U := by
  change (affineDiagram ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j)).map
      (homOfLE h.le) ≫ _ = _
  exact localProjectiveMap_naturality p j J F hspan hF (homOfLE h.le)
    (subordinateCoordinate j U) (subordinateCoordinate j V)
    (subordinateCoordinate_le j U) (subordinateCoordinate_le j V)

/-- The native global map is glued from the actual equal-degree generator maps. -/
def projectiveBlowupMapOfForms (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d) :
    blowup ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j) ⟶
      projectiveSpace R m :=
  (subordinateCover ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j) j).glueMorphismsOfLocallyDirected (formsChartMap p j J F hspan)
      (fun _ => formsChartMap_compatible p j J F hspan hF _)

/-- Restriction to each genuine subordinate Rees chart recovers the original local morphism. -/
@[reassoc]
theorem projectiveBlowupMapOfForms_restrict (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d)
    (U : SubordinateAffineSite j) :
    chartInclusion ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j) U.1 ≫
      projectiveBlowupMapOfForms p j J F hspan hF = formsChartMap p j J F hspan U :=
  (subordinateCover _ j).map_glueMorphismsOfLocallyDirected
    (formsChartMap p j J F hspan) (fun _ => formsChartMap_compatible p j J F hspan hF _) U

/-- The global native projective morphism lies over the original structure map. -/
@[reassoc]
theorem projectiveBlowupMapOfForms_structure (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d) :
    projectiveBlowupMapOfForms p j J F hspan hF ≫ projectiveSpaceStructure R m =
      blowupStructure ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j) ≫ p := by
  apply (subordinateCover _ j).hom_ext
  intro U
  change chartInclusion _ U.1 ≫ _ = chartInclusion _ U.1 ≫ _
  rw [← Category.assoc, projectiveBlowupMapOfForms_restrict]
  dsimp only [formsChartMap]
  rw [localProjectiveMap_structure]
  exact (chartInclusion_structure_assoc _ U.1 p).symm

/-- Every original ideal on an actually projectively embedded scheme has an internally
constructed global projective morphism from its native blowup, over the original base. -/
theorem exists_projectiveBlowupMap [IsNoetherianRing R] (D : X.IdealSheafData)
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ projectiveSpace R n) [IsClosedImmersion j] :
    ∃ (m : ℕ) (q : blowup D ⟶ projectiveSpace R m),
      q ≫ projectiveSpaceStructure R m = blowupStructure D ≫ p := by
  obtain ⟨m, d, F, J, hF, hspan, hD⟩ := exists_fin_sameDegree_representation D j
  subst D
  exact ⟨m, projectiveBlowupMapOfForms p j J F hspan hF,
    projectiveBlowupMapOfForms_structure p j J F hspan hF⟩

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
