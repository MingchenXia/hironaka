import Hironaka.Algebra.ReesPrincipalFactor
import Hironaka.Geometry.AffineBlowupChart
import Hironaka.Geometry.ProjClosedImmersion
import Hironaka.Geometry.ProjStructureMap

/-!
# Removing a nonzero principal factor from an actual affine blowup centre

The actual Rees substitution `T ↦ c T` and its graded inverse induce inverse
native Proj morphisms. They commute with the original affine structure maps
and identify the genuine degree-one basic opens.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Hironaka.Algebra.ReesPrincipalFactor

namespace Hironaka.Geometry.BlowupPrincipalFactor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The irrelevant containment is produced from the genuine Rees surjection. -/
theorem reesScale_irrelevant (c : A) (I : Ideal A) :
    HomogeneousIdeal.irrelevant (reesGrading (scaledIdeal c I)) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesScaleGraded c I) :=
  ProjClosedImmersion.irrelevant_le_map_of_surjective _ (reesScale_surjective c I)

/-- The actual native Proj morphism induced by `T ↦ c T`. -/
def blowupPrincipalFactorMap (c : A) (I : Ideal A) :
    affineBlowup (scaledIdeal c I) ⟶ affineBlowup I :=
  Proj.map (reesScaleGraded c I) (reesScale_irrelevant c I)

/-- The actual morphism commutes with the original base structure maps. -/
theorem blowupPrincipalFactorMap_structure (c : A) (I : Ideal A) :
    blowupPrincipalFactorMap c I ≫ affineBlowupStructure I =
      affineBlowupStructure (scaledIdeal c I) :=
  ProjStructureMap.map_toSpec_base (reesScaleGraded c I) (reesScale_irrelevant c I)
    (reesDegreeZeroEquiv I).toRingHom (reesDegreeZeroEquiv (scaledIdeal c I)).toRingHom
    (reesScaleGraded_degreeZero c I)

/-- The actual canonical morphism is a closed immersion even before cancellation. -/
theorem blowupPrincipalFactorMap_isClosedImmersion (c : A) (I : Ideal A) :
    IsClosedImmersion (blowupPrincipalFactorMap c I) :=
  ProjClosedImmersion.isClosedImmersion_map _ (reesScale_surjective c I) _

variable [IsDomain A]

/-- The inverse containment likewise follows from the constructed graded inverse. -/
theorem reesScaleInverse_irrelevant (c : A) (I : Ideal A) (hc : c ≠ 0) :
    HomogeneousIdeal.irrelevant (reesGrading I) ≤
      (HomogeneousIdeal.irrelevant (reesGrading (scaledIdeal c I))).map
        (reesScaleInverseGraded c I hc) :=
  ProjClosedImmersion.irrelevant_le_map_of_surjective _
    (reesScaleInverseGraded_surjective c I hc)

/-- The actual inverse native Proj morphism, with no supplied comparison map. -/
def blowupPrincipalFactorInverse (c : A) (I : Ideal A) (hc : c ≠ 0) :
    affineBlowup I ⟶ affineBlowup (scaledIdeal c I) :=
  Proj.map (reesScaleInverseGraded c I hc) (reesScaleInverse_irrelevant c I hc)

/-- Removing a nonzero principal factor gives a genuine native blowup isomorphism. -/
def blowupPrincipalFactorIso (c : A) (I : Ideal A) (hc : c ≠ 0) :
    affineBlowup (scaledIdeal c I) ≅ affineBlowup I where
  hom := blowupPrincipalFactorMap c I
  inv := blowupPrincipalFactorInverse c I hc
  hom_inv_id := by
    dsimp only [blowupPrincipalFactorMap, blowupPrincipalFactorInverse, affineBlowup]
    rw [← Proj.map_comp]
    simpa only [reesScaleGraded_comp_inverse] using
      (Proj.map_id (𝒜 := reesGrading (scaledIdeal c I)))
  inv_hom_id := by
    dsimp only [blowupPrincipalFactorMap, blowupPrincipalFactorInverse, affineBlowup]
    rw [← Proj.map_comp]
    simpa only [reesScaleInverseGraded_comp] using (Proj.map_id (𝒜 := reesGrading I))

/-- The isomorphism is over the original coefficient spectrum. -/
@[reassoc]
theorem blowupPrincipalFactorIso_hom_structure (c : A) (I : Ideal A) (hc : c ≠ 0) :
    (blowupPrincipalFactorIso c I hc).hom ≫ affineBlowupStructure I =
      affineBlowupStructure (scaledIdeal c I) :=
  blowupPrincipalFactorMap_structure c I

/-- The inverse isomorphism has the same actual base compatibility. -/
@[reassoc]
theorem blowupPrincipalFactorIso_inv_structure (c : A) (I : Ideal A) (hc : c ≠ 0) :
    (blowupPrincipalFactorIso c I hc).inv ≫ affineBlowupStructure (scaledIdeal c I) =
      affineBlowupStructure I := by
  rw [← blowupPrincipalFactorIso_hom_structure c I hc, Iso.inv_hom_id_assoc]

/-- In particular the comparison is a proper native morphism without any FG assumption. -/
theorem blowupPrincipalFactorIso_hom_isProper (c : A) (I : Ideal A) (hc : c ≠ 0) :
    IsProper (blowupPrincipalFactorIso c I hc).hom := by
  infer_instance

/-- Exact comparison of the actual degree-one basic opens used in node resolution. -/
theorem blowupPrincipalFactorIso_preimage_chart (c : A) (I : Ideal A) (hc : c ≠ 0)
    (a : A) (ha : a ∈ I) :
    (blowupPrincipalFactorIso c I hc).hom ⁻¹ᵁ affineBlowupChartOpen I a ha =
      affineBlowupChartOpen (scaledIdeal c I) (c * a) (mul_mem_scaledIdeal c I a ha) := by
  change Proj.map (reesScaleGraded c I) (reesScale_irrelevant c I) ⁻¹ᵁ
      Proj.basicOpen (reesGrading I) (reesDegreeOne I a ha) = _
  rw [Proj.map_preimage_basicOpen, reesScaleGraded_degreeOne]
  rfl

/-- The resulting comparison of the actual open subschemes themselves. -/
def blowupPrincipalFactorChartIso (c : A) (I : Ideal A) (hc : c ≠ 0)
    (a : A) (ha : a ∈ I) :
    (affineBlowupChartOpen (scaledIdeal c I) (c * a) (mul_mem_scaledIdeal c I a ha)).toScheme ≅
      (affineBlowupChartOpen I a ha).toScheme :=
  ((affineBlowup (scaledIdeal c I)).isoOfEq
    (blowupPrincipalFactorIso_preimage_chart c I hc a ha).symm).trans
      ((blowupPrincipalFactorIso c I hc).hom.preimageIso (affineBlowupChartOpen I a ha))

/-- This is the restriction of the actual global comparison, with its genuine inclusions. -/
@[reassoc]
theorem blowupPrincipalFactorChartIso_hom_ι (c : A) (I : Ideal A) (hc : c ≠ 0)
    (a : A) (ha : a ∈ I) :
    (blowupPrincipalFactorChartIso c I hc a ha).hom ≫ (affineBlowupChartOpen I a ha).ι =
      (affineBlowupChartOpen (scaledIdeal c I) (c * a) (mul_mem_scaledIdeal c I a ha)).ι ≫
        (blowupPrincipalFactorIso c I hc).hom := by
  dsimp only [blowupPrincipalFactorChartIso, Iso.trans_hom]
  rw [Category.assoc, Scheme.Hom.preimageIso_hom_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

/-- The actual native chart comparison is also over the original coefficient spectrum. -/
theorem blowupPrincipalFactorChartIso_structure (c : A) (I : Ideal A) (hc : c ≠ 0)
    (a : A) (ha : a ∈ I) :
    (blowupPrincipalFactorChartIso c I hc a ha).hom ≫
        (affineBlowupChartOpen I a ha).ι ≫ affineBlowupStructure I =
      (affineBlowupChartOpen (scaledIdeal c I) (c * a) (mul_mem_scaledIdeal c I a ha)).ι ≫
        affineBlowupStructure (scaledIdeal c I) := by
  rw [← Category.assoc, blowupPrincipalFactorChartIso_hom_ι, Category.assoc,
    blowupPrincipalFactorIso_hom_structure]

end Hironaka.Geometry.BlowupPrincipalFactor
