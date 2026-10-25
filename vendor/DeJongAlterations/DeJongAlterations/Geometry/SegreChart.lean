import DeJongAlterations.Algebra.SegreChart
import DeJongAlterations.Geometry.ProjectiveIdealCharts
import DeJongAlterations.Projective
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Native affine chart embeddings for the Segre construction

The actual surjective Segre chart coordinate map produces a closed immersion
into the native coordinate open of the target projective space. Its composite
to projective space preserves the original coefficient structure map.
The tensor spectrum is the actual product of the two affine source charts.

Global compatibility and gluing into a morphism from the product of projective
spaces are separate remaining obligations.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Algebra.Segre

noncomputable section

namespace DeJongAlterations.Geometry.Segre

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {m n d : ℕ}

/-- The actual native Proj coordinate chart isomorphism to its polynomial coordinate spectrum. -/
def coordinateChartIso (i : Fin (d + 1)) :
    (Proj.basicOpen (projectiveSpaceGrading R d) (MvPolynomial.X i)).toScheme ≅
      Spec (CommRingCat.of (CoordinateRing R i)) :=
  (Proj.basicOpenIsoSpec (projectiveSpaceGrading R d) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))).trans
    (Scheme.Spec.mapIso (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.symm.op)

/-- The actual affine polynomial coordinate chart map into native projective space. -/
def coordinateChartInclusion (i : Fin (d + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i)) ⟶ projectiveSpace R d :=
  (coordinateChartIso (R := R) i).inv ≫
    (Proj.basicOpen (projectiveSpaceGrading R d) (MvPolynomial.X i)).ι

instance coordinateChartInclusion_isOpenImmersion (i : Fin (d + 1)) :
    IsOpenImmersion (coordinateChartInclusion (R := R) i) := by
  unfold coordinateChartInclusion
  infer_instance

/-- The actual polynomial chart map factors through the native homogeneous-chart immersion. -/
theorem coordinateChartInclusion_eq (i : Fin (d + 1)) :
    coordinateChartInclusion (R := R) i =
      Spec.map (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.hom ≫
        Proj.awayι (projectiveSpaceGrading R d) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ)) := by
  change (Spec.map (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.hom ≫
      (Proj.basicOpenIsoSpec (projectiveSpaceGrading R d) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))).inv) ≫ _ = _
  rw [Category.assoc]
  rfl

private theorem awayι_structure (i : Fin (d + 1)) :
    Proj.awayι (projectiveSpaceGrading R d) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ)) ≫
      projectiveSpaceStructure R d =
    Spec.map (CommRingCat.ofHom (homogeneousChartCoefficients (R := R) i)) := by
  unfold projectiveSpaceStructure
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The actual affine coordinate chart preserves the original coefficient-ring structure. -/
theorem coordinateChartInclusion_structure (i : Fin (d + 1)) :
    coordinateChartInclusion (R := R) i ≫ projectiveSpaceStructure R d =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R i))) := by
  rw [coordinateChartInclusion_eq, Category.assoc, awayι_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (homogeneousChartEquiv (R := R) i).commutes r)

/-- The actual Segre chart ring map gives a scheme map into the actual target coordinate open. -/
def chartClosedImmersion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ⟶
      (Proj.basicOpen (projectiveSpaceGrading R (dimension m n))
        (MvPolynomial.X (indexEquiv m n (i, j)))).toScheme :=
  Spec.map (CommRingCat.ofHom (chartMap (R := R) i j).toRingHom) ≫
    (coordinateChartIso (R := R) (indexEquiv m n (i, j))).inv

/-- Native closed immersion is derived from the actual surjectivity theorem. -/
instance chartClosedImmersion_isClosedImmersion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsClosedImmersion (chartClosedImmersion (R := R) i j) := by
  let := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (chartMap (R := R) i j).toRingHom) (chartMap_surjective i j)
  unfold chartClosedImmersion
  infer_instance

/-- The actual local Segre morphism into native target projective space. -/
def chartToProjective (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ⟶
      projectiveSpace R (dimension m n) :=
  Spec.map (CommRingCat.ofHom (chartMap (R := R) i j).toRingHom) ≫
    coordinateChartInclusion (indexEquiv m n (i, j))

/-- The local projective map is the actual closed immersion followed by the target open inclusion. -/
theorem chartClosedImmersion_ι (i : Fin (m + 1)) (j : Fin (n + 1)) :
    chartClosedImmersion (R := R) i j ≫
        (Proj.basicOpen (projectiveSpaceGrading R (dimension m n))
          (MvPolynomial.X (indexEquiv m n (i, j)))).ι =
      chartToProjective i j := by
  exact Category.assoc _ _ _

/-- The actual local Segre projective map has the required coefficient structure triangle. -/
theorem chartToProjective_structure (i : Fin (m + 1)) (j : Fin (n + 1)) :
    chartToProjective (R := R) i j ≫ projectiveSpaceStructure R (dimension m n) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (CoordinateRing R i ⊗[R] CoordinateRing R j))) := by
  rw [chartToProjective, Category.assoc, coordinateChartInclusion_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (chartMap (R := R) i j).commutes r)

/-- The source tensor spectrum is the actual affine fiber product of the source coordinate charts. -/
theorem chartProduct_isPullback (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          CoordinateRing R i →+* CoordinateRing R i ⊗[R] CoordinateRing R j)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          CoordinateRing R j →+* CoordinateRing R i ⊗[R] CoordinateRing R j)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R i))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (CoordinateRing R i) (CoordinateRing R j))

end DeJongAlterations.Geometry.Segre
