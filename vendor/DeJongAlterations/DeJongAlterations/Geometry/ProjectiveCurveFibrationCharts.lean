import DeJongAlterations.Geometry.RationalCoordinateMap
import DeJongAlterations.Geometry.Segre
import DeJongAlterations.Geometry.ProjIntegral
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The actual affine chart used by the projective rational projection -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.ProjectiveCurveFibration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Enumeration of the actual polynomial coordinate ring of the zero-th projective chart. -/
def chartCoordinateEquiv : MvPolynomial (Fin n) R ≃ₐ[R]
    ProjectiveIdeal.CoordinateRing R (0 : Fin (n + 1)) :=
  MvPolynomial.renameEquiv R (finSuccAboveEquiv (0 : Fin (n + 1)))

/-- The genuine standard affine chart into the native polynomial projective spectrum. -/
def affineChart : Spec (.of (MvPolynomial (Fin n) R)) ⟶ projectiveSpace R n :=
  Spec.map (chartCoordinateEquiv R n).symm.toRingEquiv.toCommRingCatIso.hom ≫
    Segre.coordinateChartInclusion (0 : Fin (n + 1))

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart R n) := by
  unfold affineChart
  infer_instance

/-- The chart preserves the actual coefficient map. -/
@[reassoc]
theorem affineChart_structure :
    affineChart R n ≫ projectiveSpaceStructure R n =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))) := by
  rw [affineChart, Category.assoc, Segre.coordinateChartInclusion_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a ↦ (chartCoordinateEquiv R n).symm.commutes a)

theorem affineChart_opensRange : (affineChart R n).opensRange =
    Proj.basicOpen (projectiveSpaceGrading R n) (MvPolynomial.X (0 : Fin (n + 1))) := by
  unfold affineChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Segre.coordinateChartInclusion_opensRange]

/-- Native projective space over a domain is integral, without a supplied geometry certificate. -/
instance projectiveSpace_isIntegral [IsDomain R] : IsIntegral (projectiveSpace R n) := by
  apply ProjIntegral.isIntegral_proj
  intro h
  have hx := HomogeneousIdeal.mem_irrelevant_of_mem (projectiveSpaceGrading R n)
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1)))
  rw [h] at hx
  exact MvPolynomial.X_ne_zero (0 : Fin (n + 1)) hx

/-- The actual affine chart is dense over a domain. -/
theorem affineChart_isDominant [IsDomain R] : IsDominant (affineChart R n) := by
  let := projectiveSpace_isIntegral R n
  constructor
  apply (affineChart R n).isOpenEmbedding.isOpen_range.dense
  exact Set.range_nonempty _

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}

/-- The actual affine rational-coordinate morphism composed with the actual target chart. -/
def projectiveCoordinateMap (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    (RationalCoordinateMap.coordinateOpen r).1.toScheme ⟶ projectiveSpace k n :=
  RationalCoordinateMap.coordinateMap p r ≫ affineChart k n

@[reassoc]
theorem projectiveCoordinateMap_structure (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    projectiveCoordinateMap p r ≫ projectiveSpaceStructure k n =
      (RationalCoordinateMap.coordinateOpen r).1.ι ≫ p := by
  rw [projectiveCoordinateMap, Category.assoc, affineChart_structure,
    show Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) =
      RationalCoordinateMap.affineSpaceStructure n from rfl,
    RationalCoordinateMap.coordinateMap_structure]

theorem projectiveCoordinateMap_isDominant (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r) :
    IsDominant (projectiveCoordinateMap p r) := by
  let := RationalCoordinateMap.coordinateMap_isDominant p r hr
  let := affineChart_isDominant k n
  unfold projectiveCoordinateMap
  infer_instance

end DeJongAlterations.Geometry.ProjectiveCurveFibration
