import Hironaka.Geometry.ProjectiveRationalPointCoordinatesEquations
import Hironaka.Geometry.ProjectiveSpaceBaseChange

/-!
# The SAME actual original rational scheme point internally produces its whole scalar point
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveRationalPointCoordinates

open ProjectiveIdeal ProjectiveSpaceBaseChange BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The actual original entire chart map is exactly the evaluation of its SAME internally recovered original chart coordinates. -/
theorem chartAlgebraPoint_eq_aeval_pointVector :
    chartAlgebraPoint k n p hp = MvPolynomial.aeval
      (fun i : ChartIndex (chosenChart k n p) => pointVector k n p hp i.1) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [aeval_X, pointVector, coordinateDehomCoord_ne]

/-- The actual entire new-field chart point uses the SAME original internally recovered coordinates with their actual coefficients mapped. -/
def scalarPointChartAlgebra : CoordinateRing L (chosenChart k n p) →ₐ[L] L :=
  MvPolynomial.aeval (fun i : ChartIndex (chosenChart k n p) => φ (pointVector k n p hp i.1))

/-- The SAME actual original rational point internally supplies its actual rational scalar point, retaining the SAME original chosen chart. -/
def scalarPoint : Spec (CommRingCat.of L) ⟶ projectiveSpace L (n + 1) :=
  Spec.map (CommRingCat.ofHom (scalarPointChartAlgebra k L φ n p hp).toRingHom) ≫
    Segre.coordinateChartInclusion (R := L) (chosenChart k n p)

/-- The entire actual scalar point preserves the literal new-field coefficient structure. -/
theorem scalarPoint_structure : scalarPoint k L φ n p hp ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _ := by
  have h : CommRingCat.ofHom (algebraMap L (CoordinateRing L (chosenChart k n p))) ≫
      CommRingCat.ofHom (scalarPointChartAlgebra k L φ n p hp).toRingHom = 𝟙 (CommRingCat.of L) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (scalarPointChartAlgebra k L φ n p hp).commutes c
  rw [scalarPoint, Category.assoc, Segre.coordinateChartInclusion_structure, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (algebraMap L (CoordinateRing L (chosenChart k n p))) ≫
      CommRingCat.ofHom (scalarPointChartAlgebra k L φ n p hp).toRingHom) = _
  rw [h]
  simp

/-- The actual new-field whole chart evaluation retains the literal SAME original whole chart coefficient square. -/
theorem scalarPointChartAlgebra_coefficient_square :
    (scalarPointChartAlgebra k L φ n p hp).toRingHom.comp (MvPolynomial.map φ) =
      φ.comp (chartAlgebraPoint k n p hp).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [scalarPointChartAlgebra]
  · intro i
    simp only [RingHom.comp_apply, MvPolynomial.map_X]
    change scalarPointChartAlgebra k L φ n p hp (X i) = φ (chartAlgebraPoint k n p hp (X i))
    simp only [scalarPointChartAlgebra, aeval_X, pointVector, coordinateDehomCoord_ne]

/-- The scalar point retains the literal original WHOLE point morphism triangle, rather than only its point-set image. -/
theorem scalarPoint_original :
    scalarPoint k L φ n p hp ≫ projectiveCoefficientMap φ (n + 1) =
      Spec.map (CommRingCat.ofHom φ) ≫ p := by
  have hchart : Segre.coordinateChartInclusion (R := L) (chosenChart k n p) ≫
      projectiveCoefficientMap φ (n + 1) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing k (chosenChart k n p) →+*
      CoordinateRing L (chosenChart k n p))) ≫ Segre.coordinateChartInclusion (R := k) (chosenChart k n p) := by
    simpa only [nativeCoordinateInclusion_eq_segre] using nativeCoefficientMap_coordinateChart φ (chosenChart k n p)
  have hpoint : p = Spec.map (CommRingCat.ofHom (chartAlgebraPoint k n p hp).toRingHom) ≫
      Segre.coordinateChartInclusion (R := k) (chosenChart k n p) := by
    rw [chartAlgebraPoint_spec, chartLift_fac]
  calc
    scalarPoint k L φ n p hp ≫ projectiveCoefficientMap φ (n + 1) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.map φ) ≫
          CommRingCat.ofHom (scalarPointChartAlgebra k L φ n p hp).toRingHom) ≫
          Segre.coordinateChartInclusion (R := k) (chosenChart k n p) := by
      rw [scalarPoint, Category.assoc, hchart, ← Category.assoc, ← Spec.map_comp]
    _ = Spec.map (CommRingCat.ofHom (chartAlgebraPoint k n p hp).toRingHom ≫ CommRingCat.ofHom φ) ≫
          Segre.coordinateChartInclusion (R := k) (chosenChart k n p) := by
      congr 2
      apply CommRingCat.hom_ext
      exact scalarPointChartAlgebra_coefficient_square k L φ n p hp
    _ = Spec.map (CommRingCat.ofHom φ) ≫
        (Spec.map (CommRingCat.ofHom (chartAlgebraPoint k n p hp).toRingHom) ≫
          Segre.coordinateChartInclusion (R := k) (chosenChart k n p)) := by
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom φ) ≫ p := congrArg (fun m => Spec.map (CommRingCat.ofHom φ) ≫ m) hpoint.symm

end Hironaka.Geometry.ProjectiveRationalPointCoordinates
