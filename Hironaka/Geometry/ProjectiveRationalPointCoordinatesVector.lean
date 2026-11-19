import Hironaka.Geometry.ProjectiveRationalPointCoordinatesLift

/-!
# Actual normalized homogeneous vector obtained from an original rational scheme point
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveRationalPointCoordinates

open ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The entire original normalized homogeneous vector, internally read from the actual chart map. -/
def pointVector (i : Fin (n + 2)) : k :=
  chartAlgebraPoint k n p hp (coordinateDehomCoord (chosenChart k n p) i)

/-- The selected original homogeneous coordinate is exactly one. -/
@[simp]
theorem pointVector_chosenChart : pointVector k n p hp (chosenChart k n p) = 1 := by
  simp [pointVector]

/-- The internally constructed original vector is genuinely nonzero. -/
theorem pointVector_ne_zero : pointVector k n p hp ≠ 0 := by
  intro h
  have he := congrArg (fun v : Fin (n + 2) → k => v (chosenChart k n p)) h
  rw [pointVector_chosenChart] at he
  exact one_ne_zero he

/-- The entire original polynomial dehomogenization is evaluation at the internally constructed vector. -/
theorem chartAlgebraPoint_dehom (F : MvPolynomial (Fin (n + 2)) k) :
    chartAlgebraPoint k n p hp (coordinateDehom (chosenChart k n p) F) =
      MvPolynomial.eval (pointVector k n p hp) F := by
  have h : (chartAlgebraPoint k n p hp).comp (coordinateDehom (chosenChart k n p)) =
      MvPolynomial.aeval (pointVector k n p hp) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [coordinateDehom, pointVector]
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using AlgHom.congr_fun h F

/-- The same actual algebra point on the actual homogeneous degree-zero localization. -/
def homogeneousChartPoint : HomogeneousChartRing k (chosenChart k n p) →ₐ[k] k :=
  (chartAlgebraPoint k n p hp).comp (homogeneousChartDehom (chosenChart k n p))

/-- Native homogeneous chart coordinates retain the literal original scheme morphism. -/
theorem homogeneousChartPoint_spec : p =
    Spec.map (CommRingCat.ofHom (homogeneousChartPoint k n p hp).toRingHom) ≫
      Proj.awayι (ProjectiveGrading k (n + 1)) (X (chosenChart k n p))
        (MvPolynomial.isHomogeneous_X k (chosenChart k n p)) (by decide : 0 < (1 : ℕ)) := by
  calc
    p = chartLift k n p ≫ Segre.coordinateChartInclusion (R := k) (chosenChart k n p) :=
      (chartLift_fac k n p).symm
    _ = Spec.map (CommRingCat.ofHom (chartAlgebraPoint k n p hp).toRingHom) ≫
        Segre.coordinateChartInclusion (R := k) (chosenChart k n p) := by rw [chartAlgebraPoint_spec]
    _ = _ := by
      rw [Segre.coordinateChartInclusion_eq, ← Category.assoc, ← Spec.map_comp]
      rfl

/-- Every original homogeneous fraction is evaluated by the original vector, without an assumed ratio certificate. -/
theorem homogeneousChartPoint_mk (d : ℕ) (F : MvPolynomial (Fin (n + 2)) k)
    (hF : F ∈ ProjectiveGrading k (n + 1) (d • (1 : ℕ))) :
    homogeneousChartPoint k n p hp
      (Away.mk (ProjectiveGrading k (n + 1))
        (MvPolynomial.isHomogeneous_X k (chosenChart k n p)) d F hF) =
      MvPolynomial.eval (pointVector k n p hp) F := by
  change chartAlgebraPoint k n p hp (homogeneousChartDehom _ _) = _
  rw [homogeneousChartDehom_mk, chartAlgebraPoint_dehom]

end Hironaka.Geometry.ProjectiveRationalPointCoordinates
