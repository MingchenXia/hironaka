import Hironaka.Geometry.ProjectiveSecantGeneralOpen
import Hironaka.Geometry.ProjectiveSecantIntersection

/-!
# Actual native secant lines of the whole original source without integrality
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1))
  [IsClosedImmersion i] (hdim : topologicalKrullDim X < n)

/-- Native membership of the original vector point gives the exact original nonzero scalar evaluation. -/
theorem generalSecantEquation_eval_ne_zero (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    MvPolynomial.eval (fun j => v j.succ) (generalSecantEquation k n i hdim).val.2 ≠ 0 := by
  change MvPolynomial.rename Fin.succ (generalSecantEquation k n i hdim).val.2 ∉
    (vectorPoint k n v hv).asHomogeneousIdeal at hc
  rw [vectorPoint_mem_homogeneous k n v hv
    (generalSecantEquation k n i hdim).property.2.1.rename_isHomogeneous] at hc
  simpa only [MvPolynomial.eval_rename, Function.comp_def] using hc

/-- Positive homogeneity produces a genuine original nonzero remaining coordinate internally. -/
theorem exists_general_secant_coordinate (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    ∃ j : Fin (n + 1), v j.succ ≠ 0 := by
  classical
  by_contra! h
  have hscaled := homogeneous_eval₂_scaled (generalSecantEquation k n i hdim).property.2.1
    (RingHom.id k) (fun j : Fin (n + 1) => v j.succ) (0 : k)
  have hz : MvPolynomial.eval (fun j : Fin (n + 1) => v j.succ)
      (generalSecantEquation k n i hdim).val.2 = 0 := by
    change MvPolynomial.eval₂Hom (RingHom.id k) (fun j : Fin (n + 1) => v j.succ) _ = 0
    simpa only [h, zero_mul, zero_pow (generalSecantEquation k n i hdim).property.1.ne',
      RingHom.id_apply] using hscaled
  exact generalSecantEquation_eval_ne_zero k n i hdim v hv hc hz

/-- The actual original secant line uses an internally produced original nonzero coordinate. -/
def generalSecantLine (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) :=
  lineImmersion k n v (exists_general_secant_coordinate k n i hdim v hv hc).choose
    (exists_general_secant_coordinate k n i hdim v hv hc).choose_spec

/-- The literal internally produced original line is a closed immersion. -/
instance generalSecantLine_isClosedImmersion (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    IsClosedImmersion (generalSecantLine k n i hdim v hv hc) := inferInstanceAs (IsClosedImmersion (lineImmersion _ _ _ _ _))

/-- Its actual coefficient triangle is the original one. -/
@[reassoc]
theorem generalSecantLine_structure (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    generalSecantLine k n i hdim v hv hc ≫ projectiveSpaceStructure k (n + 1) = projectiveSpaceStructure k 1 :=
  lineImmersion_structure _ _ _ _ _

/-- The original standard endpoint is preserved literally. -/
theorem generalSecantLine_apply_standard (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    generalSecantLine k n i hdim v hv hc (centrePoint k 0) = centrePoint k n :=
  lineImmersion_apply_standard _ _ _ _ _

/-- The other endpoint is the actual original centre, not a replacement vector point. -/
theorem generalSecantLine_apply_vector_end (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    generalSecantLine k n i hdim v hv hc (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)) =
      vectorPoint k n v hv :=
  lineImmersion_apply_vector_end _ _ _ _ _ _

/-- The actual original centre open pulls back to exactly the original line's non-endpoint chart. -/
theorem generalSecantLine_preimage_centerOpen (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim) :
    generalSecantLine k n i hdim v hv hc ⁻¹ᵁ generalSecantCenterOpen k n i hdim =
      Proj.basicOpen (ProjectiveGrading k 1) (MvPolynomial.X (1 : Fin 2)) := by
  change Proj.basicOpen (ProjectiveGrading k 1)
    (lineGradedMap k n v (MvPolynomial.rename Fin.succ (generalSecantEquation k n i hdim).val.2)) = _
  rw [lineGradedMap_rename_homogeneous k n v (generalSecantEquation k n i hdim).property.2.1,
    Proj.basicOpen_mul, basicOpen_constant k _ (generalSecantEquation_eval_ne_zero k n i hdim v hv hc),
    top_inf_eq, Proj.basicOpen_pow _ _ _ (generalSecantEquation k n i hdim).property.1]

/-- The entire original homogeneous ideal, rather than its radical, gives the actual pure parameter power. -/
theorem generalSecantLine_equation_mem_mapped_ideal (v : Fin (n + 2) → k) :
    C (MvPolynomial.eval (fun j => v j.succ) (generalSecantEquation k n i hdim).val.2) *
      MvPolynomial.X (1 : Fin 2) ^ (generalSecantEquation k n i hdim).val.1 ∈
        (ProjectiveProjection.representativeIdeal k n i).map (lineGradedMap k n v) := by
  rw [← lineGradedMap_rename_homogeneous k n v (generalSecantEquation k n i hdim).property.2.1]
  exact Ideal.mem_map_of_mem _ (generalSecantEquation k n i hdim).property.2.2.2

/-- Every actual intersection point lies outside the original line's non-endpoint chart. -/
theorem generalSecantLine_intersection_outside_chart (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim)
    (y : projectiveSpace k 1) (hy : generalSecantLine k n i hdim v hv hc y ∈ Set.range i) :
    y ∉ Proj.basicOpen (ProjectiveGrading k 1) (MvPolynomial.X (1 : Fin 2)) := by
  intro h
  have hm : generalSecantLine k n i hdim v hv hc y ∈ generalSecantCenterOpen k n i hdim := by
    change y ∈ generalSecantLine k n i hdim v hv hc ⁻¹ᵁ generalSecantCenterOpen k n i hdim
    rw [generalSecantLine_preimage_centerOpen]
    exact h
  exact generalSecantCenterOpen_avoids_image k n i hdim _ hm hy

/-- The actual native pullback intersection retains its original two projection maps and the support bound. -/
theorem generalSecantLine_pullback_support (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim)
    (z : (Limits.pullback i (generalSecantLine k n i hdim v hv hc) : Scheme)) :
    Limits.pullback.snd i (generalSecantLine k n i hdim v hv hc) z ∉
      Proj.basicOpen (ProjectiveGrading k 1) (MvPolynomial.X (1 : Fin 2)) := by
  apply generalSecantLine_intersection_outside_chart k n i hdim v hv hc
  refine ⟨Limits.pullback.fst i (generalSecantLine k n i hdim v hv hc) z, ?_⟩
  exact congrArg (fun f : Limits.pullback i (generalSecantLine k n i hdim v hv hc) ⟶
    projectiveSpace k (n + 1) => f z) (Limits.pullback.condition (f := i) (g := generalSecantLine k n i hdim v hv hc))

end Hironaka.Geometry.ProjectiveSecant
