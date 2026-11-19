import Hironaka.Geometry.ProjectiveSecantPointOpen
import Hironaka.Geometry.ProjectiveSecantSupport

/-!
# Actual original secant lines retain the original fixed and centre scheme points
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (q : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hq : q ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
  (hdim : topologicalKrullDim X < n)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The original centre is transported as its actual scheme morphism. -/
def transformedCenter : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1) :=
  p ≫ (fixedPointAutomorphism k n q hq).hom

include hp in
/-- Its original coefficient triangle is retained by the actual scheme map. -/
@[reassoc]
theorem transformedCenter_structure :
    transformedCenter k n q hq p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _ := by
  rw [transformedCenter, Category.assoc, fixedPointAutomorphism_structure, hp]

variable (hc : pointImage k n p ∈ fixedPointCenterOpen k n q hq i hdim)

include hc in
/-- The actual transported centre's coordinates are produced internally and lie in the computed open. -/
theorem transformedCenter_vector_mem :
    vectorPoint k n (pointVector k n (transformedCenter k n q hq p)
      (transformedCenter_structure k n q hq p hp))
      (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp)) ∈
        secantCenterOpen k n (fixedPointInclusion k n q hq i) hdim := by
  rw [pointVector_image]
  exact hc

/-- The actual original line through the two original scheme points, with no caller-supplied vector or line certificate. -/
def fixedPointLine : projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) :=
  secantLine k n (fixedPointInclusion k n q hq i) hdim
    (pointVector k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (transformedCenter_vector_mem k n q hq i hdim p hp hc) ≫ (fixedPointAutomorphism k n q hq).inv

/-- The original line is a genuine native closed immersion. -/
instance fixedPointLine_isClosedImmersion : IsClosedImmersion (fixedPointLine k n q hq i hdim p hp hc) := by
  dsimp only [fixedPointLine]
  infer_instance

/-- The actual original line retains the original coefficient field. -/
@[reassoc]
theorem fixedPointLine_structure :
    fixedPointLine k n q hq i hdim p hp hc ≫ projectiveSpaceStructure k (n + 1) = projectiveSpaceStructure k 1 := by
  rw [fixedPointLine, Category.assoc, fixedPointAutomorphism_inv_structure, secantLine_structure]

/-- The original first native endpoint maps to the exact original fixed scheme point. -/
theorem fixedPointLine_apply_fixed :
    fixedPointLine k n q hq i hdim p hp hc (centrePoint k 0) = pointImage k n q := by
  change (fixedPointAutomorphism k n q hq).inv (secantLine _ _ _ _ _ _ _ (centrePoint k 0)) = _
  rw [secantLine_apply_standard, fixedPointAutomorphism_inv_apply]

/-- The other actual native endpoint maps to the exact original centre scheme point. -/
theorem fixedPointLine_apply_center :
    fixedPointLine k n q hq i hdim p hp hc
      (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)) = pointImage k n p := by
  change (fixedPointAutomorphism k n q hq).inv (secantLine _ _ _ _ _ _ _ _) = _
  rw [secantLine_apply_vector_end, pointVector_image]
  change ((fixedPointAutomorphism k n q hq).hom ≫ (fixedPointAutomorphism k n q hq).inv) (pointImage k n p) = _
  rw [Iso.hom_inv_id]
  rfl

/-- The actual original line retains its literal whole scheme-coordinate triangle. -/
@[reassoc]
theorem fixedPointLine_comp_coordinates :
    fixedPointLine k n q hq i hdim p hp hc ≫ (fixedPointAutomorphism k n q hq).hom =
      secantLine k n (fixedPointInclusion k n q hq i) hdim
        (pointVector k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
        (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
        (transformedCenter_vector_mem k n q hq i hdim p hp hc) := by
  rw [fixedPointLine, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original line/source intersection point on the actual native line is its original fixed-point parameter. -/
theorem fixedPointLine_intersection_eq_standard (y : projectiveSpace k 1)
    (hy : fixedPointLine k n q hq i hdim p hp hc y ∈ Set.range i) : y = centrePoint k 0 := by
  apply secantLine_intersection_eq_standard k n (fixedPointInclusion k n q hq i) hdim
    (pointVector k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (transformedCenter_vector_mem k n q hq i hdim p hp hc) y
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  change (fixedPointAutomorphism k n q hq).hom (i x) = _
  rw [hx]
  exact congrArg (fun f : projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) => f y)
    (fixedPointLine_comp_coordinates k n q hq i hdim p hp hc)

/-- The native pullback's actual second projection retains the specified original line parameter. -/
theorem fixedPointLine_pullback_snd_eq_standard
    (z : (Limits.pullback i (fixedPointLine k n q hq i hdim p hp hc) : Scheme)) :
    Limits.pullback.snd i (fixedPointLine k n q hq i hdim p hp hc) z = centrePoint k 0 := by
  apply fixedPointLine_intersection_eq_standard k n q hq i hdim p hp hc
  refine ⟨Limits.pullback.fst i (fixedPointLine k n q hq i hdim p hp hc) z, ?_⟩
  exact congrArg (fun f : Limits.pullback i (fixedPointLine k n q hq i hdim p hp hc) ⟶
    projectiveSpace k (n + 1) => f z)
      (Limits.pullback.condition (f := i) (g := fixedPointLine k n q hq i hdim p hp hc))

/-- The original pullback's actual source projection maps under the original immersion to the original fixed point. -/
theorem fixedPointLine_pullback_fst_image
    (z : (Limits.pullback i (fixedPointLine k n q hq i hdim p hp hc) : Scheme)) :
    i (Limits.pullback.fst i (fixedPointLine k n q hq i hdim p hp hc) z) = pointImage k n q := by
  have h := congrArg (fun f : Limits.pullback i (fixedPointLine k n q hq i hdim p hp hc) ⟶
    projectiveSpace k (n + 1) => f z)
      (Limits.pullback.condition (f := i) (g := fixedPointLine k n q hq i hdim p hp hc))
  change i (Limits.pullback.fst i (fixedPointLine k n q hq i hdim p hp hc) z) =
    fixedPointLine k n q hq i hdim p hp hc (Limits.pullback.snd i (fixedPointLine k n q hq i hdim p hp hc) z) at h
  rw [fixedPointLine_pullback_snd_eq_standard, fixedPointLine_apply_fixed] at h
  exact h

/-- The actual original line meets the actual original closed image at exactly the original fixed point. -/
theorem fixedPointLine_range_inter_range (hqX : pointImage k n q ∈ Set.range i) :
    Set.range (fixedPointLine k n q hq i hdim p hp hc) ∩ Set.range i = {pointImage k n q} := by
  ext z
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [fixedPointLine_intersection_eq_standard k n q hq i hdim p hp hc y hy,
      fixedPointLine_apply_fixed]
    exact Set.mem_singleton _
  · intro hz
    have hz' : z = pointImage k n q := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨centrePoint k 0, fixedPointLine_apply_fixed k n q hq i hdim p hp hc⟩, hqX⟩

end Hironaka.Geometry.ProjectiveSecant
