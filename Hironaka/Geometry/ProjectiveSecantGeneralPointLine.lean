import Hironaka.Geometry.ProjectiveSecantGeneralPointOpen
import Hironaka.Geometry.ProjectiveSecantGeneralSupport
import Hironaka.Geometry.ProjectiveSecantPointLine

/-!
# Whole-source secant lines through both actual original rational scheme points
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
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (hdim : topologicalKrullDim X < n)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

variable (hc : pointImage k n p ∈ generalFixedPointCenterOpen k n q hq i hdim)

include hc in
/-- The actual transported centre's coordinates are produced internally and lie in the computed open. -/
theorem generalTransformedCenter_vector_mem :
    vectorPoint k n (pointVector k n (transformedCenter k n q hq p)
      (transformedCenter_structure k n q hq p hp))
      (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp)) ∈
        generalSecantCenterOpen k n (fixedPointInclusion k n q hq i) hdim := by
  rw [pointVector_image]
  exact hc

/-- The actual original line through the two original scheme points, with no caller-supplied vector or line certificate. -/
def generalFixedPointLine : projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) :=
  generalSecantLine k n (fixedPointInclusion k n q hq i) hdim
    (pointVector k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (generalTransformedCenter_vector_mem k n q hq i hdim p hp hc) ≫ (fixedPointAutomorphism k n q hq).inv

/-- The original line is a genuine native closed immersion. -/
instance generalFixedPointLine_isClosedImmersion : IsClosedImmersion (generalFixedPointLine k n q hq i hdim p hp hc) := by
  dsimp only [generalFixedPointLine]
  infer_instance

/-- The actual original line retains the original coefficient field. -/
@[reassoc]
theorem generalFixedPointLine_structure :
    generalFixedPointLine k n q hq i hdim p hp hc ≫ projectiveSpaceStructure k (n + 1) = projectiveSpaceStructure k 1 := by
  rw [generalFixedPointLine, Category.assoc, fixedPointAutomorphism_inv_structure, generalSecantLine_structure]

/-- The original first native endpoint maps to the exact original fixed scheme point. -/
theorem generalFixedPointLine_apply_fixed :
    generalFixedPointLine k n q hq i hdim p hp hc (centrePoint k 0) = pointImage k n q := by
  change (fixedPointAutomorphism k n q hq).inv (generalSecantLine _ _ _ _ _ _ _ (centrePoint k 0)) = _
  rw [generalSecantLine_apply_standard, fixedPointAutomorphism_inv_apply]

/-- The other actual native endpoint maps to the exact original centre scheme point. -/
theorem generalFixedPointLine_apply_center :
    generalFixedPointLine k n q hq i hdim p hp hc
      (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)) = pointImage k n p := by
  change (fixedPointAutomorphism k n q hq).inv (generalSecantLine _ _ _ _ _ _ _ _) = _
  rw [generalSecantLine_apply_vector_end, pointVector_image]
  change ((fixedPointAutomorphism k n q hq).hom ≫ (fixedPointAutomorphism k n q hq).inv) (pointImage k n p) = _
  rw [Iso.hom_inv_id]
  rfl

/-- The actual original line retains its literal whole scheme-coordinate triangle. -/
@[reassoc]
theorem generalFixedPointLine_comp_coordinates :
    generalFixedPointLine k n q hq i hdim p hp hc ≫ (fixedPointAutomorphism k n q hq).hom =
      generalSecantLine k n (fixedPointInclusion k n q hq i) hdim
        (pointVector k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
        (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
        (generalTransformedCenter_vector_mem k n q hq i hdim p hp hc) := by
  rw [generalFixedPointLine, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original line/source intersection point on the actual native line is its original fixed-point parameter. -/
theorem generalFixedPointLine_intersection_eq_standard (y : projectiveSpace k 1)
    (hy : generalFixedPointLine k n q hq i hdim p hp hc y ∈ Set.range i) : y = centrePoint k 0 := by
  apply generalSecantLine_intersection_eq_standard k n (fixedPointInclusion k n q hq i) hdim
    (pointVector k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (pointVector_ne_zero k n (transformedCenter k n q hq p) (transformedCenter_structure k n q hq p hp))
    (generalTransformedCenter_vector_mem k n q hq i hdim p hp hc) y
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  change (fixedPointAutomorphism k n q hq).hom (i x) = _
  rw [hx]
  exact congrArg (fun f : projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) => f y)
    (generalFixedPointLine_comp_coordinates k n q hq i hdim p hp hc)

/-- The native pullback's actual second projection retains the specified original line parameter. -/
theorem generalFixedPointLine_pullback_snd_eq_standard
    (z : (Limits.pullback i (generalFixedPointLine k n q hq i hdim p hp hc) : Scheme)) :
    Limits.pullback.snd i (generalFixedPointLine k n q hq i hdim p hp hc) z = centrePoint k 0 := by
  apply generalFixedPointLine_intersection_eq_standard k n q hq i hdim p hp hc
  refine ⟨Limits.pullback.fst i (generalFixedPointLine k n q hq i hdim p hp hc) z, ?_⟩
  exact congrArg (fun f : Limits.pullback i (generalFixedPointLine k n q hq i hdim p hp hc) ⟶
    projectiveSpace k (n + 1) => f z)
      (Limits.pullback.condition (f := i) (g := generalFixedPointLine k n q hq i hdim p hp hc))

/-- The original pullback's actual source projection maps under the original immersion to the original fixed point. -/
theorem generalFixedPointLine_pullback_fst_image
    (z : (Limits.pullback i (generalFixedPointLine k n q hq i hdim p hp hc) : Scheme)) :
    i (Limits.pullback.fst i (generalFixedPointLine k n q hq i hdim p hp hc) z) = pointImage k n q := by
  have h := congrArg (fun f : Limits.pullback i (generalFixedPointLine k n q hq i hdim p hp hc) ⟶
    projectiveSpace k (n + 1) => f z)
      (Limits.pullback.condition (f := i) (g := generalFixedPointLine k n q hq i hdim p hp hc))
  change i (Limits.pullback.fst i (generalFixedPointLine k n q hq i hdim p hp hc) z) =
    generalFixedPointLine k n q hq i hdim p hp hc (Limits.pullback.snd i (generalFixedPointLine k n q hq i hdim p hp hc) z) at h
  rw [generalFixedPointLine_pullback_snd_eq_standard, generalFixedPointLine_apply_fixed] at h
  exact h

/-- The actual original line meets the actual original closed image at exactly the original fixed point. -/
theorem generalFixedPointLine_range_inter_range (hqX : pointImage k n q ∈ Set.range i) :
    Set.range (generalFixedPointLine k n q hq i hdim p hp hc) ∩ Set.range i = {pointImage k n q} := by
  ext z
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [generalFixedPointLine_intersection_eq_standard k n q hq i hdim p hp hc y hy,
      generalFixedPointLine_apply_fixed]
    exact Set.mem_singleton _
  · intro hz
    have hz' : z = pointImage k n q := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨centrePoint k 0, generalFixedPointLine_apply_fixed k n q hq i hdim p hp hc⟩, hqX⟩

end Hironaka.Geometry.ProjectiveSecant
