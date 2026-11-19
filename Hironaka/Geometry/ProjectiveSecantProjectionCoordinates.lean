import Hironaka.Geometry.ProjectiveSecantTangentDifferential
import Hironaka.Algebra.ProjectiveSecantProjectionCoordinates

/-!
# The same original source point and homogeneous equation in actual projection coordinates
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (q p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hq : q ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The exact original source vector is transformed internally by the actual original centre's linear coordinate equivalence. -/
def projectionCoordinatePointVector : Fin (n + 2) → k :=
  coordinateLinearEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector k n q hq)

/-- The actual original linear equivalence retains a genuinely nonzero original point vector. -/
theorem projectionCoordinatePointVector_ne_zero : projectionCoordinatePointVector k n q p hq hp ≠ 0 := by
  intro hz
  apply pointVector_ne_zero k n q hq
  apply (coordinateLinearEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).injective
  simpa only [projectionCoordinatePointVector, map_zero] using hz

/-- Literal original homogeneous evaluation identifies the actual transformed original scheme point with this exact transformed vector point. -/
theorem coordinateAutomorphism_apply_originalPoint :
    (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom
        (pointImage k n q) =
      vectorPoint k n (projectionCoordinatePointVector k n q p hq hp)
        (projectionCoordinatePointVector_ne_zero k n q p hq hp) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d F hF
  change coordinatePolynomialEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp) F ∈
    (pointImage k n q).asHomogeneousIdeal ↔ _
  rw [pointImage_mem_homogeneous k n q hq
    (coordinatePolynomialEquiv_isHomogeneous k n _ _ hF),
    vectorPoint_mem_homogeneous k n _ _ hF,
    original_eval_coordinatePolynomialEquiv]
  rfl

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

omit q hq [IsClosedImmersion i] in
/-- The actual original outside centre forces a genuinely nonzero actual remaining projection coordinate at the same original source point. -/
theorem exists_projectionCoordinatePointVector_remaining_ne_zero
    (hout : pointImage k n p ∉ Set.range i) :
    ∃ j : Fin (n + 1), projectionCoordinatePointVector k n (s ≫ i) p hs hp j.succ ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have he : vectorPoint k n (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
      (projectionCoordinatePointVector_ne_zero k n (s ≫ i) p hs hp) = centrePoint k n := by
    apply eq_centrePoint_of_remaining_mem
    intro j
    exact (vectorPoint_mem_homogeneous k n _ _ (MvPolynomial.isHomogeneous_X k j.succ)).mpr (by simpa only [MvPolynomial.eval_X] using hn j)
  rw [← coordinateAutomorphism_apply_originalPoint] at he
  have hpcentre := coordinateAutomorphism_apply_vectorPoint k n
    (pointVector k n p hp) (pointVector_ne_zero k n p hp)
  rw [pointVector_image] at hpcentre
  have hqp : pointImage k n (s ≫ i) = pointImage k n p := by
    have hh := congrArg (fun x =>
      (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).inv x)
      (he.trans hpcentre.symm)
    change ((coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom ≫
      (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).inv)
        (pointImage k n (s ≫ i)) =
      ((coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom ≫
        (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).inv)
          (pointImage k n p) at hh
    rw [Iso.hom_inv_id] at hh
    exact hh
  apply hout
  exact ⟨s (⊥ : PrimeSpectrum k), hqp⟩

variable (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

omit q hq in
/-- The exact internally produced whole original homogeneous equation in the actual original centre's projection coordinates. -/
def projectionCoordinateTangentEquation : MvPolynomial (Fin (n + 2)) k :=
  (coordinatePolynomialEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).symm
    (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2

omit q hq in
/-- The actual inverse projection substitution retains the internally derived positive original homogeneous degree. -/
theorem projectionCoordinateTangentEquation_isHomogeneous :
    (projectionCoordinateTangentEquation k n p hp i s hs hdim hx).IsHomogeneous
      (originalHomogeneousTangentEquation k n i s hs hdim hx).val.1 :=
  coordinatePolynomialEquiv_symm_isHomogeneous k n _ _
    (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.1

omit q hq in
/-- Whole actual polynomial injectivity preserves the original nonzero relation. -/
theorem projectionCoordinateTangentEquation_ne_zero :
    projectionCoordinateTangentEquation k n p hp i s hs hdim hx ≠ 0 := by
  intro hz
  apply (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.2.1
  apply (coordinatePolynomialEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).symm.injective
  simpa only [projectionCoordinateTangentEquation, map_zero] using hz

omit q hq in
/-- The actual original whole inverse substitution vanishes at the exact transformed original source vector. -/
theorem projectionCoordinateTangentEquation_eval_zero :
    MvPolynomial.eval (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
      (projectionCoordinateTangentEquation k n p hp i s hs hdim hx) = 0 := by
  change MvPolynomial.eval (coordinateLinearEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector k n (s ≫ i) hs)) ((coordinatePolynomialEquiv k n (pointVector k n p hp)
      (pointVector_ne_zero k n p hp)).symm (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2) = 0
  rw [original_eval_inverseCoordinatePolynomialEquiv, LinearEquiv.symm_apply_apply]
  exact originalHomogeneousTangentEquation_eval_zero k n i s hs hdim hx

omit q hq in
/-- Original actual centre-open membership produces a nonzero actual discarded-coordinate derivative of the same original equation at the same actual transformed original source point. -/
theorem projectionCoordinateTangentEquation_pderiv_zero_ne_zero
    (hc : pointImage k n p ∈ originalTangentOpen k n i s hs hdim hx) :
    MvPolynomial.eval (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
      (MvPolynomial.pderiv 0 (projectionCoordinateTangentEquation k n p hp i s hs hdim hx)) ≠ 0 := by
  change MvPolynomial.eval (coordinateLinearEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector k n (s ≫ i) hs))
      (MvPolynomial.pderiv 0 ((coordinatePolynomialEquiv k n (pointVector k n p hp)
        (pointVector_ne_zero k n p hp)).symm
          (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2)) ≠ 0
  rw [original_eval_pderiv_inverseCoordinatePolynomialEquiv]
  exact originalHomogeneousTangentEquation_direction_ne_zero k n i s hs hdim hx p hp hc

end Hironaka.Geometry.ProjectiveSecant
