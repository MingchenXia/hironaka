import Hironaka.Geometry.ProjectiveSecantSeparablePoint
import Hironaka.Geometry.ProjectiveSecantTangentOpen

/-!
# Original geometric tangent-secant data internally produce actual finite separable centres
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open BlowupProjectiveEmbedding Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hsmall : topologicalKrullDim X < n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- The actual original homogeneous parameter form internally defining the SAME original tangent-secant centre open. -/
def tangentSecantParameterForm : MvPolynomial (Fin (n + 2)) k :=
  originalTangentLinearForm k n i s hs hsmall.le hx *
    coordinatePolynomialEquiv k n (pointVector k n (s ≫ i) hs) (pointVector_ne_zero k n (s ≫ i) hs)
      (MvPolynomial.rename Fin.succ (secantEquation k n (fixedPointInclusion k n (s ≫ i) hs i) hsmall).val.2)

/-- The actual original parameter form has its internally produced original homogeneous degree. -/
theorem tangentSecantParameterForm_isHomogeneous :
    (tangentSecantParameterForm k n i s hs hsmall hx).IsHomogeneous
      (1 + (secantEquation k n (fixedPointInclusion k n (s ≫ i) hs i) hsmall).val.1) :=
  (originalTangentLinearForm_isHomogeneous k n i s hs hsmall.le hx).mul
    (coordinatePolynomialEquiv_isHomogeneous k n _ _
      (secantEquation k n (fixedPointInclusion k n (s ≫ i) hs i) hsmall).property.2.1.rename_isHomogeneous)

/-- Original tangent nonvanishing, actual original coordinate injectivity and original secant nonvanishing make the entire computed original parameter form nonzero. -/
theorem tangentSecantParameterForm_ne_zero : tangentSecantParameterForm k n i s hs hsmall hx ≠ 0 := by
  apply mul_ne_zero (originalTangentLinearForm_ne_zero k n i s hs hsmall.le hx)
  intro h
  have hG : MvPolynomial.rename Fin.succ (secantEquation k n (fixedPointInclusion k n (s ≫ i) hs i) hsmall).val.2 ≠ 0 :=
    (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective (n + 1))).not.mpr
      (secantEquation k n (fixedPointInclusion k n (s ≫ i) hs i) hsmall).property.2.2.1
  apply hG
  apply (coordinatePolynomialEquiv k n (pointVector k n (s ≫ i) hs) (pointVector_ne_zero k n (s ≫ i) hs)).injective
  simpa only [map_zero] using h

/-- The SAME actual original tangent-secant centre open is exactly the principal open of this SAME whole original nonzero homogeneous parameter form. -/
theorem tangentSecantCenterOpen_eq_basicOpen_parameterForm :
    tangentSecantCenterOpen k n i s hs hx hsmall =
      Proj.basicOpen (ProjectiveGrading k (n + 1)) (tangentSecantParameterForm k n i s hs hsmall hx) := by
  dsimp only [tangentSecantCenterOpen, originalTangentOpen, fixedPointCenterOpen,
    fixedPointAutomorphism, secantCenterOpen, tangentSecantParameterForm]
  rw [coordinateAutomorphism_preimage_basicOpen, Proj.basicOpen_mul]

/-- Original integral projective geometry and actual original rational smooth source internally produce an actual finite separable rational centre in the SAME original nonempty general-position open, over every original coefficient field. No rational centre, coordinate vector, finite-extension or separability certificate is supplied. -/
theorem exists_finite_separable_tangentSecant_centre :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      ∃ q : Spec (CommRingCat.of L) ⟶ projectiveSpace L (n + 1),
        q ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _ ∧
        (q ≫ projectiveCoefficientMap (algebraMap k L) (n + 1)) ≫ projectiveSpaceStructure k (n + 1) =
          Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        (q ≫ projectiveCoefficientMap (algebraMap k L) (n + 1)) (⊥ : PrimeSpectrum L) ∈
          tangentSecantCenterOpen k n i s hs hx hsmall := by
  obtain ⟨L, hfin, hsep, q, hq, hcoef, hopen⟩ := exists_finite_separable_projective_point k n
    (tangentSecantParameterForm k n i s hs hsmall hx)
    (tangentSecantParameterForm_isHomogeneous k n i s hs hsmall hx)
    (tangentSecantParameterForm_ne_zero k n i s hs hsmall hx)
  exact ⟨L, hfin, hsep, q, hq, hcoef,
    (congrArg (fun U : (projectiveSpace k (n + 1)).Opens =>
      (q ≫ projectiveCoefficientMap (algebraMap k L) (n + 1)) (⊥ : PrimeSpectrum L) ∈ U)
        (tangentSecantCenterOpen_eq_basicOpen_parameterForm k n i s hs hsmall hx)).mpr hopen⟩

end Hironaka.Geometry.ProjectiveSecant
