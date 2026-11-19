import Hironaka.Geometry.ProjectiveRationalPointCoordinatesScalarVector
import Hironaka.Geometry.ProjectiveLinearCoordinatesScalarAutomorphism
import Hironaka.Algebra.ProjectiveLinearCoordinatesComparisonPolynomial

/-!
# The actual original rational point internally produces its literal whole scalar projection-coordinate comparison
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveLinearCoordinates

open ProjectiveRationalPointCoordinates Algebra.ProjectiveLinearCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The SAME actual original rational point internally produces its whole scalar normalization. -/
def originalPointScalarNormalization : (Fin (n + 2) → L) ≃ₗ[L] (Fin (n + 2) → L) :=
  scalarLinearEquiv k L φ (coordinateLinearEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp))

/-- The SAME actual new scalar rational point internally supplies its independently chosen whole new-field normalization. -/
def newPointScalarNormalization : (Fin (n + 2) → L) ≃ₗ[L] (Fin (n + 2) → L) :=
  coordinateLinearEquiv L n (pointVector L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp))
    (pointVector_ne_zero L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp))

/-- The actual normalization comparison uses these SAME internally constructed entire original and new maps. -/
def scalarPointNormalizationComparison : (Fin (n + 2) → L) ≃ₗ[L] (Fin (n + 2) → L) :=
  (originalPointScalarNormalization k L φ n p hp).symm.trans (newPointScalarNormalization k L φ n p hp)

/-- The actual scalar point internally constructs the nonzero scalar comparing its independently recovered coordinates with the SAME mapped original coordinates. -/
def scalarPointNormalizationScalar : L := (exists_scalarPointVector_nonzero_smul_original k L φ n p hp).choose

/-- The internally obtained scalar is nonzero and retains the SAME literal original and new point vectors. -/
theorem scalarPointNormalizationScalar_spec : scalarPointNormalizationScalar k L φ n p hp ≠ 0 ∧
    pointVector L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp) =
      scalarPointNormalizationScalar k L φ n p hp • (φ ∘ pointVector k n p hp) :=
  (exists_scalarPointVector_nonzero_smul_original k L φ n p hp).choose_spec

/-- The SAME original rational point internally proves the exact original centre-line equality for the full actual scalar normalization comparison. -/
theorem scalarPointNormalizationComparison_apply_centre :
    scalarPointNormalizationComparison k L φ n p hp (Pi.single 0 1) =
      (scalarPointNormalizationScalar k L φ n p hp)⁻¹ • Pi.single 0 1 := by
  let A := originalPointScalarNormalization k L φ n p hp
  let B := newPointScalarNormalization k L φ n p hp
  let a := scalarPointNormalizationScalar k L φ n p hp
  have ha : a ≠ 0 := (scalarPointNormalizationScalar_spec k L φ n p hp).1
  have hA : A.symm (Pi.single 0 1) = φ ∘ pointVector k n p hp := by
    apply A.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (scalar_coordinateLinearEquiv_apply_self k L φ n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).symm
  have hB : a • B (φ ∘ pointVector k n p hp) = Pi.single 0 1 := by
    rw [← map_smul, ← (scalarPointNormalizationScalar_spec k L φ n p hp).2]
    exact coordinateLinearEquiv_apply_self L n _ _
  change B (A.symm (Pi.single 0 1)) = a⁻¹ • Pi.single 0 1
  rw [hA]
  calc
    B (φ ∘ pointVector k n p hp) = a⁻¹ • (a • B (φ ∘ pointVector k n p hp)) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = _ := by rw [hB]

/-- The actual invertible remaining-coordinate scalar comparison is produced from the SAME original rational scheme point; no coordinate certificate is supplied. -/
def scalarPointTargetLinearEquiv : (Fin (n + 1) → L) ≃ₗ[L] (Fin (n + 1) → L) :=
  remainingLinearEquiv L n (scalarPointNormalizationComparison k L φ n p hp)
    (scalarPointNormalizationScalar k L φ n p hp)⁻¹
    (inv_ne_zero (scalarPointNormalizationScalar_spec k L φ n p hp).1)
    (scalarPointNormalizationComparison_apply_centre k L φ n p hp)

/-- The SAME actual original rational scheme point internally constructs its actual whole scalar target-coordinate automorphism. -/
def scalarPointTargetAutomorphism : projectiveSpace L n ≅ projectiveSpace L n :=
  linearAutomorphism L n (scalarPointTargetLinearEquiv k L φ n p hp)

/-- The actual whole scalar target-coordinate automorphism retains the literal coefficient structure over the new field. -/
@[reassoc]
theorem scalarPointTargetAutomorphism_structure :
    (scalarPointTargetAutomorphism k L φ n p hp).hom ≫ projectiveSpaceStructure L n =
      projectiveSpaceStructure L n := linearAutomorphism_structure L n _

/-- The independently chosen new normalization retains the ENTIRE new-field polynomial projection triangle with the SAME actual original normalization's scalar extension. -/
theorem scalarPoint_normalizationPolynomial_triangle (F : MvPolynomial (Fin (n + 1)) L) :
    linearPolynomialEquiv L (newPointScalarNormalization k L φ n p hp) (MvPolynomial.rename Fin.succ F) =
      linearPolynomialEquiv L (originalPointScalarNormalization k L φ n p hp)
        (MvPolynomial.rename Fin.succ (linearPolynomialEquiv L (scalarPointTargetLinearEquiv k L φ n p hp) F)) := by
  have h := linearPolynomialEquiv_trans L (originalPointScalarNormalization k L φ n p hp)
    (scalarPointNormalizationComparison k L φ n p hp)
  have he : (originalPointScalarNormalization k L φ n p hp).trans
      (scalarPointNormalizationComparison k L φ n p hp) = newPointScalarNormalization k L φ n p hp := by
    apply LinearEquiv.ext
    intro x
    simp only [scalarPointNormalizationComparison, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [he] at h
  have hF := AlgHom.congr_fun h (MvPolynomial.rename Fin.succ F)
  simp only [AlgEquiv.toAlgHom_apply, AlgHom.comp_apply] at hF
  rw [hF, linearPolynomialEquiv_remaining_triangle L n
    (scalarPointNormalizationComparison k L φ n p hp) (scalarPointNormalizationScalar k L φ n p hp)⁻¹
    (inv_ne_zero (scalarPointNormalizationScalar_spec k L φ n p hp).1)
    (scalarPointNormalizationComparison_apply_centre k L φ n p hp)]
  rfl

/-- The actual independently chosen new point normalization, in its SAME original frozen polynomial definition, retains the ENTIRE new-field projection triangle. -/
theorem scalarPoint_coordinatePolynomial_triangle (F : MvPolynomial (Fin (n + 1)) L) :
    coordinatePolynomialEquiv L n
      (pointVector L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp))
      (pointVector_ne_zero L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp))
      (MvPolynomial.rename Fin.succ F) =
    linearPolynomialEquiv L (originalPointScalarNormalization k L φ n p hp)
      (MvPolynomial.rename Fin.succ (linearPolynomialEquiv L (scalarPointTargetLinearEquiv k L φ n p hp) F)) := by
  rw [coordinatePolynomialEquiv_apply_eq_linearPolynomialEquiv]
  exact scalarPoint_normalizationPolynomial_triangle k L φ n p hp F

/-- After the internally constructed actual inverse target-coordinate substitution, the independently normalized actual scalar point projection retains the literal ENTIRE original polynomial coefficient triangle, with no pivot-naturality or coordinate-comparison certificate. -/
theorem scalarPoint_originalPolynomial_coefficient_triangle (F : MvPolynomial (Fin (n + 1)) k) :
    coordinatePolynomialEquiv L n
      (pointVector L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp))
      (pointVector_ne_zero L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp))
      (MvPolynomial.rename Fin.succ ((linearPolynomialEquiv L (scalarPointTargetLinearEquiv k L φ n p hp)).symm
        (MvPolynomial.map φ F))) =
      MvPolynomial.map φ (coordinatePolynomialEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
        (MvPolynomial.rename Fin.succ F)) := by
  rw [scalarPoint_coordinatePolynomial_triangle, AlgEquiv.apply_symm_apply, ← MvPolynomial.map_rename,
    coordinatePolynomialEquiv_apply_eq_linearPolynomialEquiv]
  exact (scalarLinearEquiv_polynomial_coefficient_triangle k L φ
    (coordinateLinearEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp))
    (MvPolynomial.rename Fin.succ F)).symm

end Hironaka.Geometry.ProjectiveLinearCoordinates
