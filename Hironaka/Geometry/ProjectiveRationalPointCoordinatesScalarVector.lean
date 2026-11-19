import Hironaka.Geometry.ProjectiveRationalPointCoordinatesScalarLift
import Hironaka.Geometry.ProjectiveSecantProjectionChartPoint
import Hironaka.Geometry.ProjectiveLinearCoordinatesVectorPoint

/-!
# Actual scalar rational points internally retain the SAME mapped original vector
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveRationalPointCoordinates

open ProjectiveIdeal ProjectiveProjectionCenter

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The SAME original internally recovered nonzero vector remains actually nonzero under the actual field coefficient map. -/
theorem scalarPoint_original_vector_ne_zero : φ ∘ pointVector k n p hp ≠ 0 := by
  intro h
  apply pointVector_ne_zero k n p hp
  ext i
  apply φ.injective
  simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun h i

/-- The actual SAME new-field chart map reads every original whole dehomogenized polynomial as evaluation at the SAME actual mapped original vector. -/
theorem scalarPointChartAlgebra_dehom (F : MvPolynomial (Fin (n + 2)) L) :
    scalarPointChartAlgebra k L φ n p hp (coordinateDehom (chosenChart k n p) F) =
      MvPolynomial.eval (φ ∘ pointVector k n p hp) F := by
  have h : (scalarPointChartAlgebra k L φ n p hp).comp (coordinateDehom (chosenChart k n p)) =
      MvPolynomial.aeval (φ ∘ pointVector k n p hp) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = chosenChart k n p
    · subst i
      simp [coordinateDehom, pointVector_chosenChart]
    · simp [coordinateDehom, coordinateDehomCoord, hi, scalarPointChartAlgebra]
  simpa only [AlgHom.comp_apply, aeval_eq_eval] using AlgHom.congr_fun h F

/-- Every actual homogeneous equation at the SAME actual new scalar scheme point is exactly the SAME mapped original vector equation, including degree zero. -/
theorem scalarPoint_mem_homogeneous {d : ℕ} {F : MvPolynomial (Fin (n + 2)) L}
    (hF : F.IsHomogeneous d) :
    F ∈ (pointImage L n (scalarPoint k L φ n p hp)).asHomogeneousIdeal ↔
      MvPolynomial.eval (φ ∘ pointVector k n p hp) F = 0 := by
  let j := chosenChart k n p
  let q := scalarPoint k L φ n p hp
  have hX : X j ∉ (pointImage L n q).asHomogeneousIdeal := by
    change pointImage L n q ∈ Proj.basicOpen (ProjectiveGrading L (n + 1)) (X j)
    have h : pointImage L n q ∈ (Segre.coordinateChartInclusion (R := L) j).opensRange := by
      exact ⟨Spec.map (CommRingCat.ofHom (scalarPointChartAlgebra k L φ n p hp).toRingHom)
        (⊥ : PrimeSpectrum L), rfl⟩
    rw [Segre.coordinateChartInclusion_opensRange] at h
    exact h
  have ho : pointImage L n q ∈ Proj.basicOpen (ProjectiveGrading L (n + 1)) (X j * F) ↔
      MvPolynomial.eval (φ ∘ pointVector k n p hp) F ≠ 0 := by
    change Spec.map (CommRingCat.ofHom (scalarPointChartAlgebra k L φ n p hp).toRingHom)
      (⊥ : PrimeSpectrum L) ∈ Segre.coordinateChartInclusion (R := L) j ⁻¹ᵁ
      Proj.basicOpen (ProjectiveGrading L (n + 1)) (X j * F) ↔ _
    rw [ProjectiveSecant.coordinateChartInclusion_preimage_mul_equation L n j hF]
    change scalarPointChartAlgebra k L φ n p hp (coordinateDehom j F) ∉ (⊥ : Ideal L) ↔ _
    rw [scalarPointChartAlgebra_dehom]
    rfl
  have hm : F ∈ (pointImage L n q).asHomogeneousIdeal ↔
      X j * F ∈ (pointImage L n q).asHomogeneousIdeal :=
    ⟨fun h => (pointImage L n q).asHomogeneousIdeal.toIdeal.mul_mem_left _ h,
      fun h => ((pointImage L n q).isPrime.mem_or_mem h).resolve_left hX⟩
  rw [hm]
  change ¬(X j * F ∈ (pointImage L n q).asHomogeneousIdeal) ↔ _ at ho
  simpa only [not_not] using not_congr ho

/-- The SAME actual new scalar point is exactly the native point of the SAME coefficientwise mapped original internally recovered vector. -/
theorem scalarPoint_vector_image :
    vectorPoint L n (φ ∘ pointVector k n p hp) (scalarPoint_original_vector_ne_zero k L φ n p hp) =
      pointImage L n (scalarPoint k L φ n p hp) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d F hF
  exact (vectorPoint_mem_homogeneous L n _ _ hF).trans (scalarPoint_mem_homogeneous k L φ n p hp hF).symm

/-- The SAME actual original rational point internally supplies the exact nonzero proportionality between independently recovered new coordinates and the SAME actual mapped original coordinates. -/
theorem exists_scalarPointVector_nonzero_smul_original :
    ∃ a : L, a ≠ 0 ∧ pointVector L n (scalarPoint k L φ n p hp)
      (scalarPoint_structure k L φ n p hp) = a • (φ ∘ pointVector k n p hp) := by
  apply ProjectiveLinearCoordinates.exists_nonzero_smul_of_vectorPoint_eq
  exact (scalarPoint_vector_image k L φ n p hp).trans
    (pointVector_image L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp)).symm

end Hironaka.Geometry.ProjectiveRationalPointCoordinates
