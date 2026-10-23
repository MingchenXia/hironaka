import DeJongAlterations.Algebra.ProjectiveLinearCoordinatesMatrix
import DeJongAlterations.Algebra.ProjectiveLinearCoordinatesGraded

/-!
# Original matrix linear forms preserve every actual homogeneous degree
-/

noncomputable section

open MvPolynomial

namespace DeJongAlterations.Algebra.ProjectiveLinearCoordinates

open Geometry.ProjectiveIdeal

universe u v w

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- Every exact original matrix row form has homogeneous degree one. -/
theorem matrixForm_isHomogeneous {ι : Type v} {κ : Type w} [Fintype κ] (A : Matrix ι κ k) (i : ι) :
    (matrixForm k A i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa using (MvPolynomial.isHomogeneous_C _ (A i j)).mul (MvPolynomial.isHomogeneous_X k j)

/-- The entire actual matrix substitution preserves every original homogeneous degree. -/
theorem matrixPolynomialMap_isHomogeneous
    {ι : Type v} {κ : Type w} [Fintype κ] (A : Matrix ι κ k)
    {F : MvPolynomial ι k} {d : ℕ} (hF : F.IsHomogeneous d) :
    (matrixPolynomialMap k A F).IsHomogeneous d := by
  simpa only [matrixPolynomialMap, one_mul] using hF.aeval _ (matrixForm_isHomogeneous k A)

/-- The whole polynomial automorphism of the original actual linear equivalence preserves every original homogeneous degree. -/
theorem linearPolynomialEquiv_isHomogeneous
    {ι : Type v} [Fintype ι] [DecidableEq ι] (e : (ι → k) ≃ₗ[k] (ι → k))
    {F : MvPolynomial ι k} {d : ℕ} (hF : F.IsHomogeneous d) :
    (linearPolynomialEquiv k e F).IsHomogeneous d :=
  matrixPolynomialMap_isHomogeneous k _ hF

/-- The entire actual original linear coordinate change as a genuine graded map on the SAME native projective homogeneous coordinate ring. -/
def linearGradedMap (n : ℕ) (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    ProjectiveGrading k n →+*ᵍ ProjectiveGrading k n where
  __ := (linearPolynomialEquiv k e).toRingHom
  map_mem hF := linearPolynomialEquiv_isHomogeneous k e hF

/-- The actual original entire graded inverse identity, in one order. -/
theorem linearGradedMap_comp_symm (n : ℕ) (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    (linearGradedMap k n e).comp (linearGradedMap k n e.symm) = GradedRingHom.id (ProjectiveGrading k n) := by
  apply DFunLike.ext
  intro F
  exact (linearPolynomialEquiv k e).apply_symm_apply F

/-- The actual original entire graded inverse identity, in the other order. -/
theorem linearGradedMap_symm_comp (n : ℕ) (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    (linearGradedMap k n e.symm).comp (linearGradedMap k n e) = GradedRingHom.id (ProjectiveGrading k n) := by
  apply DFunLike.ext
  intro F
  exact (linearPolynomialEquiv k e).symm_apply_apply F

/-- The SAME actual inverse polynomial map internally proves the native irrelevant containment in ALL projective dimensions, including dimension zero. -/
theorem linearGradedMap_irrelevant_le (n : ℕ)
    (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading k n) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k n)).map (linearGradedMap k n e) := by
  rw [← toIdeal_le_toIdeal_iff]
  change (HomogeneousIdeal.irrelevant (ProjectiveGrading k n)).toIdeal ≤
    Ideal.map (linearGradedMap k n e).toRingHom (HomogeneousIdeal.irrelevant (ProjectiveGrading k n)).toIdeal
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hmem : linearGradedMap k n e.symm (X i) ∈
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k n)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      ((linearGradedMap k n e.symm).map_mem (MvPolynomial.isHomogeneous_X k i))
  have h := Ideal.mem_map_of_mem (linearGradedMap k n e).toRingHom hmem
  change linearPolynomialEquiv k e ((linearPolynomialEquiv k e).symm (X i)) ∈ _ at h
  rw [AlgEquiv.apply_symm_apply] at h
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars] at h
  exact h

end DeJongAlterations.Algebra.ProjectiveLinearCoordinates
