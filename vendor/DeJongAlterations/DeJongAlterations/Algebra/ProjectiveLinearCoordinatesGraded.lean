import DeJongAlterations.Algebra.ProjectiveLinearCoordinatesPolynomial
import DeJongAlterations.Algebra.ProjectiveIdealPolynomialGrading
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# Exact graded coordinate changes and internally derived irrelevant-ideal bounds
-/

noncomputable section

open MvPolynomial

namespace DeJongAlterations.Algebra.ProjectiveLinearCoordinates

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- Every actual normalized coordinate form has homogeneous degree one. -/
theorem normalizeForm_isHomogeneous (w : Fin (n + 2) → k) (i : Fin (n + 2)) :
    (normalizeForm k n w i).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [normalizeForm] using (MvPolynomial.isHomogeneous_C _ ((w 0)⁻¹)).mul
      (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 2)))
  · have hmul : (C (w j.succ * (w 0)⁻¹) * X 0 : MvPolynomial (Fin (n + 2)) k).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C _ (w j.succ * (w 0)⁻¹)).mul
        (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 2)))
    simpa [normalizeForm] using (MvPolynomial.isHomogeneous_X k j.succ).sub hmul

/-- Every actual inverse coordinate form has homogeneous degree one. -/
theorem inverseNormalizeForm_isHomogeneous (w : Fin (n + 2) → k) (i : Fin (n + 2)) :
    (inverseNormalizeForm k n w i).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [inverseNormalizeForm] using (MvPolynomial.isHomogeneous_C _ (w 0)).mul
      (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 2)))
  · have hmul : (C (w j.succ) * X 0 : MvPolynomial (Fin (n + 2)) k).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C _ (w j.succ)).mul
        (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 2)))
    simpa [inverseNormalizeForm] using (MvPolynomial.isHomogeneous_X k j.succ).add hmul

/-- The full original coordinate substitution preserves all homogeneous degrees. -/
theorem coordinatePolynomialEquiv_isHomogeneous (v : Fin (n + 2) → k) (hv : v ≠ 0)
    {F : MvPolynomial (Fin (n + 2)) k} {d : ℕ} (hF : F.IsHomogeneous d) :
    (coordinatePolynomialEquiv k n v hv F).IsHomogeneous d := by
  change (MvPolynomial.rename (Equiv.swap 0 (pivot k n v hv))
    (normalizePolynomialMap k n (swapLinearEquiv k n (pivot k n v hv) v) F)).IsHomogeneous d
  apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
  simpa only [normalizePolynomialMap, one_mul] using hF.aeval _ (normalizeForm_isHomogeneous k n _)

/-- The full original inverse coordinate substitution preserves all homogeneous degrees. -/
theorem coordinatePolynomialEquiv_symm_isHomogeneous (v : Fin (n + 2) → k) (hv : v ≠ 0)
    {F : MvPolynomial (Fin (n + 2)) k} {d : ℕ} (hF : F.IsHomogeneous d) :
    ((coordinatePolynomialEquiv k n v hv).symm F).IsHomogeneous d := by
  change (inverseNormalizePolynomialMap k n (swapLinearEquiv k n (pivot k n v hv) v)
    (MvPolynomial.rename (Equiv.swap 0 (pivot k n v hv)) F)).IsHomogeneous d
  have h := hF.rename_isHomogeneous (f := Equiv.swap 0 (pivot k n v hv))
  simpa only [inverseNormalizePolynomialMap, one_mul] using h.aeval _ (inverseNormalizeForm_isHomogeneous k n _)

/-- The original coordinate change as an actual degree-preserving graded homomorphism. -/
def coordinateGradedMap (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    ProjectiveGrading k (n + 1) →+*ᵍ ProjectiveGrading k (n + 1) where
  __ := (coordinatePolynomialEquiv k n v hv).toRingHom
  map_mem hF := coordinatePolynomialEquiv_isHomogeneous k n v hv hF

/-- The original inverse coordinate change as an actual graded homomorphism. -/
def inverseCoordinateGradedMap (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    ProjectiveGrading k (n + 1) →+*ᵍ ProjectiveGrading k (n + 1) where
  __ := (coordinatePolynomialEquiv k n v hv).symm.toRingHom
  map_mem hF := coordinatePolynomialEquiv_symm_isHomogeneous k n v hv hF

/-- Both entire graded maps cancel, in one order. -/
theorem coordinateGradedMap_comp_inverse (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (coordinateGradedMap k n v hv).comp (inverseCoordinateGradedMap k n v hv) =
      GradedRingHom.id (ProjectiveGrading k (n + 1)) := by
  apply DFunLike.ext
  intro F
  exact (coordinatePolynomialEquiv k n v hv).apply_symm_apply F

/-- Both entire graded maps cancel, in the opposite order. -/
theorem inverseCoordinateGradedMap_comp_coordinate (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (inverseCoordinateGradedMap k n v hv).comp (coordinateGradedMap k n v hv) =
      GradedRingHom.id (ProjectiveGrading k (n + 1)) := by
  apply DFunLike.ext
  intro F
  exact (coordinatePolynomialEquiv k n v hv).symm_apply_apply F

/-- A genuine inverse graded homomorphism derives literal irrelevant-ideal containment. -/
theorem irrelevant_le_map_of_inverse
    (f g : ProjectiveGrading k (n + 1) →+*ᵍ ProjectiveGrading k (n + 1))
    (hfg : ∀ F, f (g F) = F) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1)) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).map f := by
  rw [← toIdeal_le_toIdeal_iff]
  change (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).toIdeal ≤
    Ideal.map f.toRingHom (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).toIdeal
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hmem : g (X i) ∈ (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (g.map_mem (MvPolynomial.isHomogeneous_X k i))
  have him := Ideal.mem_map_of_mem f.toRingHom hmem
  change f (g (X i)) ∈ Ideal.map f.toRingHom
    (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).toIdeal at him
  rw [hfg] at him
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars] at him
  change X i ∈ Ideal.map f.toRingHom (Ideal.span (Set.range (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) k)))
  exact him

/-- Actual coordinate change derives the native Proj map hypothesis internally. -/
theorem coordinateGradedMap_irrelevant_le (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1)) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).map (coordinateGradedMap k n v hv) :=
  irrelevant_le_map_of_inverse k n (coordinateGradedMap k n v hv) (inverseCoordinateGradedMap k n v hv)
    (coordinatePolynomialEquiv k n v hv).apply_symm_apply

/-- Actual inverse coordinate change derives its native Proj map hypothesis internally. -/
theorem inverseCoordinateGradedMap_irrelevant_le (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1)) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).map (inverseCoordinateGradedMap k n v hv) :=
  irrelevant_le_map_of_inverse k n (inverseCoordinateGradedMap k n v hv) (coordinateGradedMap k n v hv)
    (coordinatePolynomialEquiv k n v hv).symm_apply_apply

end DeJongAlterations.Algebra.ProjectiveLinearCoordinates
