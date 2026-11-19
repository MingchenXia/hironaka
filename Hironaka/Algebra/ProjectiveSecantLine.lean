import Hironaka.Geometry.ProjectiveRationalPointCoordinatesEvaluation
import Hironaka.Geometry.ProjClosedImmersion
import Mathlib.Tactic.FinCases

/-!
# The literal original line through the standard point and an original vector
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual homogeneous original line-coordinate forms. -/
def lineCoordinates (v : Fin (n + 2) → k) : Fin (n + 2) → MvPolynomial (Fin 2) k :=
  Fin.cases (X 0 + C (v 0) * X 1) (fun j => C (v j.succ) * X 1)

/-- Every original line-coordinate form has homogeneous degree one. -/
theorem lineCoordinates_isHomogeneous (v : Fin (n + 2) → k) (i : Fin (n + 2)) :
    (lineCoordinates k n v i).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hm : (C (v 0) * X 1 : MvPolynomial (Fin 2) k).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C _ (v 0)).mul (MvPolynomial.isHomogeneous_X k (1 : Fin 2))
    simpa [lineCoordinates] using (MvPolynomial.isHomogeneous_X k (0 : Fin 2)).add hm
  · simpa [lineCoordinates] using (MvPolynomial.isHomogeneous_C _ (v j.succ)).mul
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2))

/-- The literal line substitution as an actual graded homomorphism. -/
def lineGradedMap (v : Fin (n + 2) → k) : ProjectiveGrading k (n + 1) →+*ᵍ ProjectiveGrading k 1 where
  __ := (MvPolynomial.aeval (lineCoordinates k n v)).toRingHom
  map_mem {i} {F} hF := by
    change ((MvPolynomial.aeval (lineCoordinates k n v)) F).IsHomogeneous i
    simpa only [one_mul] using hF.aeval _ (lineCoordinates_isHomogeneous k n v)

@[simp]
theorem lineGradedMap_X_zero (v : Fin (n + 2) → k) :
    lineGradedMap k n v (X 0) = X 0 + C (v 0) * X 1 := by simp [lineGradedMap, lineCoordinates]

@[simp]
theorem lineGradedMap_X_succ (v : Fin (n + 2) → k) (j : Fin (n + 1)) :
    lineGradedMap k n v (X j.succ) = C (v j.succ) * X 1 := by simp [lineGradedMap, lineCoordinates]

/-- A genuine nonzero original remaining coordinate constructs an actual polynomial right inverse. -/
def linePolynomialSection (v : Fin (n + 2) → k) (j : Fin (n + 1)) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin (n + 2)) k :=
  let T := C ((v j.succ)⁻¹) * X j.succ
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then X 0 - C (v 0) * T else T)

/-- The actual line homomorphism cancels the internally constructed right inverse on the whole polynomial ring. -/
theorem lineGradedMap_comp_section (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    (lineGradedMap k n v).toRingHom.comp (linePolynomialSection k n v j).toRingHom = RingHom.id _ := by
  have hT : C ((v j.succ)⁻¹) * (C (v j.succ) * X 1 : MvPolynomial (Fin 2) k) = X 1 := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hj, map_one, one_mul]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [linePolynomialSection, lineGradedMap]
  · intro i
    fin_cases i <;> simp [linePolynomialSection, lineGradedMap, lineCoordinates, hT]

/-- The original nonzero remaining coordinate gives actual surjectivity, rather than a line-immersion certificate. -/
theorem lineGradedMap_surjective (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    Function.Surjective (lineGradedMap k n v) := by
  intro F
  exact ⟨linePolynomialSection k n v j F, RingHom.congr_fun (lineGradedMap_comp_section k n v j hj) F⟩

/-- Native Proj relevance is derived internally for the actual original line map. -/
theorem lineGradedMap_irrelevant_le (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading k 1) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k (n + 1))).map (lineGradedMap k n v) :=
  Geometry.ProjClosedImmersion.irrelevant_le_map_of_surjective _ (lineGradedMap_surjective k n v j hj)

/-- The original remaining homogeneous equation has its exact original pure line-parameter pullback. -/
theorem lineGradedMap_rename_homogeneous (v : Fin (n + 2) → k)
    {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous d) :
    lineGradedMap k n v (MvPolynomial.rename Fin.succ F) =
      C (MvPolynomial.eval (fun j => v j.succ) F) * (X (1 : Fin 2)) ^ d := by
  have hcomp : (lineGradedMap k n v).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom =
      MvPolynomial.eval₂Hom C (fun j => C (v j.succ) * X (1 : Fin 2)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lineGradedMap]
    · intro j
      simp
  have heval : MvPolynomial.eval₂Hom (C : k →+* MvPolynomial (Fin 2) k) (fun j : Fin (n + 1) => C (v j.succ)) =
      (C : k →+* MvPolynomial (Fin 2) k).comp (MvPolynomial.eval (fun j : Fin (n + 1) => v j.succ)) := by
    apply MvPolynomial.ringHom_ext <;> intro a <;> simp
  change ((lineGradedMap k n v).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom) F = _
  rw [hcomp]
  calc
    _ = MvPolynomial.eval₂Hom C (fun j => X (1 : Fin 2) * C (v j.succ)) F := by
      apply congrArg (fun g : Fin (n + 1) → MvPolynomial (Fin 2) k => MvPolynomial.eval₂Hom C g F)
      funext j
      exact mul_comm _ _
    _ = X (1 : Fin 2) ^ d * MvPolynomial.eval₂Hom C (fun j : Fin (n + 1) => C (v j.succ)) F :=
      Geometry.ProjectiveRationalPointCoordinates.homogeneous_eval₂_scaled hF _ _ _
    _ = _ := by rw [heval, RingHom.comp_apply, mul_comm]

end Hironaka.Algebra.ProjectiveSecant
