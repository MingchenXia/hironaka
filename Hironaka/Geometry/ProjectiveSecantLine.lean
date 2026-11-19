import Hironaka.Algebra.ProjectiveSecantLine
import Hironaka.Geometry.ProjStructureMap
import Hironaka.Geometry.ProjectiveModification

/-!
# The actual native projective secant-line closed immersion
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter
open Algebra.ProjectiveSecant Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual native projective line from original homogeneous coordinate forms. -/
def lineImmersion (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) :=
  Proj.map (lineGradedMap k n v) (lineGradedMap_irrelevant_le k n v j hj)

/-- Actual surjectivity of original polynomial coordinates proves a genuine native closed immersion. -/
instance lineImmersion_isClosedImmersion (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    IsClosedImmersion (lineImmersion k n v j hj) :=
  ProjClosedImmersion.isClosedImmersion_map _ (lineGradedMap_surjective k n v j hj) _

/-- The native line retains the literal original coefficient structure. -/
@[reassoc]
theorem lineImmersion_structure (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    lineImmersion k n v j hj ≫ projectiveSpaceStructure k (n + 1) = projectiveSpaceStructure k 1 := by
  apply ProjStructureMap.map_toSpec_base
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change lineGradedMap k n v (C a) = C a
  simp [lineGradedMap]

/-- The standard endpoint's entire original homogeneous evaluation is preserved. -/
theorem centreGradedMap_comp_line (v : Fin (n + 2) → k) :
    (centreGradedMap k 0).comp (lineGradedMap k n v) = centreGradedMap k n := by
  have h1 : centreGradedMap k 0 (X (1 : Fin 2)) = 0 :=
    centreGradedMap_X_succ k 0 (0 : Fin 1)
  have h : (centreGradedMap k 0).toRingHom.comp (lineGradedMap k n v).toRingHom =
      (centreGradedMap k n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lineGradedMap, centreGradedMap]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change centreGradedMap k 0 (lineGradedMap k n v (X 0)) = centreGradedMap k n (X 0)
        rw [lineGradedMap_X_zero, map_add, map_mul, h1, mul_zero, add_zero,
          centreGradedMap_X_zero, centreGradedMap_X_zero]
      · change centreGradedMap k 0 (lineGradedMap k n v (X j.succ)) = centreGradedMap k n (X j.succ)
        rw [lineGradedMap_X_succ, map_mul, h1, mul_zero, centreGradedMap_X_succ]
  apply DFunLike.ext
  intro F
  exact RingHom.congr_fun h F

/-- The original standard point is the literal native image of the actual line's standard endpoint. -/
theorem lineImmersion_apply_standard (v : Fin (n + 2) → k) (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    lineImmersion k n v j hj (centrePoint k 0) = centrePoint k n := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro F
  change centreGradedMap k 0 (lineGradedMap k n v F) = 0 ↔ centreGradedMap k n F = 0
  have h := DFunLike.congr_fun (centreGradedMap_comp_line k n v) F
  change centreGradedMap k 0 (lineGradedMap k n v F) = centreGradedMap k n F at h
  rw [h]

/-- The original other endpoint is represented by its literal original binary vector. -/
def lineEndVector : Fin 2 → k := fun i => if i = 0 then 0 else 1

/-- The second endpoint's original vector is genuinely nonzero. -/
theorem lineEndVector_ne_zero : lineEndVector k ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Fin 2 → k => v 1) h
  simp [lineEndVector] at h1

/-- The other endpoint's native vector substitution retains the whole original vector. -/
theorem vectorGradedMap_comp_line (v : Fin (n + 2) → k) :
    (vectorGradedMap k 0 (lineEndVector k)).comp (lineGradedMap k n v) = vectorGradedMap k n v := by
  have h : (vectorGradedMap k 0 (lineEndVector k)).toRingHom.comp (lineGradedMap k n v).toRingHom =
      (vectorGradedMap k n v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lineGradedMap, vectorGradedMap]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [lineGradedMap, lineCoordinates, vectorGradedMap, lineEndVector]
      · simp [lineGradedMap, lineCoordinates, vectorGradedMap, lineEndVector]
  apply DFunLike.ext
  intro F
  exact RingHom.congr_fun h F

/-- The other actual native line endpoint maps to the exact original vector point. -/
theorem lineImmersion_apply_vector_end (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (j : Fin (n + 1)) (hj : v j.succ ≠ 0) :
    lineImmersion k n v j hj (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)) =
      vectorPoint k n v hv := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro F
  change vectorGradedMap k 0 (lineEndVector k) (lineGradedMap k n v F) = 0 ↔ vectorGradedMap k n v F = 0
  have h := DFunLike.congr_fun (vectorGradedMap_comp_line k n v) F
  change vectorGradedMap k 0 (lineEndVector k) (lineGradedMap k n v F) = vectorGradedMap k n v F at h
  rw [h]

end Hironaka.Geometry.ProjectiveSecant
