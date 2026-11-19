import Hironaka.Algebra.ProjectiveProjectionFiniteCentre
import Hironaka.Algebra.ProjectiveLinearCoordinates

/-!
# The actual native projective point of an original nonzero rational vector

The point is the original homogeneous evaluation prime. A nonzero
coordinate proves relevance internally.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Geometry.ProjectiveProjectionCenter

open ProjectiveIdeal Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The original vector's literal homogeneous evaluation substitution. -/
def vectorGradedMap (v : Fin (n + 2) → k) : ProjectiveGrading k (n + 1) →+*ᵍ
    MvPolynomial.homogeneousSubmodule Unit k where
  __ := (MvPolynomial.aeval (fun i => C (v i) * X ()) :
    MvPolynomial (Fin (n + 2)) k →ₐ[k] MvPolynomial Unit k).toRingHom
  map_mem {i} {F} hF := by
    have hcoord (j : Fin (n + 2)) : (C (v j) * X () : MvPolynomial Unit k).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C Unit (v j)).mul (MvPolynomial.isHomogeneous_X k ())
    change (MvPolynomial.aeval (fun i => C (v i) * X ()) F).IsHomogeneous i
    simpa only [one_mul] using hF.aeval _ hcoord

/-- Every original variable evaluates to its original vector coefficient times T. -/
@[simp]
theorem vectorGradedMap_X (v : Fin (n + 2) → k) (i : Fin (n + 2)) :
    vectorGradedMap k n v (X i) = C (v i) * X () := by
  simp [vectorGradedMap]

/-- The actual rational point determined by the original nonzero homogeneous vector. -/
def vectorPoint (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    ProjectiveSpectrum (ProjectiveGrading k (n + 1)) where
  asHomogeneousIdeal := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Unit k)).comap
    (vectorGradedMap k n v)
  isPrime := (inferInstance : (⊥ : Ideal (MvPolynomial Unit k)).IsPrime).comap
    (vectorGradedMap k n v).toRingHom
  not_irrelevant_le h := by
    have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X k (pivot k n v hv)))
    change vectorGradedMap k n v (X (pivot k n v hv)) = 0 at hX
    rw [vectorGradedMap_X] at hX
    exact (mul_ne_zero (MvPolynomial.C_ne_zero.mpr (pivot_ne_zero k n v hv))
      (MvPolynomial.X_ne_zero ())) hX

/-- Membership in the actual rational point prime is original homogeneous evaluation vanishing. -/
theorem mem_vectorPoint_iff (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (F : MvPolynomial (Fin (n + 2)) k) :
    F ∈ (vectorPoint k n v hv).asHomogeneousIdeal ↔ vectorGradedMap k n v F = 0 := Iff.rfl

end Hironaka.Geometry.ProjectiveProjectionCenter
