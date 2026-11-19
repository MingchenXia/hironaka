import Hironaka.Algebra.PluckerQuotTransitionCommonPivot

/-!
# SAME original normalized quotient kernel determines the exact whole pivot transition

The unit minor and entire original target change are internally produced
from the actual original surjections and SAME entire original kernel.
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

open PluckerQuot ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A ι ν : Type u} [CommRing A] [Fintype ι] [Fintype ν]
  [DecidableEq ι] [DecidableEq ν]

/-- SAME entire original normalized quotient kernel INTERNALLY produces the unit cross-pivot minor and EXACT whole original normalized-matrix transition. -/
theorem originalCommonKernel_pivotNormalize_eq
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
    (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker) :
    pivotNormalize (splitNormalizedMatrix p C) (t ∘ Sum.inl) = splitNormalizedMatrix t D := by
  let e := originalCommonQuotientTargetEquiv
    (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin
    (originalSplitNormalizedMatrix_surjective p C) (originalSplitNormalizedMatrix_surjective t D) h
  let P := LinearMap.toMatrix' e.toLinearMap
  have he := originalCommonQuotientTargetEquiv_whole_triangle
    (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin
    (originalSplitNormalizedMatrix_surjective p C) (originalSplitNormalizedMatrix_surjective t D) h
  have hM : P * splitNormalizedMatrix p C = splitNormalizedMatrix t D := by
    have hC : LinearMap.toMatrix' (splitNormalizedMatrix p C).mulVecLin = splitNormalizedMatrix p C :=
      LinearMap.toMatrix'_toLin' (splitNormalizedMatrix p C)
    have hD : LinearMap.toMatrix' (splitNormalizedMatrix t D).mulVecLin = splitNormalizedMatrix t D :=
      LinearMap.toMatrix'_toLin' (splitNormalizedMatrix t D)
    have hh := congrArg LinearMap.toMatrix' he
    simpa only [LinearMap.toMatrix'_comp, hC, hD] using hh
  have hS : P * selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl) = 1 := by
    rw [← selectedMatrix_mul, hM, selectedMatrix_splitNormalized_pivot]
  have hu := originalCommonKernel_pivotMinor_isUnit p t C D h
  have hInv : P = (selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl))⁻¹ := by
    calc
      P = P * (selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl) *
          (selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl))⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (P * selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl)) *
          (selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl))⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = (selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl))⁻¹ := by rw [hS, Matrix.one_mul]
  change (selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl))⁻¹ * splitNormalizedMatrix p C = _
  rw [← hInv]
  exact hM

end Hironaka.Algebra.PluckerQuotTransition
