import Hironaka.Algebra.PluckerQuotTransitionPivotEvaluation

/-!
# EVERY original selected minor retains its actual original coefficient evaluation
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuotTransition

open PluckerQuot ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- Every ORIGINAL polynomial selected minor evaluates to SAME original selected minor of the actual evaluated split normalized quotient. -/
theorem originalMatrixCoefficientEvaluation_minor
    (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A) (s : ι → ι ⊕ ν) :
    originalMatrixCoefficientEvaluation R C (columnMinor (pivotUniversalMatrix R p) s) =
      columnMinor (splitNormalizedMatrix p C) s := by
  let φ := (originalMatrixCoefficientEvaluation R C).toRingHom
  have hm : φ.mapMatrix (selectedMatrix (pivotUniversalMatrix R p) s) =
      selectedMatrix (splitNormalizedMatrix p C) s := by
    ext i j
    exact congrFun (congrFun (originalMatrixCoefficientEvaluation_pivotMatrix R p C) i) (s j)
  exact (φ.map_det (selectedMatrix (pivotUniversalMatrix R p) s)).trans (congrArg Matrix.det hm)

end Hironaka.Algebra.PluckerQuotTransition
