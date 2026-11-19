import Hironaka.Algebra.PluckerQuotTransitionOverlap

/-!
# Exact original Cramer entries for pivot normalization

This is an identity on the entire original commutative ring, with its actual
selected-column matrix and its actual original free column.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι η : Type u} [Fintype ι] [DecidableEq ι]

/-- The actual normalized matrix entry times the actual pivot determinant is its original
replacement minor, over the whole original ring. -/
theorem pivotNormalize_entry_mul_det (M : Matrix ι η R) (s : ι → η)
    (hs : IsUnit (columnMinor M s)) (i : ι) (k : η) :
    columnMinor M s * pivotNormalize M s i k =
      columnMinor M (Function.update s i k) := by
  have h := congrFun ((selectedMatrix M s).det_smul_inv_mulVec_eq_cramer
    (fun j ↦ M j k) hs) i
  rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
    updateCol_selectedMatrix] at h
  exact h

end Hironaka.Algebra.PluckerQuot
