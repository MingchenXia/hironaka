import Hironaka.Algebra.PluckerQuotTransitionLocalizedQuotient
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The WHOLE original localized quotient has its actual original coefficient matrix

The matrix comes from the SAME actual scalar quotient and actual target
isomorphism, retaining BOTH whole maps and every original column value.
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w x

variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  {E : Type w} [Fintype E] [DecidableEq E] {I : Type x}
  (q : (E → A) →ₗ[A] M) (S : Submonoid A)
  (e : LocalizedModule S M ≃ₗ[Localization S] (I → Localization S))

/-- The actual original matrix is the native matrix of SAME scalar quotient in its actual target isomorphism. -/
def originalFramedLocalizedQuotientMatrix : Matrix I E (Localization S) :=
  LinearMap.toMatrix' (e.toLinearMap.comp (originalLocalizedCoordinateQuotient q S))

/-- EVERY original matrix entry is the actual target-frame value of the localization of SAME ORIGINAL quotient column. -/
theorem originalFramedLocalizedQuotientMatrix_entry (i : I) (j : E) :
    originalFramedLocalizedQuotientMatrix q S e i j =
      e (LocalizedModule.mkLinearMap S M (q (Pi.single j (1 : A)))) i := by
  simp only [originalFramedLocalizedQuotientMatrix, LinearMap.toMatrix'_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, originalLocalizedCoordinateQuotient_single]

/-- The WHOLE SAME original scalar quotient is its entire original native matrix under the actual produced target isomorphism. -/
theorem originalFramedLocalizedQuotientMatrix_whole_triangle :
    e.toLinearMap.comp (originalLocalizedCoordinateQuotient q S) =
      (originalFramedLocalizedQuotientMatrix q S e).mulVecLin := by
  exact (Matrix.toLin'_toMatrix' (e.toLinearMap.comp (originalLocalizedCoordinateQuotient q S))).symm

/-- The reverse WHOLE original quotient triangle lands in SAME actual native localized target. -/
theorem originalFramedLocalizedQuotientMatrix_whole_triangle_inv :
    e.symm.toLinearMap.comp (originalFramedLocalizedQuotientMatrix q S e).mulVecLin =
      originalLocalizedCoordinateQuotient q S := by
  apply LinearMap.ext
  intro v
  have h := LinearMap.congr_fun (originalFramedLocalizedQuotientMatrix_whole_triangle q S e) v
  exact (congrArg e.symm h.symm).trans (e.symm_apply_apply _)

/-- SAME ORIGINAL selected quotient columns become the actual identity matrix columns, from their actual original target-frame unit readbacks. -/
theorem originalFramedLocalizedQuotientMatrix_pivot (a : I ↪ E)
    (h : ∀ j, e (LocalizedModule.mkLinearMap S M (q (Pi.single (a j) (1 : A)))) =
      Pi.single j (1 : Localization S)) (i j : I) :
    originalFramedLocalizedQuotientMatrix q S e i (a j) =
      if i = j then (1 : Localization S) else 0 := by
  rw [originalFramedLocalizedQuotientMatrix_entry, h j]
  simp only [Pi.single_apply]

end Hironaka.Algebra.PluckerQuotTransition
