import Hironaka.Geometry.QuotGrassmannPivotNativePrincipalMatrices
import Hironaka.Algebra.PluckerQuotTransitionFixedMatrix

/-!
# SAME actual native quotient produces local quotients with fixed ORIGINAL indices

The cover, actual original ambient permutation and native localized target
isomorphism are derived from the point itself. Both whole original quotient
triangles have the fixed original row and complementary-column indices.
-/

noncomputable section

open scoped Classical TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuotTransition

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (ι ν : Type u) [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- SAME actual native point INTERNALLY constructs an actual finite principal cover, original ambient pivot permutations, actual localized target isomorphisms and BOTH WHOLE normalized-quotient triangles with FIXED ORIGINAL row/complement indices. -/
theorem originalNativeGrassmannian_exists_finitePrincipalFixedNormalizedQuotients
    (N : Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι)) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃
        (p : (ι ⊕ ν) ≃ (ι ⊕ ν))
        (e : LocalizedModule (Submonoid.powers g) ((A ⊗[R] ((ι ⊕ ν) → R)) ⧸ N.toSubmodule) ≃ₗ[Localization.Away g]
          (ι → Localization.Away g)) (C : Matrix ι ν (Localization.Away g)),
        e.toLinearMap.comp
          ((originalLocalizedCoordinateQuotient
            (originalNativeGrassmannianCoordinateQuotient R A (ι ⊕ ν) (Fintype.card ι) N)
            (Submonoid.powers g)).comp
            (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g) p.symm).toLinearMap) =
          Algebra.PluckerQuot.matrixQuotient C ∧
        e.symm.toLinearMap.comp (Algebra.PluckerQuot.matrixQuotient C) =
          (originalLocalizedCoordinateQuotient
            (originalNativeGrassmannianCoordinateQuotient R A (ι ⊕ ν) (Fintype.card ι) N)
            (Submonoid.powers g)).comp
            (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g) p.symm).toLinearMap := by
  obtain ⟨s, hspan, hs⟩ := originalNativeGrassmannian_exists_finitePrincipalPivotMatrices
    R A (ι ⊕ ν) (Fintype.card ι) N
  refine ⟨s, hspan, ?_⟩
  intro g hg
  obtain ⟨I, hI, a, hcard, e, C, hwhole, _, hpivot⟩ := hs g hg
  let : Fintype I := Fintype.ofFinite I
  let : DecidableEq I := Classical.decEq I
  let p := originalFixedPivotPermutation a hcard
  let e' := e ≪≫ₗ LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g)
    (originalFixedPivotRowEquiv hcard)
  let D := originalFixedPivotCoefficientMatrix C a hcard
  have hf : e'.toLinearMap.comp
      ((originalLocalizedCoordinateQuotient
        (originalNativeGrassmannianCoordinateQuotient R A (ι ⊕ ν) (Fintype.card ι) N)
        (Submonoid.powers g)).comp
        (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g) p.symm).toLinearMap) =
      Algebra.PluckerQuot.matrixQuotient D := by
    change (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g)
      (originalFixedPivotRowEquiv hcard)).toLinearMap.comp
        ((e.toLinearMap.comp (originalLocalizedCoordinateQuotient
          (originalNativeGrassmannianCoordinateQuotient R A (ι ⊕ ν) (Fintype.card ι) N)
          (Submonoid.powers g))).comp
            (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g) p.symm).toLinearMap) = _
    rw [hwhole]
    exact originalFixedPivotMatrix_whole_quotient C a hcard hpivot
  refine ⟨p, e', D, hf, ?_⟩
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hf v
  exact (congrArg e'.symm hv.symm).trans (e'.symm_apply_apply _)

end Hironaka.Geometry.QuotGrassmann
