import Hironaka.Algebra.PluckerQuotTransitionLocalizedFree
import Mathlib.LinearAlgebra.StdBasis

/-!
# Actual target frames from SAME original localized selected-column maps

The native bijectivity is already produced by the actual principal-cover
theorem. This constructs both actual maps and original unit readbacks, with
no frame or scalar compatibility assumption.
-/

noncomputable section

open scoped Classical
open Module

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w x

variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  {E : Type w} [DecidableEq E] {I : Type x} [Finite I]
  (q : (E → A) →ₗ[A] M) (a : I ↪ E) (g : A)
  (h : Function.Bijective (LocalizedModule.map (Submonoid.powers g)
    (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A))))))

/-- BOTH actual localized target maps come from the SAME original bijective selected-column map and original native coefficient localization. -/
def originalPrincipalPivotTargetFrame :
    LocalizedModule (Submonoid.powers g) M ≃ₗ[Localization.Away g]
      (I → Localization.Away g) :=
  (LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers g)
    (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A))))) h).symm ≪≫ₗ
      originalLocalizedFinsuppCoefficientEquiv A (Submonoid.powers g) I ≪≫ₗ
        (Pi.basisFun (Localization.Away g) I).repr.symm

/-- EVERY ORIGINAL selected quotient column has its SAME actual coordinate unit value under the produced original target frame. -/
theorem originalPrincipalPivotTargetFrame_column (i : I) :
    originalPrincipalPivotTargetFrame q a g h
        (LocalizedModule.mkLinearMap (Submonoid.powers g) M
          (q (Pi.single (a i) (1 : A)))) =
      Pi.single i (1 : Localization.Away g) := by
  let S := Submonoid.powers g
  let c := Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A)))
  let p := LinearEquiv.ofBijective (LocalizedModule.map S c) h
  have hc : p (LocalizedModule.mkLinearMap S (I →₀ A) (Finsupp.single i 1)) =
      LocalizedModule.mkLinearMap S M (q (Pi.single (a i) (1 : A))) := by
    change LocalizedModule.map S c (LocalizedModule.mk (Finsupp.single i 1) 1) =
      LocalizedModule.mk (q (Pi.single (a i) (1 : A))) 1
    rw [LocalizedModule.map_mk]
    simp only [c, Finsupp.linearCombination_single, one_smul]
  have hv : p.symm (LocalizedModule.mkLinearMap S M (q (Pi.single (a i) (1 : A)))) =
      LocalizedModule.mkLinearMap S (I →₀ A) (Finsupp.single i 1) :=
    (congrArg p.symm hc.symm).trans (p.symm_apply_apply _)
  change (Pi.basisFun (Localization.Away g) I).repr.symm
      (originalLocalizedFinsuppCoefficientEquiv A S I
        (p.symm (LocalizedModule.mkLinearMap S M (q (Pi.single (a i) (1 : A)))))) = _
  rw [hv, originalLocalizedFinsuppCoefficientEquiv_single, Basis.repr_symm_single_one,
    Pi.basisFun_apply]

/-- The produced ACTUAL inverse target map sends every original coordinate unit back to SAME localized ORIGINAL quotient column. -/
theorem originalPrincipalPivotTargetFrame_symm_single (i : I) :
    (originalPrincipalPivotTargetFrame q a g h).symm
        (Pi.single i (1 : Localization.Away g)) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M
        (q (Pi.single (a i) (1 : A))) := by
  apply (originalPrincipalPivotTargetFrame q a g h).injective
  rw [LinearEquiv.apply_symm_apply, originalPrincipalPivotTargetFrame_column]

/-- The WHOLE SAME original localized selected-column map satisfies its actual free coefficient/produced-target frame triangle. -/
theorem originalPrincipalPivotTargetFrame_whole_triangle :
    (originalPrincipalPivotTargetFrame q a g h).toLinearMap.comp
        (LocalizedModule.map (Submonoid.powers g)
          (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A))))) =
      (Pi.basisFun (Localization.Away g) I).repr.symm.toLinearMap.comp
        (originalLocalizedFinsuppCoefficientEquiv A (Submonoid.powers g) I).toLinearMap := by
  apply LinearMap.ext
  intro w
  let p := LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers g)
    (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A))))) h
  change (Pi.basisFun (Localization.Away g) I).repr.symm
      (originalLocalizedFinsuppCoefficientEquiv A (Submonoid.powers g) I
        (p.symm (p w))) = _
  rw [p.symm_apply_apply]
  rfl

end Hironaka.Algebra.PluckerQuotTransition
