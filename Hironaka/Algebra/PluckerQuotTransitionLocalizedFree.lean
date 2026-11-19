import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Module

/-!
# Actual ORIGINAL localized free coefficients, with both whole native maps

The actual canonical localization and exact original coefficient map are
retained; native scalar extension preserves the same underlying maps.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v

variable (A : Type u) [CommRing A] (S : Submonoid A) (I : Type v)

/-- The actual native localized original free module is the SAME original free module over its actual localized ring. -/
def originalLocalizedFinsuppCoefficientEquiv :
    LocalizedModule S (I →₀ A) ≃ₗ[Localization S] (I →₀ Localization S) :=
  (IsLocalizedModule.iso S
    (Finsupp.mapRange.linearMap (α := I) (Algebra.linearMap A (Localization S)))).extendScalarsOfIsLocalization
      S (Localization S)

/-- EVERY original vector retains its literal original scalar coefficient localization under SAME native whole-map isomorphism. -/
theorem originalLocalizedFinsuppCoefficientEquiv_mk (w : I →₀ A) :
    originalLocalizedFinsuppCoefficientEquiv A S I
        (LocalizedModule.mkLinearMap S (I →₀ A) w) =
      Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization S)) w := by
  change IsLocalizedModule.iso S
      (Finsupp.mapRange.linearMap (α := I) (Algebra.linearMap A (Localization S)))
        (LocalizedModule.mk w 1) = _
  exact IsLocalizedModule.iso_mk_one S
    (Finsupp.mapRange.linearMap (α := I) (Algebra.linearMap A (Localization S))) w

/-- EVERY original source unit coefficient maps to SAME literal localized unit coefficient. -/
theorem originalLocalizedFinsuppCoefficientEquiv_single (i : I) :
    originalLocalizedFinsuppCoefficientEquiv A S I
        (LocalizedModule.mkLinearMap S (I →₀ A) (Finsupp.single i 1)) =
      Finsupp.single i (1 : Localization S) := by
  simpa only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, map_one] using
      originalLocalizedFinsuppCoefficientEquiv_mk A S I (Finsupp.single i 1)

/-- The inverse actual native map retains the SAME original unit vector with its literal original denominator one. -/
theorem originalLocalizedFinsuppCoefficientEquiv_symm_single (i : I) :
    (originalLocalizedFinsuppCoefficientEquiv A S I).symm
        (Finsupp.single i (1 : Localization S)) =
      LocalizedModule.mkLinearMap S (I →₀ A) (Finsupp.single i 1) := by
  apply (originalLocalizedFinsuppCoefficientEquiv A S I).injective
  rw [LinearEquiv.apply_symm_apply, originalLocalizedFinsuppCoefficientEquiv_single]

end Hironaka.Algebra.PluckerQuotTransition
