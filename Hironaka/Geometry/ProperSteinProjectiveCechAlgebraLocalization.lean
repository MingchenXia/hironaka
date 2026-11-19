import Hironaka.Geometry.ProperSteinProjectiveCechModuleLocalization
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Literal original module/algebra away comparison, with its genuine fraction triangle -/

universe u
open CategoryTheory
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]

/-- The SAME actual algebra away ring is the ORIGINAL scalar-module localization. -/
def algebraModuleAwayEquiv (f : S) :
    LocalizedModule (Submonoid.powers f) A ≃ₗ[S]
      Localization.Away (algebraMap S A f) := by
  let g := (Algebra.linearMap A (Localization.Away (algebraMap S A f))).restrictScalars S
  let : IsLocalizedModule (Submonoid.powers f) g :=
    IsLocalizedModule.restrictScalars_powers f (Algebra.linearMap A _)
  exact IsLocalizedModule.iso (Submonoid.powers f) g

/-- The actual equivalence retains EACH original numerator. -/
theorem algebraModuleAwayEquiv_mk_one (f : S) (a : A) :
    algebraModuleAwayEquiv f (LocalizedModule.mk a 1) =
      algebraMap A (Localization.Away (algebraMap S A f)) a := by
  let g := (Algebra.linearMap A (Localization.Away (algebraMap S A f))).restrictScalars S
  let : IsLocalizedModule (Submonoid.powers f) g :=
    IsLocalizedModule.restrictScalars_powers f (Algebra.linearMap A _)
  exact IsLocalizedModule.iso_mk_one _ _ _

/-- Original literal denominator powers retain their SAME actual original fraction. -/
theorem algebraModuleAwayEquiv_mk_power (f : S) (a : A) (n : ℕ) :
    algebraModuleAwayEquiv f (LocalizedModule.mk a (homogeneousPowerDenominator f n)) =
      Localization.mk a (homogeneousPowerDenominator (algebraMap S A f) n) := by
  apply ((IsLocalization.Away.algebraMap_isUnit (algebraMap S A f)).pow n).mul_right_cancel
  have hmul : (f ^ n) • LocalizedModule.mk a (homogeneousPowerDenominator f n) =
      (LocalizedModule.mk a 1 : LocalizedModule (Submonoid.powers f) A) := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel (homogeneousPowerDenominator f n) a
  have h := congrArg (algebraModuleAwayEquiv f) hmul
  rw [LinearEquiv.map_smul, algebraModuleAwayEquiv_mk_one] at h
  rw [Algebra.smul_def, map_pow,
    IsScalarTower.algebraMap_apply S A (Localization.Away (algebraMap S A f)) f] at h
  have he := IsLocalization.mk'_spec (Localization.Away (algebraMap S A f)) a
    (homogeneousPowerDenominator (algebraMap S A f) n)
  calc
    _ = algebraMap A (Localization.Away (algebraMap S A f)) a := by
      simpa only [mul_comm] using h
    _ = _ := by simpa only [Localization.mk_eq_mk', homogeneousPowerDenominator, map_pow] using he.symm

end
end Hironaka.Geometry.ProperSteinProjectiveCech
