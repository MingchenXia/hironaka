import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Actual integral closure and principal coefficient localization

The identity of a common ambient ring induces the integral-closure map.
For a domain's actual fraction field, the coefficient localization embedding
is constructed by the native localization lift, without a supplied comparison.
-/

noncomputable section

namespace DeJongAlterations.Algebra.IntegralClosureLocalization

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section CommonAmbient

variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- Restricting the actual ambient identity gives the native integral-closure map. -/
def closureMap : integralClosure R A →+* integralClosure S A where
  toFun x := ⟨(x : A), x.property.tower_top⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The actual integral-closure algebra structure is induced by the ambient identity. -/
instance closureAlgebra : Algebra (integralClosure R A) (integralClosure S A) :=
  (closureMap (R := R) (S := S) (A := A)).toAlgebra

@[simp]
theorem closureMap_coe (x : integralClosure R A) :
    (closureMap (S := S) x : A) = (x : A) := rfl

@[simp]
theorem closureMap_algebraMap (r : R) :
    closureMap (R := R) (S := S) (A := A) (algebraMap R (integralClosure R A) r) =
      algebraMap R (integralClosure S A) r := rfl

/-- The actual original coefficient embedding is preserved by the integral-closure algebra map. -/
instance closureAlgebra_base_tower :
    IsScalarTower R (integralClosure R A) (integralClosure S A) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The two actual inclusions into the common ambient ring commute. -/
instance closureAlgebra_ambient_tower :
    IsScalarTower (integralClosure R A) (integralClosure S A) A :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The actual integral-closure map is localization whenever the compatible coefficient map is. -/
theorem closure_isLocalization (s : R) [IsLocalization.Away s S]
    (hs : IsUnit (algebraMap R A s)) :
    IsLocalization.Away (algebraMap R (integralClosure R A) s) (integralClosure S A) := by
  let : IsLocalization.Away (algebraMap R A s) A :=
    IsLocalization.away_of_isUnit_of_bijective A hs Function.bijective_id
  exact IsLocalization.Away.integralClosure (R := R) (S := A) (Rf := S) (Sf := A) s

end CommonAmbient

section FractionField

variable {R F : Type u} [CommRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- A nonzero original coefficient has unit image in the actual common fraction field. -/
theorem image_isUnit (s : R) (hs : s ≠ 0) : IsUnit (algebraMap R F s) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply hs
  apply IsFractionRing.injective R F
  simpa only [map_zero] using h

/-- The actual principal localization embeds in the original common fraction field. -/
def awayToField (s : R) (hs : s ≠ 0) : Localization.Away s →+* F :=
  IsLocalization.Away.lift s (image_isUnit (F := F) s hs)

/-- Use the actual localization lift as the localized coefficient algebra structure. -/
abbrev awayFieldAlgebra (s : R) (hs : s ≠ 0) : Algebra (Localization.Away s) F :=
  (awayToField (F := F) s hs).toAlgebra

@[simp]
theorem awayToField_algebraMap (s : R) (hs : s ≠ 0) (r : R) :
    awayToField (F := F) s hs (algebraMap R (Localization.Away s) r) =
      algebraMap R F r :=
  IsLocalization.Away.lift_eq _ _ _

/-- The canonical localized coefficient map preserves the actual original embedding. -/
theorem awayFieldAlgebra_tower (s : R) (hs : s ≠ 0) :
    letI := awayFieldAlgebra (F := F) s hs
    IsScalarTower R (Localization.Away s) F := by
  let := awayFieldAlgebra (F := F) s hs
  exact IsScalarTower.of_algebraMap_eq (fun r => (awayToField_algebraMap s hs r).symm)

/-- With the actual localized coefficient algebra, the original field remains a fraction field. -/
theorem awayFieldAlgebra_isFractionRing [IsDomain R] (s : R) (hs : s ≠ 0) :
    letI := awayFieldAlgebra (F := F) s hs
    letI := awayFieldAlgebra_tower (F := F) s hs
    IsFractionRing (Localization.Away s) F := by
  let := awayFieldAlgebra (F := F) s hs
  let := awayFieldAlgebra_tower (F := F) s hs
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers s) (Localization.Away s) F

/-- The actual localized coefficient map is an embedding into the original common field. -/
theorem awayToField_injective [IsDomain R] (s : R) (hs : s ≠ 0) :
    Function.Injective (awayToField (F := F) s hs) := by
  let := awayFieldAlgebra (F := F) s hs
  let := awayFieldAlgebra_tower (F := F) s hs
  let := awayFieldAlgebra_isFractionRing (F := F) s hs
  exact IsFractionRing.injective (Localization.Away s) F

/-- The actual normalization inside the common fraction field commutes with principal localization. -/
theorem away_integralClosure_isLocalization (s : R) (hs : s ≠ 0) :
    letI := awayFieldAlgebra (F := F) s hs
    letI := awayFieldAlgebra_tower (F := F) s hs
    IsLocalization.Away (algebraMap R (integralClosure R F) s)
      (integralClosure (Localization.Away s) F) := by
  let := awayFieldAlgebra (F := F) s hs
  let := awayFieldAlgebra_tower (F := F) s hs
  exact closure_isLocalization (S := Localization.Away s) s (image_isUnit (F := F) s hs)

end FractionField

end DeJongAlterations.Algebra.IntegralClosureLocalization
