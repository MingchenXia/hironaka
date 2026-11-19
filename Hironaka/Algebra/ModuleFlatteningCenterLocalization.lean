import Hironaka.Algebra.ModuleFlatteningMinorsCoordinates
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Original fraction-field embeddings of the actual base local rings

The localization lift extends the original coefficient map. Its actual
scalar triangle and fraction-ring instance support the same original
generic coordinate equations at every original prime.
-/

noncomputable section

namespace Hironaka.Algebra.ModuleFlatteningCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]

/-- Original prime-complement denominators are actual nonzero original base elements. -/
theorem primeCompl_le_nonZeroDivisors : p.primeCompl ≤ nonZeroDivisors R := by
  intro x hx
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (by rintro rfl; exact hx p.zero_mem)

/-- The actual original base localization maps canonically to the original fraction field. -/
def atPrimeFractionMap : Localization.AtPrime p →+* FractionRing R :=
  IsLocalization.map (M := p.primeCompl) (S := Localization.AtPrime p)
    (T := nonZeroDivisors R) (FractionRing R) (RingHom.id R)
    (primeCompl_le_nonZeroDivisors p)

/-- The original canonical coefficient algebra from the actual local ring to the original fraction field. -/
abbrev atPrimeFractionAlgebra : Algebra (Localization.AtPrime p) (FractionRing R) :=
  (atPrimeFractionMap p).toAlgebra

/-- The actual localization lift preserves the original coefficient scalar triangle. -/
theorem atPrimeFractionScalarTower :
    letI := atPrimeFractionAlgebra p
    IsScalarTower R (Localization.AtPrime p) (FractionRing R) := by
  let := atPrimeFractionAlgebra p
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (IsLocalization.map_eq (M := p.primeCompl) (S := Localization.AtPrime p)
    (T := nonZeroDivisors R) (Q := FractionRing R) (g := RingHom.id R)
    (primeCompl_le_nonZeroDivisors p) r).symm

/-- The original fraction field is the actual fraction field of the actual original base local ring. -/
theorem atPrimeFraction_isFractionRing :
    letI := atPrimeFractionAlgebra p
    IsFractionRing (Localization.AtPrime p) (FractionRing R) := by
  let := atPrimeFractionAlgebra p
  let := atPrimeFractionScalarTower p
  exact IsFractionRing.isFractionRing_of_isLocalization p.primeCompl
    (Localization.AtPrime p) (FractionRing R) (primeCompl_le_nonZeroDivisors p)

end Hironaka.Algebra.ModuleFlatteningCenter
