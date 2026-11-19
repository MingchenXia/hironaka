import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The actual projective overlap restriction inverts the other pivot ratio

This uses the native homogeneous-localization restriction map. Both numerator
and denominator are the original homogeneous elements of the same ring.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

open HomogeneousLocalization

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {s t : A}
  (hs : s ∈ 𝒜 1) (ht : t ∈ 𝒜 1)

/-- Restriction to the actual homogeneous product open makes the original other-pivot ratio a unit. -/
theorem overlapRatio_isUnit :
    IsUnit (awayMap 𝒜 ht (rfl : s * t = s * t)
      (Away.mk 𝒜 hs 1 t (by simpa using ht))) := by
  let := (awayMap 𝒜 ht (rfl : s * t = s * t)).toAlgebra
  let := Away.isLocalization_mul hs ht (rfl : s * t = s * t) (by decide : (1 : ℕ) ≠ 0)
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Away 𝒜 (s * t)) (Away.isLocalizationElem hs ht)
  simpa only [Away.isLocalizationElem, pow_one, RingHom.algebraMap_toAlgebra] using hu

/-- The actual original homogeneous coordinate ratios obey the exact change-of-denominator
identity on the whole native product-open ring. -/
theorem overlapRatio_change_denominator {v : A} (hv : v ∈ 𝒜 1) :
    awayMap 𝒜 ht (rfl : s * t = s * t)
        (Away.mk 𝒜 hs 1 t (by simpa using ht)) *
      awayMap 𝒜 hs (mul_comm s t)
        (Away.mk 𝒜 ht 1 v (by simpa using hv)) =
    awayMap 𝒜 ht (rfl : s * t = s * t)
      (Away.mk 𝒜 hs 1 v (by simpa using hv)) := by
  apply HomogeneousLocalization.val_injective
  simp only [val_mul, awayMap_mk, Away.val_mk, pow_one, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

end Hironaka.Algebra.PluckerQuot
