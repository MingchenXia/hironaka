import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Surjective maps from domains preserving Krull dimension

This supplies the dimension step for a later regular-local quotient argument.
It does not assume or assert that an arbitrary regular local ring is a domain.
-/

open scoped nonZeroDivisors

namespace DeJongAlterations.Algebra.RegularLocalSurjection

/-- A surjective map from a finite-dimensional domain cannot preserve dimension
while killing a nonzero element. No locality or Noetherianity is assumed. -/
theorem injective_of_surjective_of_ringKrullDim_le
    {C S : Type*} [CommRing C] [IsDomain C] [FiniteRingKrullDim C]
    [CommRing S] (f : C →+* S) (hf : Function.Surjective f)
    (hdim : ringKrullDim C ≤ ringKrullDim S) : Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hr : x - y ∈ C⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hne
  have hfzero : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hsucc := ringKrullDim_succ_le_of_surjective f hf hr hfzero
  have hbad : ringKrullDim C + 1 ≤ ringKrullDim C :=
    (add_le_add hdim (le_rfl : (1 : WithBot ℕ∞) ≤ 1)).trans hsucc
  have hn : ringKrullDim C = ((LTSeries.longestOf (PrimeSpectrum C)).length : ℕ) :=
    Order.krullDim_eq_length_of_finiteDimensionalOrder
  rw [hn] at hbad
  have hnat : (LTSeries.longestOf (PrimeSpectrum C)).length + 1 ≤
      (LTSeries.longestOf (PrimeSpectrum C)).length := by exact_mod_cast hbad
  omega

end DeJongAlterations.Algebra.RegularLocalSurjection
