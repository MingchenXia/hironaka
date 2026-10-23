import DeJongAlterations.Algebra.RegularSmoothConverseParameters

/-!
# A genuine strict regular-local dimension drop internally produces a nonzero cotangent relation
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.ProjectiveSecant

/-- An actual regular-local quotient of strictly smaller original dimension has an actual original kernel element with nonzero cotangent class. -/
theorem exists_kernel_cotangent_ne_zero {P Q : Type*} [CommRing P] [CommRing Q]
    [IsRegularLocalRing P] [IsRegularLocalRing Q] (f : P →+* Q) (hf : Function.Surjective f)
    (hdim : ringKrullDim Q < ringKrullDim P) :
    ∃ x : maximalIdeal P, f x = 0 ∧ (maximalIdeal P).toCotangent x ≠ 0 := by
  let : Algebra P Q := f.toAlgebra
  obtain ⟨r, t, ht, hli, he⟩ := RegularSmoothConverseParameters.exists_kernel_parameters P Q hf
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, add_zero] at he
    exact (ne_of_lt hdim) he
  refine ⟨t ⟨0, hr⟩, ht ⟨0, hr⟩, ?_⟩
  exact hli.ne_zero ⟨0, hr⟩

end DeJongAlterations.Algebra.ProjectiveSecant
