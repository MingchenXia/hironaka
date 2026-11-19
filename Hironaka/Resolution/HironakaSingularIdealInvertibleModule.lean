import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Regular.Basic

/-!
# Regular generators from standard invertibility of the same ideal module

The input is Mathlib's native Module.Invertible on the literal ideal
submodule. Zero divisors in the ring are allowed. Local Picard triviality
produces a generator; faithfulness of the invertible ideal makes EVERY
actual principal generator regular, including one spread to nearby stalks.

Blueprint: `hironaka-singular-ideal-invertible-module.tex`.
-/

set_option autoImplicit false

open Set

namespace Hironaka.HironakaSingularIdealInvertibleModule

noncomputable section

/-- Any given generator of the SAME standard invertible ideal is regular.
No local-ring or domain assumption is needed for this implication. -/
theorem isRegular_of_span_eq {R : Type*} [CommRing R]
    (I : Ideal R) (hInv : Module.Invertible R I) {alpha : R}
    (hspan : I = Ideal.span {alpha}) : IsRegular alpha := by
  let := hInv
  have hleft : IsLeftRegular alpha := by
    intro b c hbc
    apply FaithfulSMul.eq_of_smul_eq_smul (α := I)
    intro x
    apply Subtype.ext
    have hx : x.val ∈ Ideal.span {alpha} := by
      rw [← hspan]
      exact x.property
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hx
    change b * x.val = c * x.val
    rw [hr]
    simpa only [← mul_assoc, mul_comm b alpha, mul_comm c alpha] using
      congrArg (fun t : R => t * r) hbc
  exact ⟨hleft, fun b c hbc => hleft (by simpa only [mul_comm] using hbc)⟩

/-- Local Picard triviality internally constructs a member generating the
WHOLE original ideal, whose regularity follows without a domain hypothesis. -/
theorem exists_regular_generator {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hInv : Module.Invertible R I) :
    ∃ alpha : R, alpha ∈ I ∧ I = Ideal.span {alpha} ∧ IsRegular alpha := by
  let := hInv
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R) (M := I)).mp inferInstance
  let a : I := e.symm 1
  let alpha : R := a.val
  have he : ∀ r : R, (e.symm r).val = r * alpha := by
    intro r
    have h := e.symm.map_smul r (1 : R)
    simpa only [Submodule.coe_smul, smul_eq_mul, mul_one, a, alpha] using
      congrArg Subtype.val h
  have hspan : I = Ideal.span {alpha} := by
    apply le_antisymm
    · intro r hr
      apply Ideal.mem_span_singleton.mpr
      refine ⟨e ⟨r, hr⟩, ?_⟩
      have h := he (e ⟨r, hr⟩)
      rw [e.symm_apply_apply] at h
      simpa only [mul_comm] using h
    · apply Ideal.span_le.mpr
      intro r hr
      rw [Set.mem_singleton_iff.mp hr]
      exact a.property
  exact ⟨alpha, a.property, hspan, isRegular_of_span_eq I hInv hspan⟩

end

end Hironaka.HironakaSingularIdealInvertibleModule
