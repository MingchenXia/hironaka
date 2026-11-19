import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A parameter-linear generalized inverse makes the full cokernel a
retract of the flat target. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatGeneralizedInverse

/-- No finiteness, locality, nilpotence, or flatness of the source is needed. -/
theorem cokernel_flat_of_generalized_inverse
    {R U V : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] [Module.Flat R V]
    (f : U →ₗ[R] V) (s : V →ₗ[R] U)
    (h : ∀ x, f (s (f x)) = f x) : Module.Flat R (V ⧸ LinearMap.range f) := by
  let p : V →ₗ[R] V := LinearMap.id - f.comp s
  have hp : LinearMap.range f ≤ LinearMap.ker p := by
    rintro _ ⟨x,rfl⟩
    change f x - f (s (f x)) = 0
    rw [h, sub_self]
  let i : (V ⧸ LinearMap.range f) →ₗ[R] V := (LinearMap.range f).liftQ p hp
  have hi : (LinearMap.range f).mkQ.comp i = LinearMap.id := by
    ext v
    change (LinearMap.range f).mkQ (p v) = (LinearMap.range f).mkQ v
    change (LinearMap.range f).mkQ (v - f (s v)) = (LinearMap.range f).mkQ v
    have hf : (LinearMap.range f).mkQ (f (s v)) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr ⟨s v,rfl⟩
    rw [map_sub, hf, sub_zero]
  exact Module.Flat.of_retract i (LinearMap.range f).mkQ hi
end Hironaka.Analytic.Unibranch.HironakaG10FlatGeneralizedInverse
