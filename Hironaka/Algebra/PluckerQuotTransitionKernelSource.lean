import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# ENTIRE original kernel equality cancels SAME actual original source isomorphism
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w x y

/-- Test EVERY original source vector at its SAME actual inverse source image to cancel the original isomorphism in an ENTIRE original quotient-kernel equality. -/
theorem originalKernel_eq_of_comp_sourceEquiv
    {A : Type u} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {W : Type w} [AddCommGroup W] [Module A W]
    {M : Type x} [AddCommGroup M] [Module A M]
    {N : Type y} [AddCommGroup N] [Module A N]
    (e : V ≃ₗ[A] W) (q : W →ₗ[A] M) (r : W →ₗ[A] N)
    (h : (q.comp e.toLinearMap).ker = (r.comp e.toLinearMap).ker) : q.ker = r.ker := by
  ext w
  have hw := SetLike.ext_iff.mp h (e.symm w)
  simpa only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hw

end Hironaka.Algebra.PluckerQuotTransition
