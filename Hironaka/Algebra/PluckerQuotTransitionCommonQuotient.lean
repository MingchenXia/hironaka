import Mathlib.LinearAlgebra.Isomorphisms

/-!
# SAME entire original quotient kernel constructs BOTH actual target maps
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w x

variable {A : Type u} [CommRing A]
  {V : Type v} [AddCommGroup V] [Module A V]
  {M : Type w} [AddCommGroup M] [Module A M]
  {N : Type x} [AddCommGroup N] [Module A N]
  (q : V →ₗ[A] M) (r : V →ₗ[A] N) (hq : Function.Surjective q) (hr : Function.Surjective r)
  (h : q.ker = r.ker)

/-- BOTH actual target maps of SAME original quotient kernel, constructed from actual native first-isomorphism and original-kernel quotient equivalences. -/
def originalCommonQuotientTargetEquiv : M ≃ₗ[A] N :=
  (q.quotKerEquivOfSurjective hq).symm ≪≫ₗ Submodule.quotEquivOfEq q.ker r.ker h ≪≫ₗ
    r.quotKerEquivOfSurjective hr

/-- The ENTIRE original surjections satisfy the actual produced target-isomorphism triangle. -/
theorem originalCommonQuotientTargetEquiv_whole_triangle :
    (originalCommonQuotientTargetEquiv q r hq hr h).toLinearMap.comp q = r := by
  apply LinearMap.ext
  intro v
  simp only [originalCommonQuotientTargetEquiv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The reverse WHOLE original quotient triangle uses the inverse of SAME actual derived target map. -/
theorem originalCommonQuotientTargetEquiv_whole_triangle_inv :
    (originalCommonQuotientTargetEquiv q r hq hr h).symm.toLinearMap.comp r = q := by
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun (originalCommonQuotientTargetEquiv_whole_triangle q r hq hr h) v
  exact (congrArg (originalCommonQuotientTargetEquiv q r hq hr h).symm hv.symm).trans
    ((originalCommonQuotientTargetEquiv q r hq hr h).symm_apply_apply _)

end Hironaka.Algebra.PluckerQuotTransition
