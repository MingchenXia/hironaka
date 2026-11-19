import Hironaka.Resolution.HironakaG10LocFrischLocus

/-! The inverse of a continuously invertible parameter-linear operator is
parameter-linear for the very same parameter action. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10InvertibleParameterLinear

/-- A continuous complex inverse agrees with the inverse of the underlying
parameter-linear equivalence. -/
theorem exists_parameterLinear_inverse
    {A E : Type*} [CommRing A] [NormedAddCommGroup E] [NormedSpace ℂ E] [Module A E]
    (C : E →L[ℂ] E) (CA : E →ₗ[A] E) (hCA : ∀ x, CA x = C x)
    (hC : C.IsInvertible) : ∃ CI : E →ₗ[A] E, ∀ x, CI x = C.inverse x := by
  have hinj : Function.Injective CA := by
    intro x y hxy
    have hxy' : C x = C y := (hCA x).symm.trans (hxy.trans (hCA y))
    have h := congrArg C.inverse hxy'
    simpa only [hC.inverse_apply_self] using h
  have hsurj : Function.Surjective CA := by
    intro y
    refine ⟨C.inverse y, ?_⟩
    rw [hCA, hC.self_apply_inverse]
  let e : E ≃ₗ[A] E := LinearEquiv.ofBijective CA ⟨hinj, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun x => ?_⟩
  apply hinj
  change CA (e.symm x) = CA (C.inverse x)
  change e (e.symm x) = _
  rw [e.apply_symm_apply, hCA, hC.self_apply_inverse]
end Hironaka.Analytic.Unibranch.HironakaG10InvertibleParameterLinear
