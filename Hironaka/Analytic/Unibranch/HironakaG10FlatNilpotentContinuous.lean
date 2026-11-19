import Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentEndomorphism
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-! # Continuous nilpotent perturbations of the identity -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
open Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentEndomorphism

/-- A continuous complex-linear map represented by a parameter-linear map
whose range is contained in a nilpotent ideal acts nilpotently. Consequently,
its difference from the identity is continuously invertible. -/
theorem isInvertible_id_sub_of_parameter_nilpotent
    {A E : Type*} [CommRing A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Module A E] (I : Ideal A) (uA : Module.End A E) (u : E →L[ℂ] E)
    (hu : ∀ x, uA x = u x) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (himage : ∀ x, uA x ∈ I • (⊤ : Submodule A E)) :
    (ContinuousLinearMap.id ℂ E - u).IsInvertible := by
  obtain ⟨n,hn⟩ := endomorphism_nilpotent_of_range I uA hnil himage
  have hp (k : ℕ) (x : E) : (uA ^ k) x = (u ^ k) x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',pow_succ']
      change uA ((uA ^ k) x) = u ((u ^ k) x)
      rw [hu, ih]
  have hn' : u ^ n = 0 := by
    ext x
    rw [← hp, hn]
    rfl
  have hunit : IsUnit (1 - u) := (show IsNilpotent u from ⟨n,hn'⟩).isUnit_one_sub
  obtain ⟨v,hv⟩ := hunit
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℂ E v, ?_⟩
  ext x
  change (v : E →L[ℂ] E) x = (1 - u) x
  rw [hv]

end Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
