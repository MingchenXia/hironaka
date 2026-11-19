import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-! Every algebraic linear map of vector spaces has a generalized inverse;
no topology, finiteness, or closed-range hypothesis is involved. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10AlgebraicReferenceInverse
noncomputable section

theorem exists_generalized_inverse
    {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (f : U →ₗ[K] V) :
    ∃ s : V →ₗ[K] U, ∀ x, f (s (f x)) = f x := by
  obtain ⟨s,hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let p : V →ₗ[K] LinearMap.range f := (LinearMap.range f).subtype.leftInverse
  refine ⟨s.comp p, fun x => ?_⟩
  have hp : p (f x) = ⟨f x, ⟨x,rfl⟩⟩ := by
    simpa [p] using (LinearMap.range f).subtype.leftInverse_apply_of_inj
      (LinearMap.range f).ker_subtype (⟨f x, ⟨x,rfl⟩⟩ : LinearMap.range f)
  change f (s (p (f x))) = f x
  rw [hp]
  exact congrArg Subtype.val (LinearMap.congr_fun hs ⟨f x, ⟨x,rfl⟩⟩)
end
end Hironaka.Analytic.Unibranch.HironakaG10AlgebraicReferenceInverse
