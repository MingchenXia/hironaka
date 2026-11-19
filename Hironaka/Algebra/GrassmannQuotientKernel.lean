import Mathlib.RingTheory.Grassmannian

/-! # Actual original quotient kernels and native Grassmannian base change

The original quotient map supplies the point. Base-change naturality is
proved for the whole actual maps, using the native first-isomorphism
equivalence, not a kernel-comparison certificate.
-/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.GrassmannQuotientKernel

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Original

variable {A : Type u} [CommRing A]
  {V : Type v} [AddCommGroup V] [Module A V]
  {M : Type w} [AddCommGroup M] [Module A M]
  [Module.Finite A M] [Module.Projective A M]

/-- The native point is the kernel of the actual ORIGINAL surjection. -/
def point (q : V →ₗ[A] M) (hq : Function.Surjective q) (r : ℕ)
    (hr : ∀ p, Module.rankAtStalk (R := A) M p = r) : Module.Grassmannian A V r :=
  let e := q.quotKerEquivOfSurjective hq
  { toSubmodule := q.ker
    finite_quotient := Module.Finite.equiv e.symm
    projective_quotient := Module.Projective.of_equiv e.symm
    rankAtStalk_eq p := (congrArg (fun f => f p) (Module.rankAtStalk_eq_of_equiv e)).trans (hr p) }

/-- The ENTIRE actual original kernel is retained. -/
theorem point_toSubmodule (q : V →ₗ[A] M) (hq : Function.Surjective q) (r : ℕ)
    (hr : ∀ p, Module.rankAtStalk (R := A) M p = r) :
    (point q hq r hr).toSubmodule = q.ker := rfl

/-- EVERY original vector has the same native quotient readback. -/
theorem point_quotient_representative (q : V →ₗ[A] M) (hq : Function.Surjective q) (r : ℕ)
    (hr : ∀ p, Module.rankAtStalk (R := A) M p = r) (v : V) :
    q.quotKerEquivOfSurjective hq ((point q hq r hr).toSubmodule.mkQ v) = q v := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk q hq v

/-- Whole actual target/map equivalence retains the SAME native Grassmannian point. -/
theorem point_eq_of_targetEquiv
    {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N]
    (q : V →ₗ[A] M) (hq : Function.Surjective q) (q' : V →ₗ[A] N)
    (hq' : Function.Surjective q') (r : ℕ)
    (hr : ∀ p, Module.rankAtStalk (R := A) M p = r)
    (hr' : ∀ p, Module.rankAtStalk (R := A) N p = r)
    (e : M ≃ₗ[A] N) (he : q' = e.toLinearMap.comp q) :
    point q hq r hr = point q' hq' r hr' := by
  apply Module.Grassmannian.ext
  change q.ker = q'.ker
  rw [he, LinearEquiv.ker_comp]

end Original

section BaseChange

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {V : Type v} [AddCommGroup V] [Module R V]
  {M : Type w} [AddCommGroup M] [Module A M]

/-- The SAME actual original quotient, with the original ambient tensor source retained. -/
def changedQuotient (q : A ⊗[R] V →ₗ[A] M) : B ⊗[R] V →ₗ[B] B ⊗[A] M :=
  q.baseChange B ∘ₗ (AlgebraTensorModule.cancelBaseChange R A B B V).symm.toLinearMap

/-- Tensor right exactness supplies surjectivity of the actual changed map. -/
theorem changedQuotient_surjective (q : A ⊗[R] V →ₗ[A] M) (hq : Function.Surjective q) :
    Function.Surjective (changedQuotient (B := B) q) :=
  (LinearMap.baseChange_surjective B hq).comp
    (AlgebraTensorModule.cancelBaseChange R A B B V).symm.surjective

/-- The WHOLE actual changed map factors through the original first-isomorphism equivalence. -/
theorem changedQuotient_factor (q : A ⊗[R] V →ₗ[A] M) (hq : Function.Surjective q) :
    changedQuotient (B := B) q =
      ((q.quotKerEquivOfSurjective hq).baseChange A B).toLinearMap.comp
        (Module.Grassmannian.baseChangeMkQ B q.ker) := by
  ext b
  simp [changedQuotient, Module.Grassmannian.baseChangeMkQ,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul]

end BaseChange

section Rank

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]

/-- The original native constant stalk rank survives the SAME actual tensor base change. -/
theorem changedRank (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := A) M p = r) :
    ∀ p, Module.rankAtStalk (R := B) (B ⊗[A] M) p = r := by
  intro p
  exact (Module.rankAtStalk_baseChange (M := M) p).trans (hr _)

end Rank

section Naturality

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {V : Type v} [AddCommGroup V] [Module R V]
  {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]

/-- The native functor maps the ORIGINAL point to the point of the SAME actual changed quotient. -/
theorem point_map (f : A →ₐ[R] B) (q : A ⊗[R] V →ₗ[A] M)
    (hq : Function.Surjective q) (r : ℕ)
    (hr : ∀ p, Module.rankAtStalk (R := A) M p = r) :
    letI : Algebra A B := f.toAlgebra
    letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.commutes x).symm)
    Module.Grassmannian.map f (point q hq r hr) =
      point (changedQuotient (B := B) q) (changedQuotient_surjective q hq) r (changedRank r hr) := by
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.commutes x).symm)
  apply Module.Grassmannian.ext
  change (Module.Grassmannian.baseChangeMkQ B q.ker).ker = (changedQuotient (B := B) q).ker
  rw [changedQuotient_factor q hq, LinearEquiv.ker_comp]

end Naturality

end Hironaka.Algebra.GrassmannQuotientKernel
