/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.Algebra.DirectSum.Internal

/-!
# The grading of the symmetric algebra

Mathlib's `SymmetricAlgebra R M`, the free commutative `R`-algebra on an `R`-module `M`, carries no
grading. Its `n`-th graded piece `Symⁿ M` is the `n`-th power of the submodule `ι(M)`
(`SymmetricAlgebra.grading R M n`), and `SymmetricAlgebra.gradedAlgebra` makes it a graded
`R`-algebra, by the argument of Mathlib's `TensorAlgebra.gradedAlgebra`: the lift of the inclusion
of `M` in degree one into the direct sum `⨁ₙ ι(M)ⁿ`, a commutative algebra, splits the inclusion of
the direct sum. The degree-zero piece is `R` (`SymmetricAlgebra.gradingZeroEquiv`).

A ring map `φ : R → S` and a `φ`-semilinear map `f : M → N` induce the graded ring map
`SymmetricAlgebra.gradedMap φ f : Sym_R M → Sym_S N`, `ι m ↦ ι (f m)`; these are the transition
maps of the projective bundle `P(E) = Proj_X (Sym E)` of a quasi-coherent sheaf [Sta, Tag 01OB].
-/

@[expose] public section

universe u

open scoped DirectSum

namespace SymmetricAlgebra

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The graded pieces of the symmetric algebra**: `Symⁿ M = ι(M)ⁿ`, the `n`-th power of the
`R`-submodule spanned by the image of `M`. -/
def grading (n : ℕ) : Submodule R (SymmetricAlgebra R M) := LinearMap.range (ι R M) ^ n

/-- The pieces multiply as powers of one submodule do. -/
instance gradedMonoid : SetLike.GradedMonoid (grading R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (ι R M))

/-- The inclusion `M → ⨁ₙ Symⁿ M` in degree one, the auxiliary map of
`SymmetricAlgebra.gradedAlgebra`. -/
def gradedι : M →ₗ[R] ⨁ i : ℕ, grading R M i :=
  DirectSum.lof R ℕ (fun i => grading R M i) 1 ∘ₗ
    (ι R M).codRestrict _ fun m => by
      simpa only [grading, pow_one] using LinearMap.mem_range_self _ m

theorem gradedι_apply (m : M) :
    gradedι R M m = DirectSum.of (fun i : ℕ => grading R M i) 1
      ⟨ι R M m, by simpa only [grading, pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

/-- **The symmetric algebra is graded** by the powers of `ι(M)`. -/
instance gradedAlgebra : GradedAlgebra (grading R M) :=
  GradedAlgebra.ofAlgHom _ (lift (gradedι R M))
    (by
      refine algHom_ext (LinearMap.ext fun m => ?_)
      change DirectSum.coeAlgHom (grading R M) (lift (gradedι R M) (ι R M m)) = ι R M m
      rw [lift_ι_apply, gradedι_apply, DirectSum.coeAlgHom_of])
    fun i x => by
      obtain ⟨x, hx⟩ := x
      dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r =>
        rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
      | add x y i hx hy ihx ihy =>
        rw [map_add, ihx, ihy, ← map_add]
        rfl
      | mem_mul m hm i x hx ih =>
        obtain ⟨_, rfl⟩ := hm
        rw [map_mul, ih, lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
        exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end SymmetricAlgebra

namespace SymmetricAlgebra

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The constants have degree zero, and only they: `Sym⁰ M = R`. -/
theorem algebraMap_bijective_gradingZero :
    Function.Bijective (algebraMap R (grading R M 0)) := by
  refine ⟨fun r s h => algebraMap_inj (M := M) r s |>.mp (congrArg Subtype.val h), ?_⟩
  rintro ⟨x, hx⟩
  rw [grading, pow_zero, Submodule.mem_one] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

variable (R M) in
/-- **The degree-zero piece of the symmetric algebra is `R`**: `R ≃+* Sym⁰ M`, the algebra map. -/
noncomputable def gradingZeroEquiv : R ≃+* grading R M 0 :=
  RingEquiv.ofBijective (algebraMap R (grading R M 0)) algebraMap_bijective_gradingZero

variable {S : Type u} {N : Type u} [CommRing S] [AddCommGroup N] [Module S N]

/-- The `R`-algebra structure of `Sym_S N` along `φ : R → S`, under which a `φ`-semilinear map
`M → N` followed by `ι` is `R`-linear; the auxiliary structure of `SymmetricAlgebra.gradedMap`. -/
noncomputable abbrev algebraOfRingHom (φ : R →+* S) : Algebra R (SymmetricAlgebra S N) :=
  ((algebraMap S (SymmetricAlgebra S N)).comp φ).toAlgebra

/-- The `R`-linear map `M → Sym_S N`, `m ↦ ι (f m)`, for the algebra structure
`SymmetricAlgebra.algebraOfRingHom φ`. -/
noncomputable def ιₛₗ (φ : R →+* S) (f : M →ₛₗ[φ] N) :
    letI := algebraOfRingHom (N := N) φ
    M →ₗ[R] SymmetricAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  { toFun := fun m => ι S N (f m)
    map_add' := fun m m' => by rw [map_add, map_add]
    map_smul' := fun r m => by
      rw [f.map_smulₛₗ, LinearMap.map_smul, RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
      rfl }

/-- **The graded map of symmetric algebras** induced by a ring map `φ : R → S` and a
`φ`-semilinear map `f : M → N`: the ring map `Sym_R M → Sym_S N` with `ι m ↦ ι (f m)` and
`r ↦ φ r`, which sends `Symⁿ M` into `Symⁿ N`. -/
noncomputable def gradedMap (φ : R →+* S) (f : M →ₛₗ[φ] N) : grading R M →+*ᵍ grading S N where
  toRingHom :=
    letI := algebraOfRingHom (N := N) φ
    (lift (ιₛₗ φ f)).toRingHom
  map_mem {n x} hx := by
    let := algebraOfRingHom (N := N) φ
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      change lift (ιₛₗ φ f) (algebraMap R _ r) ∈ grading S N 0
      rw [AlgHom.commutes, grading, pow_zero]
      exact Submodule.algebraMap_mem _
    | add x y i hx hy ihx ihy =>
      change lift (ιₛₗ φ f) (x + y) ∈ grading S N i
      rw [map_add]
      exact add_mem ihx ihy
    | mem_mul m hm i x hx ih =>
      obtain ⟨m, rfl⟩ := hm
      change lift (ιₛₗ φ f) (ι R M m * x) ∈ grading S N (i + 1)
      rw [map_mul, lift_ι_apply, grading, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

end SymmetricAlgebra
