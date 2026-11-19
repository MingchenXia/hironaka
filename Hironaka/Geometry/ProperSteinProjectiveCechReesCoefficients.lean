/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.DirectSum.Module

/-!
# Actual ideal-power decomposition of original Rees elements

Closed algebraic section adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesPowerDecomposition.lean`,
SHA256 5cbef79e7fda8c52f805710e5637a833beb1508885c7d6cacf7a8f0d1617a0a3.
Only native Mathlib imports are retained; geometric chart restriction is excluded.

The actual Rees ring decomposes into the direct sum of its actual ideal
powers by its genuine polynomial coefficients. This is the coefficient
comparison used to construct the graded Čech comparison.
-/

open scoped Polynomial DirectSum
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesCoefficients

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The genuine coefficients of an actual Rees polynomial, with their actual
ideal-power membership and finite original polynomial support. -/
def coefficients (p : reesAlgebra I) : ⨁ n : ℕ, ↥(I ^ n) :=
  DFinsupp.mk (p : R[X]).support fun n => ⟨(p : R[X]).coeff n, p.2 n⟩

/-- Every actual coefficient is retained exactly in its original degree. -/
theorem coefficients_apply (p : reesAlgebra I) (n : ℕ) :
    coefficients I p n = ⟨(p : R[X]).coeff n, p.2 n⟩ := by
  classical
  apply Subtype.ext
  dsimp only [coefficients]
  rw [DFinsupp.mk_apply]
  split_ifs with hn
  · rfl
  · exact (Polynomial.notMem_support_iff.mp hn).symm

/-- The genuine coefficient map is linear on all actual Rees sections. -/
def coefficientLinear : reesAlgebra I →ₗ[R] ⨁ n : ℕ, ↥(I ^ n) where
  toFun := coefficients I
  map_add' p q := by
    ext n
    simp only [coefficients_apply, DirectSum.add_apply]
    exact Polynomial.coeff_add (p : R[X]) (q : R[X]) n
  map_smul' r p := by
    ext n
    simp only [coefficients_apply, DirectSum.smul_apply]
    exact Polynomial.coeff_smul r (p : R[X]) n

/-- The genuine Rees coefficient map is injective on all sections. -/
theorem coefficientLinear_injective : Function.Injective (coefficientLinear I) := by
  intro p q h
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  have hn := congrArg (fun x : ⨁ n : ℕ, ↥(I ^ n) => (x n : R)) h
  change (coefficients I p n : R) = (coefficients I q n : R) at hn
  simpa only [coefficients_apply] using hn

/-- A genuine homogeneous monomial is exactly the direct-sum inclusion of
its actual original ideal-power coefficient. -/
theorem coefficients_monomial (n : ℕ) (a : ↥(I ^ n)) :
    coefficients I (⟨Polynomial.monomial n (a : R),
      reesAlgebra.monomial_mem.mpr a.2⟩ : reesAlgebra I) =
        DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n a := by
  ext j
  rw [coefficients_apply]
  change (Polynomial.monomial n (a : R)).coeff j =
    (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n a j : R)
  rw [DirectSum.lof_eq_of]
  by_cases hj : j = n
  · subst j
    rw [DirectSum.of_eq_same]
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
  · rw [DirectSum.of_eq_of_ne (β := fun n => ↥(I ^ n)) n j a hj]
    simp only [Polynomial.coeff_monomial, if_neg (Ne.symm hj)]
    rfl

/-- Every finite family of actual ideal-power coefficients is realized by
an actual Rees polynomial, without any completion or finiteness hypothesis. -/
theorem coefficientLinear_surjective : Function.Surjective (coefficientLinear I) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, (coefficientLinear I).map_zero⟩
  | of n a =>
    exact ⟨⟨Polynomial.monomial n (a : R), reesAlgebra.monomial_mem.mpr a.2⟩,
      coefficients_monomial I n a⟩
  | add x y hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, (coefficientLinear I).map_add p q⟩

/-- The actual Rees ring is linearly the direct sum of its actual ideal
powers, through genuine original polynomial coefficients. -/
def powerEquiv : reesAlgebra I ≃ₗ[R] ⨁ n : ℕ, ↥(I ^ n) :=
  LinearEquiv.ofBijective (coefficientLinear I)
    ⟨coefficientLinear_injective I, coefficientLinear_surjective I⟩

section FiniteProduct

variable (A : Type u) [CommRing A] (J : Type u) [Fintype J]
variable (M : J → ℕ → Type u) [∀ j n, AddCommGroup (M j n)] [∀ j n, Module A (M j n)]

/-- A finite product of actual degree decompositions is the direct sum of
its finite products of actual degree pieces. -/
def finitePiDirectSumEquiv :
    (∀ j : J, ⨁ n : ℕ, M j n) ≃ₗ[A] ⨁ n : ℕ, (∀ j : J, M j n) := by
  classical
  let e : (Σ j : J, ℕ) ≃ (Σ n : ℕ, J) :=
    ⟨fun p => ⟨p.2, p.1⟩, fun p => ⟨p.2, p.1⟩, fun _ => rfl, fun _ => rfl⟩
  let s : (⨁ p : (Σ j : J, ℕ), M p.1 p.2) ≃ₗ[A]
      (⨁ p : (Σ n : ℕ, J), M p.2 p.1) := DFinsupp.domLCongr e
  exact (DirectSum.linearEquivFunOnFintype A J (fun j => ⨁ n : ℕ, M j n)).symm ≪≫ₗ
    (DirectSum.sigmaLcurryEquiv (δ := fun (j : J) (n : ℕ) => M j n) A).symm ≪≫ₗ
    s ≪≫ₗ
    (DirectSum.sigmaLcurryEquiv (δ := fun (n : ℕ) (j : J) => M j n) A) ≪≫ₗ
    (DFinsupp.mapRange.linearEquiv fun n =>
      DirectSum.linearEquivFunOnFintype A J (fun j => M j n))

/-- The finite product/direct-sum comparison retains every original
coefficient at its exact original index and degree. -/
theorem finitePiDirectSumEquiv_apply (x : ∀ j : J, ⨁ n : ℕ, M j n) (n : ℕ) (j : J) :
    finitePiDirectSumEquiv A J M x n j = x j n := by
  rfl

end FiniteProduct

section ReesProduct

variable (A : Type u) [CommRing A] (J : Type u) [Fintype J]
variable (S : J → Type u) [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
variable (K : ∀ j, Ideal (S j))

/-- Every finite product of actual Rees chart rings decomposes linearly
over the original base into its finite products of actual ideal powers. -/
def finiteReesPowerEquiv :
    (∀ j : J, reesAlgebra (K j)) ≃ₗ[A]
      ⨁ n : ℕ, (∀ j : J, ↥(K j ^ n)) :=
  (LinearEquiv.piCongrRight fun j => (powerEquiv (K j)).restrictScalars A) ≪≫ₗ
    finitePiDirectSumEquiv A J (fun j n => ↥(K j ^ n))

/-- The finite Rees decomposition retains every actual original coefficient
in every actual chart and original degree. -/
theorem finiteReesPowerEquiv_apply (p : ∀ j : J, reesAlgebra (K j)) (n : ℕ) (j : J) :
    finiteReesPowerEquiv A J S K p n j = ⟨(p j : (S j)[X]).coeff n, (p j).2 n⟩ := by
  rw [finiteReesPowerEquiv, LinearEquiv.trans_apply, finitePiDirectSumEquiv_apply]
  exact coefficients_apply (K j) (p j) n

end ReesProduct

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesCoefficients
