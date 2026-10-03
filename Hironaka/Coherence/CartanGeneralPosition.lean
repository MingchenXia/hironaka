/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false

/-!
# Finitely many points of the moment curve avoid any `m` hyperplanes

Combinatorial step of the plan for Cartan's theorem on an irreducible germ (step 2): instead of Demailly's
interpolation in the coefficients `c` of the primitive element (CADG II.4.29), use finitely many coefficient vectors
`c(t_i) = (1, t_i, …, t_i^{k-1})` on the moment curve. A hyperplane `{c: ∑_l λ_l c_l = 0}` (`λ ≠ 0`) contains `c(t)`
only for the `≤ k - 1` roots `t` of `∑_l λ_l t^l`. Hence (`exists_forall_sum_mul_pow_ne_zero`): for `K > m (k - 1)`
distinct `t_i` and any `m` nonzero `λ_j`, some `c(t_i)` lies on none of the hyperplanes. In the application the `m ≤
q(q-1)` hyperplanes are those where `u_c` fails to be primitive or fails to separate the fibre over a given base
point; `m` is bounded independently of the base point.
-/

open Polynomial

namespace Hironaka.CartanGeneralPosition

/-- The polynomial `∑_l λ_l X^l` of a coefficient vector. -/
noncomputable def coeffPoly {k : ℕ} (lam : Fin k → ℂ) : ℂ[X] :=
  ∑ l : Fin k, C (lam l) * X ^ (l : ℕ)

theorem eval_coeffPoly {k : ℕ} (lam : Fin k → ℂ) (t : ℂ) :
    (coeffPoly lam).eval t = ∑ l : Fin k, lam l * t ^ (l : ℕ) := by
  simp [coeffPoly, eval_finsetSum]

theorem coeff_coeffPoly {k : ℕ} (lam : Fin k → ℂ) (l : Fin k) :
    (coeffPoly lam).coeff l = lam l := by
  classical
  simp only [coeffPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single l (fun b _ hb => if_neg fun h => hb (Fin.ext h).symm)
    (fun h => absurd (Finset.mem_univ l) h), if_pos rfl]

theorem coeffPoly_ne_zero {k : ℕ} {lam : Fin k → ℂ} (h : lam ≠ 0) : coeffPoly lam ≠ 0 := by
  intro h0
  apply h
  funext l
  rw [← coeff_coeffPoly lam l, h0, coeff_zero, Pi.zero_apply]

theorem natDegree_coeffPoly_le {k : ℕ} (lam : Fin k → ℂ) : (coeffPoly lam).natDegree ≤ k - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun l _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := l.2; omega)

/-- **General position on the moment curve.**  For `m` nonzero vectors `λ_j ∈ ℂ^k` and
`K > m (k - 1)` distinct numbers `t_i`, some `t_i` satisfies `∑_l λ_{j,l} t_i^l ≠ 0` for
every `j`. -/
theorem exists_forall_sum_mul_pow_ne_zero {k m K : ℕ} (lam : Fin m → Fin k → ℂ)
    (hlam : ∀ j, lam j ≠ 0) (t : Fin K → ℂ) (ht : Function.Injective t)
    (hK : m * (k - 1) < K) :
    ∃ i, ∀ j, ∑ l : Fin k, lam j l * t i ^ (l : ℕ) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- every index is bad for some `j`
  have hsub : (Finset.univ : Finset (Fin K)) ⊆ Finset.univ.biUnion fun j =>
      Finset.univ.filter fun i => t i ∈ (coeffPoly (lam j)).roots.toFinset := by
    intro i _
    obtain ⟨j, hj⟩ := hcon i
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    rw [Multiset.mem_toFinset, mem_roots (coeffPoly_ne_zero (hlam j)), IsRoot.def,
      eval_coeffPoly]
    exact hj
  have hcard : ∀ j, (Finset.univ.filter fun i => t i ∈ (coeffPoly (lam j)).roots.toFinset).card ≤
      k - 1 := by
    intro j
    calc (Finset.univ.filter fun i => t i ∈ (coeffPoly (lam j)).roots.toFinset).card
        ≤ (coeffPoly (lam j)).roots.toFinset.card :=
          Finset.card_le_card_of_injOn t (fun i hi => (Finset.mem_filter.1 hi).2)
            (fun a _ b _ hab => ht hab)
      _ ≤ (coeffPoly (lam j)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (coeffPoly (lam j)).natDegree := card_roots' _
      _ ≤ k - 1 := natDegree_coeffPoly_le _
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ j : Fin m, (Finset.univ.filter fun i => t i ∈
      (coeffPoly (lam j)).roots.toFinset).card ≤ m * (k - 1) := by
    calc _ ≤ ∑ _j : Fin m, (k - 1) := Finset.sum_le_sum fun j _ => hcard j
      _ = m * (k - 1) := by simp
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

end Hironaka.CartanGeneralPosition
