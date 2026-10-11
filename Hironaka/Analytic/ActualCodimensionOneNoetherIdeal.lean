/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermMinimalPolynomial
import Hironaka.Coherence.OkaGermRelations


set_option autoImplicit false

/-! # Actual principality in one-coordinate Noether position

The actual base inclusion and actual Weierstrass polynomial are the
natural Noether-position hypothesis.  The generator and full ideal
identity are produced internally, not supplied as certificates.
-/

open Hironaka

noncomputable section
open Set Filter Topology Polynomial
namespace Hironaka.ActualCodimensionOneNoetherIdeal
open HolGerm GermAlgebraicParametrization GermMinimalPolynomial OkaGermRelations

/-- True one-coordinate Noether position internally produces a distinguished
polynomial generating the entire prime ideal, with a prime evaluated germ. -/
theorem exists_prime_weierstrass_generator {n : ℕ}
    (Q : Ideal (HolGerm (ComplexModel (n + 1)))) [Q.IsPrime]
    (hQ : IsNoetherNormalization Q n) :
    ∃ W : (HolGerm (ComplexModel n))[X], IsWeierstrass W ∧
      0 < W.natDegree ∧
      Q = Ideal.span ({evalGerm (n + 1) W (coord (Fin.last n))} :
        Set (HolGerm (ComplexModel (n + 1)))) ∧
      Prime (evalGerm (n + 1) W (coord (Fin.last n))) := by
  classical
  obtain ⟨W, hW, hdeg, hmem, hdiv⟩ := exists_minpoly_isWeierstrass hQ
    (coord (Fin.last n)) (by simp [coord, coordGerm, HolGerm.eval_mk])
  have hlast : evalGerm (n + 1) W (coord (Fin.last n)) =
      weierstrassGerm (n + 1) n n.lt_succ_self W.natDegree W.coeff := by
    simpa only [projGerm_self] using evalGerm_coord_last (n := n) le_rfl hW.1
  have heq : Q = Ideal.span ({evalGerm (n + 1) W (coord (Fin.last n))} :
      Set (HolGerm (ComplexModel (n + 1)))) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨q, r, hqr⟩ := exists_eq_mul_weierstrassGerm_add hW.2 g
      let R : (HolGerm (ComplexModel n))[X] :=
        ∑ j ∈ Finset.range W.natDegree, C (r j) * X ^ j
      have hev : evalGerm (n + 1) R (coord (Fin.last n)) =
          ∑ j ∈ Finset.range W.natDegree, projGerm (n + 1) n (r j) *
            coordGerm (n + 1) n n.lt_succ_self ^ j := by
        simp only [R, evalGerm, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow]
        rfl
      have hRm : evalGerm (n + 1) R (coord (Fin.last n)) ∈ Q := by
        have hz := Q.sub_mem hg (Q.mul_mem_left q hmem)
        rw [hlast, hqr, add_sub_cancel_left] at hz
        rw [hev]
        exact hz
      have hR0 : R = 0 := by
        by_contra hR
        have hle := natDegree_le_of_dvd (hdiv R hRm) hR
        have hnz : R.coeff R.natDegree ≠ 0 := by
          rw [coeff_natDegree]
          exact leadingCoeff_ne_zero.mpr hR
        apply hnz
        change (∑ j ∈ Finset.range W.natDegree, C (r j) * X ^ j).coeff
          R.natDegree = 0
        rw [finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j hj
        have hjk : j ≠ R.natDegree := by
          have hjlt := Finset.mem_range.mp hj
          omega
        simp only [coeff_C_mul_X_pow, if_neg (Ne.symm hjk)]
      have hv0 : evalGerm (n + 1) R (coord (Fin.last n)) = 0 := by
        rw [hR0]
        exact eval₂_zero _ _
      rw [← hev, hv0, add_zero, ← hlast] at hqr
      rw [Ideal.mem_span_singleton]
      exact ⟨q, by rw [hqr, mul_comm]⟩
    · apply Ideal.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hmem
  have hne : evalGerm (n + 1) W (coord (Fin.last n)) ≠ 0 := by
    have ht : evalGerm (n + 1) W (coord (Fin.last n)) =
        comapEquiv (euclideanSnocCLE n) (shiftEval 0 W) := by
      rw [hlast, shiftEval_zero_monic hW.1,
        comapEquiv_euclideanSnocCLE_prodWeierstrassGerm]
    intro hz
    have hzero : shiftEval (E := ComplexModel n) 0 W = 0 := by
      apply (comapEquiv (euclideanSnocCLE n)).injective
      simpa only [map_zero, ← ht] using hz
    apply hW.1.ne_zero
    apply shiftEval_zero_injective
    simpa only [map_zero] using hzero
  refine ⟨W, hW, hdeg, heq, ?_⟩
  rw [← Ideal.span_singleton_prime hne, ← heq]
  infer_instance

end Hironaka.ActualCodimensionOneNoetherIdeal
