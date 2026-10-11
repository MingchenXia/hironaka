/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermPrimeNullstellensatz
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset


set_option autoImplicit false

/-!
# Actual prime zero germs and simultaneous finite avoidance

The complete mathematical statements and ENTIRE proofs precede the import
baseline.  Inputs are original holomorphic functions and ordinary prime
germ/nondivisibility conditions, not irreducibility or avoidance certificates.
-/

open Hironaka

noncomputable section
open Set Filter
open scoped Topology

namespace Hironaka.ActualPrimeGermGenericAvoidance

open AnalyticGermDecomposition

variable {n : ℕ}

/-- The original prime function produces its actual vanishing ideal and
irreducible zero germ; neither is an input certificate. -/
theorem vanishingIdeal_zeroSet_eq_and_irreducible
    (q : EuclideanSpace ℂ (Fin n) → ℂ)
    (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq)) :
    vanishingIdeal {z | q z = 0} = Ideal.span {HolGerm.mk q hq} ∧
      IsIrreducibleGerm {z | q z = 0} := by
  let I : Ideal (HolGerm (EuclideanSpace ℂ (Fin n))) := Ideal.span {HolGerm.mk q hq}
  let : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hQ
  have hle : vanishingIdeal {z | q z = 0} ≤ I := by
    simpa only [Fin.forall_fin_one] using
      GermPrimeNullstellensatz.vanishingIdeal_le_of_isPrime I (fun _ : Fin 1 => q)
        (fun _ => ⟨hq, Ideal.mem_span_singleton_self _⟩)
  have hreverse : I ≤ vanishingIdeal {z | q z = 0} := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain rfl := Set.mem_singleton_iff.mp hg
    exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun _ hz => hz)
  have hEq : vanishingIdeal {z | q z = 0} = I := le_antisymm hle hreverse
  refine ⟨hEq, (isIrreducibleGerm_iff_isPrime (isAnalyticGerm_zeroSet hq)).mpr ?_⟩
  rw [hEq]
  exact inferInstance

private theorem exists_mk_finset_prod {ι : Type*} (s : Finset ι)
    (a : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (ha : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a i) z) :
    ∃ hP : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun x => ∏ i ∈ s, a i x) z,
      HolGerm.mk (fun x => ∏ i ∈ s, a i x) hP = ∏ i ∈ s, HolGerm.mk (a i) (ha i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (⟨eventually_differentiableAt_one, HolGerm.mk_one⟩ :
        ∃ hP : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)),
            DifferentiableAt ℂ (fun _ => (1 : ℂ)) z,
          HolGerm.mk (fun _ => (1 : ℂ)) hP = 1)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    obtain ⟨hP, hPC⟩ := ih
    refine ⟨eventually_differentiableAt_mul (ha i) hP, ?_⟩
    rw [HolGerm.mk_mul (a i) (fun x => ∏ j ∈ s, a j x) (ha i) hP, hPC]

/-- Every neighborhood of the origin contains a zero of the original prime
function avoiding all the original finite nondivisible test functions. -/
theorem frequently_zero_avoiding_finite_family {ι : Type*} [Fintype ι]
    (q : EuclideanSpace ℂ (Fin n) → ℂ)
    (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq))
    (a : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (ha : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a i) z)
    (hnot : ∀ i, ¬HolGerm.mk q hq ∣ HolGerm.mk (a i) (ha i)) :
    ∃ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), q z = 0 ∧ ∀ i, a i z ≠ 0 := by
  classical
  have hnotprod (s : Finset ι) : ¬HolGerm.mk q hq ∣ ∏ i ∈ s, HolGerm.mk (a i) (ha i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using hQ.not_dvd_one
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      intro hdiv
      exact (hQ.dvd_or_dvd hdiv).elim (hnot i) ih
  obtain ⟨hP, hPC⟩ := exists_mk_finset_prod Finset.univ a ha
  by_contra hfreq
  have hev := Filter.not_frequently.mp hfreq
  have hmem : HolGerm.mk (fun z => ∏ i, a i z) hP ∈ vanishingIdeal {z | q z = 0} := by
    apply mem_vanishingIdeal_mk.mpr
    refine hev.mono fun z hz hzq => ?_
    by_contra hprod
    apply hz
    refine ⟨hzq, fun i hi => ?_⟩
    exact hprod (Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ i, hi⟩)
  rw [(vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1,
    Ideal.mem_span_singleton, hPC] at hmem
  exact hnotprod Finset.univ hmem

end Hironaka.ActualPrimeGermGenericAvoidance
