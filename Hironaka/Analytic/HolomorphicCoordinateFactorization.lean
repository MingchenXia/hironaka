/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicCoordinatePrime
import Hironaka.Analytic.RueckertNullstellensatz
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Divisibility.Basic

set_option autoImplicit false

/-! # Genuine coordinate monomial factorization from the actual local zero locus -/

open Set Filter
open scoped Topology

namespace Hironaka.HolomorphicCoordinateFactorization

open HolomorphicGermReducednessBridge AnalyticGermDecomposition

noncomputable section

/-- Decomposition and the actual prime-power divisor theorem supply every exponent. -/
theorem exists_associated_prod_pow_of_dvd_prod_pow
    {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] [DecompositionMonoid R]
    {n : ℕ} (p : Fin n → R) (N : Fin n → ℕ) {d : R}
    (hp : ∀ i, Prime (p i)) (hd : d ∣ ∏ i, p i ^ N i) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ N i) ∧ Associated d (∏ i, p i ^ a i) := by
  induction n generalizing d with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    have hd1 : d ∣ 1 := by simpa only [Fin.prod_univ_zero] using hd
    simpa only [Fin.prod_univ_zero] using
      associated_one_iff_isUnit.mpr (isUnit_iff_dvd_one.mpr hd1)
  | succ n ih =>
    have hd' : d ∣ p 0 ^ N 0 * ∏ i : Fin n, p i.succ ^ N i.succ := by
      simpa only [Fin.prod_univ_succ] using hd
    obtain ⟨d₀, d', hd₀, hd', hdfac⟩ := exists_dvd_and_dvd_of_dvd_mul hd'
    obtain ⟨a₀, ha₀, hassoc₀⟩ := (dvd_prime_pow (hp 0) (N 0)).mp hd₀
    obtain ⟨a', ha', hassoc'⟩ := ih (fun i => p i.succ) (fun i => N i.succ)
      (fun i => hp i.succ) hd'
    refine ⟨Fin.cons a₀ a', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha₀
      · exact ha' j
    · rw [hdfac]
      simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using
        hassoc₀.mul_mul hassoc'

private theorem eventually_differentiableAt_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := E) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem mk_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (eventually_differentiableAt_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : E)) : (E → ℂ) →+* Germ (𝓝 (0 : E)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

/-- Actual radical membership produces a coordinate-product power in the principal ideal. -/
theorem exists_coordinate_product_power_dvd_of_zero_locus
    {n : ℕ} {G : ComplexModel n → ℂ}
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z)
    (hzero : ∀ᶠ z in 𝓝 0, G z = 0 → ∃ i : Fin n, z i = 0) :
    ∃ N : ℕ, HolGerm.mk G hG ∣
      (∏ i : Fin n, HolGerm.mk (fun z : ComplexModel n => z i)
        (eventually_differentiableAt_coordinate i)) ^ N := by
  let P : ComplexModel n → ℂ := fun z => ∏ i : Fin n, z i
  have hP : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ P z :=
    eventually_differentiableAt_product Finset.univ (fun (i : Fin n) (z : ComplexModel n) => z i)
      eventually_differentiableAt_coordinate
  have hvan : HolGerm.mk P hP ∈ vanishingIdeal {z | ∀ _ : Fin 1, G z = 0} := by
    apply mem_vanishingIdeal_mk.mpr
    filter_upwards [hzero] with z hz hzg
    obtain ⟨i, hi⟩ := hz (hzg 0)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let I : Ideal (HolGerm (ComplexModel n)) := Ideal.span {HolGerm.mk G hG}
  have hrad : HolGerm.mk P hP ∈ I.radical :=
    RueckertNullstellensatz.vanishingIdeal_le_radical I (fun _ : Fin 1 => G)
      (fun _ => ⟨hG, Ideal.subset_span (Set.mem_singleton _)⟩) hvan
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨N, ?_⟩
  have hdiv : HolGerm.mk G hG ∣ HolGerm.mk P hP ^ N :=
    Ideal.mem_span_singleton.mp hN
  have hprod : HolGerm.mk P hP = ∏ i : Fin n,
      HolGerm.mk (fun z : ComplexModel n => z i)
        (eventually_differentiableAt_coordinate i) :=
    mk_product Finset.univ (fun (i : Fin n) (z : ComplexModel n) => z i) eventually_differentiableAt_coordinate
  rw [hprod] at hdiv
  exact hdiv

/-- The unit and every monomial order follow from the actual zero locus and germ algebra. -/
theorem exists_unit_mul_coordinate_monomial_of_zero_locus
    {n : ℕ} {G : ComplexModel n → ℂ}
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z)
    (hzero : ∀ᶠ z in 𝓝 0, G z = 0 → ∃ i : Fin n, z i = 0) :
    ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
      (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
        G =ᶠ[𝓝 0] fun z => H z * ∏ i : Fin n, z i ^ a i := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  let p : Fin n → HolGerm (ComplexModel n) := fun i =>
    HolGerm.mk (fun z : ComplexModel n => z i) (eventually_differentiableAt_coordinate i)
  obtain ⟨N, hN⟩ := exists_coordinate_product_power_dvd_of_zero_locus hG hzero
  have hdiv : HolGerm.mk G hG ∣ ∏ i : Fin n, p i ^ N := by
    simpa only [Finset.prod_pow] using hN
  obtain ⟨a, _, hassoc⟩ := exists_associated_prod_pow_of_dvd_prod_pow p (fun _ => N)
    (fun i => HolomorphicCoordinatePrime.prime_coordinate_germ i) hdiv
  obtain ⟨v, hv⟩ := hassoc.symm
  obtain ⟨H, hH, hrep⟩ := HolGerm.exists_eq_mk (v : HolGerm (ComplexModel n))
  have hH0 : H 0 ≠ 0 := by
    have hval := (HolGerm.isUnit_iff_eval_ne_zero _).mp v.isUnit
    rw [hrep, HolGerm.eval_mk] at hval
    exact hval
  let M : ComplexModel n → ℂ := fun z => ∏ i : Fin n, z i ^ a i
  have hM : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ M z :=
    eventually_differentiableAt_product Finset.univ
      (fun (i : Fin n) (z : ComplexModel n) => z i ^ a i)
      (fun i => eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (a i))
  have hmon : HolGerm.mk M hM = ∏ i : Fin n, p i ^ a i := by
    have h := mk_product Finset.univ
      (fun (i : Fin n) (z : ComplexModel n) => z i ^ a i)
      (fun i => eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (a i))
    calc
      HolGerm.mk M hM = ∏ i : Fin n,
          HolGerm.mk (fun z : ComplexModel n => z i ^ a i)
            (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (a i)) := h
      _ = ∏ i : Fin n, p i ^ a i := by
        apply Finset.prod_congr rfl
        intro i _
        exact HolGerm.mk_pow (fun z : ComplexModel n => z i)
          (eventually_differentiableAt_coordinate i) (a i)
  refine ⟨a, H, hH, hH0, ?_⟩
  apply (HolGerm.mk_eq_mk_iff (hf := hG)
    (hg := eventually_differentiableAt_mul hH hM)).mp
  calc
    HolGerm.mk G hG = (∏ i : Fin n, p i ^ a i) * (v : HolGerm (ComplexModel n)) := hv.symm
    _ = HolGerm.mk H hH * HolGerm.mk M hM := by rw [hrep, ← hmon, mul_comm]
    _ = HolGerm.mk (fun z => H z * M z) (eventually_differentiableAt_mul hH hM) :=
      (HolGerm.mk_mul H M hH hM).symm

end
end Hironaka.HolomorphicCoordinateFactorization
