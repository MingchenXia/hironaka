import Hironaka.Analytic.HolomorphicNormalOrderDiscrepancy
import Hironaka.Analytic.HolomorphicGermReducednessBridge
import Hironaka.Analytic.SNCEuclideanCoordinateMultiplier
import Hironaka.Analytic.ComplexMonomialMultiplierUnit

set_option autoImplicit false

/-! # All coordinate factors of an arbitrary holomorphic test

The original test may have extra zeros and the remaining holomorphic factor
may vanish at zero. Actual Noetherian local-germ separation supplies all finite
orders; the sufficient multiplier criterion permits an arbitrary holomorphic
quotient. The necessity criterion and a valuative converse are separate results.
Reference: Demailly, *Complex Analytic and Differential Geometry*, local germ
algebra; *Analytic Methods in Algebraic Geometry*, multiplier ideal definition.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.HolomorphicCoordinateOrders

open HolomorphicGermReducednessBridge

noncomputable section

private theorem exists_finite_product_factorization
    {R : Type*} [CommMonoidWithZero R] {ι : Type*} [DecidableEq ι]
    (p : ι → R) (hfinite : ∀ i g, g ≠ 0 → FiniteMultiplicity (p i) g)
    (s : Finset ι) {g : R} (hg : g ≠ 0) :
    ∃ (a : ι → ℕ) (h : R), h ≠ 0 ∧
      g = (∏ i ∈ s, p i ^ a i) * h ∧ ∀ i ∈ s, ¬p i ∣ h := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty =>
      exact ⟨fun _ => 0, g, hg, by simp, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨q, hgq, hnot⟩ := (hfinite i g hg).exists_eq_pow_mul_and_not_dvd
      have hq : q ≠ 0 := by
        intro heq
        exact hg (by simpa only [heq, mul_zero] using hgq)
      obtain ⟨a, h, hh, hqh, hall⟩ := ih hq
      let a' := Function.update a i (multiplicity (p i) g)
      have hprod : (∏ j ∈ insert i s, p j ^ a' j) =
          p i ^ multiplicity (p i) g * ∏ j ∈ s, p j ^ a j := by
        rw [Finset.prod_insert hi]
        simp only [a', Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
      refine ⟨a', h, hh, ?_, ?_⟩
      · rw [hprod, mul_assoc, ← hqh]
        exact hgq
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · intro hdiv
          apply hnot
          have hdivq : h ∣ q := ⟨∏ j ∈ s, p j ^ a j, by rw [hqh]; ac_rfl⟩
          exact hdiv.trans hdivq
        · exact hall j hj

private theorem eventually_differentiableAt_product
    {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem mk_product
    {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (eventually_differentiableAt_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) : (ComplexModel n → ℂ) →+*
      Germ (𝓝 (0 : ComplexModel n)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

/-- Every coordinate factor is internally extracted; the remaining test may
have additional zeros and need not be a unit at the center. -/
theorem exists_coordinate_factorization_of_nonzero_germ
    {n : ℕ} {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0) :
    ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ)
      (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z),
      (∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0) ∧
      F =ᶠ[𝓝 0] (fun z => H z * ∏ j : Fin n, z j ^ a j) ∧
      ∀ j : Fin n, ¬HolGerm.mk (fun z : ComplexModel n => z j)
        (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH := by
  classical
  let R := HolGerm (ComplexModel n)
  let : IsNoetherianRing R := isNoetherianRing_holGerm_euclidean n
  let p : Fin n → R := fun j => HolGerm.mk (fun z : ComplexModel n => z j)
    (eventually_differentiableAt_coordinate j)
  let g : R := HolGerm.mk F hF
  have hg : g ≠ 0 := by
    intro hzero
    have heq : F =ᶠ[𝓝 (0 : ComplexModel n)] fun _ => (0 : ℂ) :=
      HolGerm.mk_eq_mk_iff.mp (hzero.trans HolGerm.mk_zero.symm)
    obtain ⟨z, hz, hz0⟩ := (hne.and_eventually heq).exists
    exact hz hz0
  have hfinite (j : Fin n) (h : R) (hh : h ≠ 0) : FiniteMultiplicity (p j) h := by
    let M : Ideal R := IsLocalRing.maximalIdeal R
    have hpM : p j ∈ M := by
      rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk]
      simp
    by_contra hnot
    have hall := FiniteMultiplicity.not_iff_forall.mp hnot
    have hmem : h ∈ ⨅ N : ℕ, M ^ N := by
      refine (Submodule.mem_iInf _).mpr fun N => ?_
      obtain ⟨q, hq⟩ := hall N
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpM N)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing M (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
      at hmem
    exact hh hmem
  obtain ⟨a, h, hh, hfactor, hnot⟩ :=
    exists_finite_product_factorization p hfinite Finset.univ hg
  obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk h
  have hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0 := by
    by_contra hnot
    have heq : H =ᶠ[𝓝 (0 : ComplexModel n)] fun _ => (0 : ℂ) := by
      filter_upwards [Filter.not_frequently.mp hnot] with z hz
      exact not_ne_iff.mp hz
    apply hh
    exact (HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero
  let M : ComplexModel n → ℂ := fun z => ∏ j : Fin n, z j ^ a j
  have hM : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ M z :=
    eventually_differentiableAt_product Finset.univ
      (fun (j : Fin n) (z : ComplexModel n) => z j ^ a j)
      (fun j => eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) (a j))
  have hmon : HolGerm.mk M hM = ∏ j : Fin n, p j ^ a j := by
    rw [mk_product]
    apply Finset.prod_congr rfl
    intro j _
    exact HolGerm.mk_pow (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) (a j)
  refine ⟨a, H, hH, hHnon, ?_, fun j => hnot j (Finset.mem_univ j)⟩
  apply (HolGerm.mk_eq_mk_iff (hf := hF)
    (hg := eventually_differentiableAt_mul hH hM)).mp
  calc
    HolGerm.mk F hF = (∏ j : Fin n, p j ^ a j) * HolGerm.mk H hH := hfactor
    _ = HolGerm.mk H hH * HolGerm.mk M hM := by rw [hmon, mul_comm]
    _ = HolGerm.mk (fun z => H z * M z) (eventually_differentiableAt_mul hH hM) :=
      (HolGerm.mk_mul H M hH hM).symm

/-- Sufficient literal multiplier membership with an arbitrary holomorphic
quotient, including a quotient vanishing at zero. -/
theorem multiplierIntegrableAt_of_coordinate_factorization
    {n : ℕ} (a : Fin n → ℕ) (b : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    {F H : ComplexModel n → ℂ} {ρ : ComplexModel n → ℝ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin n, z j ^ a j)
    (hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z)
    (hthreshold : ∀ j : Fin n, c * b j < (a j : ℝ) + 1) :
    MultiplierIntegrableAt (fun z : ComplexModel n =>
      (∑ j, ((2 * b j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (ρ z : EReal))
      c F 0 volume := by
  have hunit : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun _ : ComplexModel n => (1 : ℂ)) z :=
    Eventually.of_forall fun _ => differentiableAt_const _
  have hmon := (SNCEuclideanCoordinateMultiplier.multiplierIntegrableAt_sum_log_unit_monomial_iff
    a b hc hunit (by norm_num : (1 : ℂ) ≠ 0) hρ).mpr hthreshold
  have hmon' : MultiplierIntegrableAt (fun z : ComplexModel n =>
      (∑ j, ((2 * b j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (ρ z : EReal))
      c (fun z => ∏ j : Fin n, z j ^ a j) 0 volume := by
    simpa only [one_mul] using hmon
  exact (multiplierIntegrableAt_differentiable_mul hmon' hH).congr EventuallyEq.rfl heq.symm

end
end Hironaka.HolomorphicCoordinateOrders
