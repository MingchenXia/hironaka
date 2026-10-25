import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The principal maximal ideal base case for regular-local domain theory

Krull intersection constructs exact orders and actual unit-times-power
expressions before any domain or non-zero-divisor assumption is introduced.
-/

open IsLocalRing

namespace DeJongAlterations.Algebra.RegularLocalDomainPrincipal

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A nonzero element has an actual finite maximal-ideal-adic order. -/
theorem exists_exact_maximalIdeal_order (x : R) (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ maximalIdeal R ^ n ∧ x ∉ maximalIdeal R ^ (n + 1) := by
  classical
  have hex : ∃ n : ℕ, x ∉ maximalIdeal R ^ n := by
    by_contra! hall
    have hm : x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
      simpa only [Submodule.mem_iInf] using hall
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hm
    exact hx (by simpa using hm)
  have hk : Nat.find hex ≠ 0 := by
    intro hzero
    have h := Nat.find_spec hex
    simp [hzero] at h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk
  refine ⟨n, ?_, ?_⟩
  · by_contra hnot
    have hle := Nat.find_min' hex hnot
    omega
  · simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec hex

/-- Principal maximal ideals give actual unit-times-power expressions without a domain hypothesis. -/
theorem exists_unit_mul_pow (t : R) (hm : maximalIdeal R = Ideal.span {t})
    (x : R) (hx : x ≠ 0) : ∃ (n : ℕ) (u : Rˣ), x = (u : R) * t ^ n := by
  obtain ⟨n, hxn, hxnext⟩ := exists_exact_maximalIdeal_order x hx
  have hpow : t ^ n ∈ maximalIdeal R ^ n := by
    rw [hm, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxn
  obtain ⟨a, rfl⟩ := hxn
  have hu : IsUnit a := by
    by_contra hnu
    apply hxnext
    rw [pow_succ]
    exact Ideal.mul_mem_mul hpow hnu
  exact ⟨n, hu.unit, by rw [hu.unit_spec, mul_comm]⟩

/-- A Noetherian local ring with a nonnilpotent principal maximal-ideal generator is a domain. -/
theorem isDomain_of_principal_maximalIdeal_not_isNilpotent
    (t : R) (hm : maximalIdeal R = Ideal.span {t}) (ht : ¬ IsNilpotent t) : IsDomain R := by
  let : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨n, u, rfl⟩ := exists_unit_mul_pow t hm a ha
    obtain ⟨m, v, rfl⟩ := exists_unit_mul_pow t hm b hb
    have hprod : ((u * v : Rˣ) : R) * t ^ (n + m) = 0 := by
      simpa only [Units.val_mul, pow_add, mul_assoc, mul_left_comm, mul_comm] using hab
    have hpow : t ^ (n + m) = 0 := (u * v).isUnit.mul_right_eq_zero.mp hprod
    exact (ht ⟨n + m, hpow⟩).elim⟩
  exact NoZeroDivisors.to_isDomain R

omit [IsNoetherianRing R] in
/-- A nilpotent maximal-ideal generator would force all primes to be maximal and dimension zero. -/
theorem not_isNilpotent_of_principal_maximalIdeal_of_pos_dim
    (t : R) (hm : maximalIdeal R = Ideal.span {t}) (hdim : 0 < ringKrullDim R) :
    ¬ IsNilpotent t := by
  rintro ⟨n, hn⟩
  have hz : Ring.KrullDimLE 0 R := Ring.KrullDimLE.mk₀ (fun I hI => by
    have htI : t ∈ I := hI.mem_of_pow_mem n (by rw [hn]; exact I.zero_mem)
    have hmI : maximalIdeal R ≤ I := by
      rw [hm]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr htI)
    have heq : maximalIdeal R = I :=
      Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal R) hI.ne_top hmI
    rw [← heq]
    infer_instance)
  exact (not_le_of_gt hdim) (Ring.krullDimLE_iff.mp hz)

/-- The positive-dimensional principal-maximal-ideal local ring base case is an actual domain. -/
theorem isDomain_of_principal_maximalIdeal_of_pos_dim
    (t : R) (hm : maximalIdeal R = Ideal.span {t}) (hdim : 0 < ringKrullDim R) : IsDomain R :=
  isDomain_of_principal_maximalIdeal_not_isNilpotent t hm
    (not_isNilpotent_of_principal_maximalIdeal_of_pos_dim t hm hdim)

end DeJongAlterations.Algebra.RegularLocalDomainPrincipal
