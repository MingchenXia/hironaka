import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual localization intersections from a regular pair

Regularity modulo the first element gives power saturation. Native fraction-field
localization subalgebras then have exactly the original coefficient intersection.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DeJongAlterations.Algebra.NodeNormalIntersection

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- Actual regularity in the principal quotient removes the second factor from divisibility. -/
theorem dvd_of_dvd_mul (x y a : R)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span {x}) y)) (h : x ∣ y * a) : x ∣ a := by
  have hzero : Ideal.Quotient.mk (Ideal.span {x}) (y * a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  have ha : Ideal.Quotient.mk (Ideal.span {x}) a = 0 :=
    hy.left (by
      change Ideal.Quotient.mk (Ideal.span {x}) y * Ideal.Quotient.mk (Ideal.span {x}) a =
        Ideal.Quotient.mk (Ideal.span {x}) y * 0
      rw [mul_zero, ← map_mul]
      exact hzero)
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)

/-- A genuine regular pair has actual power saturation, without a supplied saturation witness. -/
theorem power_dvd_of_dvd_mul_pow (x y : R) (hx : x ≠ 0)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span {x}) y)) (n m : ℕ) (a : R)
    (h : x ^ n ∣ y ^ m * a) : x ^ n ∣ a := by
  have hym : IsRegular (Ideal.Quotient.mk (Ideal.span {x}) (y ^ m)) := by
    simpa only [map_pow] using hy.pow m
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hxpow : x ∣ x ^ (n + 1) := ⟨x ^ n, by rw [pow_succ]; ring⟩
    obtain ⟨b, rfl⟩ := dvd_of_dvd_mul x (y ^ m) a hym (hxpow.trans h)
    have hn : x ^ n ∣ y ^ m * b := by
      obtain ⟨c, hc⟩ := h
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hx
      calc
        x * (y ^ m * b) = y ^ m * (x * b) := by ring
        _ = x ^ (n + 1) * c := hc
        _ = x * (x ^ n * c) := by rw [pow_succ]; ring
    obtain ⟨c, hc⟩ := ih b hn
    refine ⟨c, ?_⟩
    rw [hc, pow_succ]
    ring

variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual away-localization subalgebra in the original fraction field. -/
abbrev awaySubalgebra (x : R) (hx : x ≠ 0) : Subalgebra R K :=
  Localization.subalgebra K (Submonoid.powers x) (powers_le_nonZeroDivisors_of_noZeroDivisors hx)

/-- The two actual localization subalgebras intersect in precisely the original coefficient subalgebra. -/
theorem away_inf_eq_bot (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hreg : IsRegular (Ideal.Quotient.mk (Ideal.span {x}) y)) :
    awaySubalgebra K x hx ⊓ awaySubalgebra K y hy = ⊥ := by
  apply le_antisymm
  · intro z hz
    have hu : z ∈ Localization.subalgebra.ofField K (Submonoid.powers x)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hx) := by
      rw [Localization.subalgebra.ofField_eq]
      exact hz.1
    have hv : z ∈ Localization.subalgebra.ofField K (Submonoid.powers y)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hy) := by
      rw [Localization.subalgebra.ofField_eq]
      exact hz.2
    obtain ⟨a, s, hs, hu⟩ := hu
    obtain ⟨b, t, ht, hv⟩ := hv
    obtain ⟨n, rfl⟩ := hs
    obtain ⟨m, rfl⟩ := ht
    have hxn : algebraMap R K (x ^ n) ≠ 0 :=
      map_ne_zero_iff _ (IsFractionRing.injective R K) |>.mpr (pow_ne_zero n hx)
    have hym : algebraMap R K (y ^ m) ≠ 0 :=
      map_ne_zero_iff _ (IsFractionRing.injective R K) |>.mpr (pow_ne_zero m hy)
    have hu' : z * algebraMap R K (x ^ n) = algebraMap R K a :=
      (eq_div_iff hxn).mp (by simpa only [div_eq_mul_inv] using hu)
    have hv' : z * algebraMap R K (y ^ m) = algebraMap R K b :=
      (eq_div_iff hym).mp (by simpa only [div_eq_mul_inv] using hv)
    have hab : a * y ^ m = b * x ^ n := by
      apply IsFractionRing.injective R K
      calc
        algebraMap R K (a * y ^ m) = (z * algebraMap R K (x ^ n)) * algebraMap R K (y ^ m) := by
          rw [map_mul, hu']
        _ = (z * algebraMap R K (y ^ m)) * algebraMap R K (x ^ n) := by ring
        _ = algebraMap R K (b * x ^ n) := by rw [hv', map_mul]
    have hdiv : x ^ n ∣ y ^ m * a := ⟨b, by simpa only [mul_comm] using hab⟩
    obtain ⟨c, hc⟩ := power_dvd_of_dvd_mul_pow x y hx hreg n m a hdiv
    apply Algebra.mem_bot.mpr
    refine ⟨c, ?_⟩
    calc
      algebraMap R K c = (algebraMap R K (x ^ n) * algebraMap R K c) /
          algebraMap R K (x ^ n) := by rw [mul_div_cancel_left₀ _ hxn]
      _ = algebraMap R K a / algebraMap R K (x ^ n) := by rw [← map_mul, ← hc]
      _ = z := hu'.symm ▸ (mul_div_cancel_right₀ z hxn)
  · exact bot_le

/-- Normality of the two actual away rings and a genuine regular pair imply normality of the domain. -/
theorem isIntegrallyClosed_of_regular_pair (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hreg : IsRegular (Ideal.Quotient.mk (Ideal.span {x}) y))
    (hxu : IsIntegrallyClosed (Localization.Away x))
    (hyv : IsIntegrallyClosed (Localization.Away y)) : IsIntegrallyClosed R := by
  let f : Fin 2 → R := ![x, y]
  have hnz (i : Fin 2) : f i ≠ 0 := by fin_cases i <;> assumption
  apply IsIntegrallyClosed.of_localization_submonoid (fun i : Fin 2 => Submonoid.powers (f i))
    (fun i => powers_le_nonZeroDivisors_of_noZeroDivisors (hnz i))
  · intro i
    fin_cases i
    · exact hxu
    · exact hyv
  · apply le_antisymm
    · rw [← away_inf_eq_bot (FractionRing R) x y hx hy hreg]
      exact le_inf (iInf_le _ (0 : Fin 2)) (iInf_le _ (1 : Fin 2))
    · exact bot_le

end DeJongAlterations.Algebra.NodeNormalIntersection
