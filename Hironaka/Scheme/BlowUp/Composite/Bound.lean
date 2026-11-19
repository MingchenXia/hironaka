/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Composite.Transition
public import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Composite.Descend
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The exponent of Hironaka's `J(m)` on a chart

For an affine open `U` of `X`, generators `s` of `I(U)` and a chart `c ∈ s`, the ideal of
`J' · E^m` on the chart of `c` is `J'_c · (c)^m`; for `m` large every generator `g = y/cⁿ` of `J'_c`
gives `g · c^m = c^{m-n} y`, a function on `U` that lies in `I(U)^m` and whose pullback lies in
`J' · E^m` on every chart `a ∈ s` — because `(c/a)^{m-n} · (y/aⁿ) ∈ J'_a` once `m - n` exceeds the
exponent of `Hironaka.Scheme.BlowUp.Composite.Transition` — hence lies in Hironaka's `K_m(U)`.  So
`J'_c · (c)^m ≤ K_m(U) · Γ(X, U)[I(U)/c]` for `m ≥ m₀(U, c)` (`exists_chartIdeal_mul_pow_le`), the
chart-level form of `J' · E^m ≤ K_m.comap b`; the exponents are finite maxima because `X` is
Noetherian (finitely generated `I(U)` and `J'_c`).  This is the chart computation behind the
"sufficiently large integer `m`" of Hironaka's `J(m)` [Hir64, Ch. 0, §3, p. 133];
`Hironaka.Scheme.BlowUp.Composite.Main` takes the maximum over finitely many `U` and `c`.
-/

public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

namespace affineBlowUpAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R) {a c : R}

theorem fracPow_mul_algebraMap_pow (n : ℕ) {y : R} (hy : y ∈ I ^ n) :
    (fracPow I n hy : affineBlowUpAlgebra I a) * algebraMap R (affineBlowUpAlgebra I a) a ^ n =
      algebraMap R (affineBlowUpAlgebra I a) y := by
  apply Subtype.ext
  change awayFrac a n y * algebraMap R (Localization.Away a) a ^ n =
    algebraMap R (Localization.Away a) y
  rw [← map_pow, awayFrac_mul_algebraMap_pow]

/-- `(y/aⁿ) · a^{n+j} = a^j y` in `R[I/a]`. -/
theorem fracPow_mul_algebraMap_pow_add (n j : ℕ) {y : R} (hy : y ∈ I ^ n) :
    (fracPow I n hy : affineBlowUpAlgebra I a) *
        algebraMap R (affineBlowUpAlgebra I a) a ^ (n + j) =
      algebraMap R (affineBlowUpAlgebra I a) (a ^ j * y) := by
  rw [pow_add, ← mul_assoc, fracPow_mul_algebraMap_pow, map_mul, map_pow, mul_comm]

variable (hc : c ∈ I)

/-- `c = a · (c/a)` in `R[I/a]`. -/
theorem algebraMap_eq_mul_frac :
    algebraMap R (affineBlowUpAlgebra I a) c =
      algebraMap R (affineBlowUpAlgebra I a) a * frac (a := a) hc := by
  apply Subtype.ext
  change algebraMap R (Localization.Away a) c = algebraMap R (Localization.Away a) a *
    (algebraMap R (Localization.Away a) c * IsLocalization.Away.invSelf a)
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

/-- `c^k y = a^{n+k} · ((c/a)^k · (y/aⁿ))` in `R[I/a]`, for `y ∈ Iⁿ`. -/
theorem algebraMap_pow_mul (n k : ℕ) {y : R} (hy : y ∈ I ^ n) :
    algebraMap R (affineBlowUpAlgebra I a) (c ^ k * y) =
      algebraMap R (affineBlowUpAlgebra I a) a ^ (n + k) *
        (frac (a := a) hc ^ k * fracPow I n hy) := by
  rw [map_mul, map_pow, algebraMap_eq_mul_frac I hc, ← fracPow_mul_algebraMap_pow I n hy]
  ring

/-- From the exponent `N` of `Hironaka.Scheme.BlowUp.Composite.Transition` to all `k ≥ N`. -/
theorem pow_frac_mul_mem_of_le {Q : Ideal (affineBlowUpAlgebra I a)} (n : ℕ) {y : R}
    (hy : y ∈ I ^ n) {N : ℕ} (hN : frac (a := a) hc ^ N * fracPow I n hy ∈ Q) {k : ℕ}
    (hk : N ≤ k) : frac (a := a) hc ^ k * fracPow I n hy ∈ Q := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm (frac hc ^ N), mul_assoc]
  exact Ideal.mul_mem_left _ _ hN

end affineBlowUpAlgebra

section Bound

variable {X : Scheme.{u}} (I : X.IdealSheafData) (J' : (blowUp I).IdealSheafData)
  (U : X.affineOpens)

/-- The chart ideal of `J' · E^m` is `J'_a · (a)^m`. -/
theorem chartIdeal_mul_pow (a : I.ideal U) (m : ℕ) :
    chartIdeal I (J' * I.exceptionalDivisor ^ m) U a =
      chartIdeal I J' U a *
        Ideal.span {algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) a) a} ^ m :=
  specIdealSheaf_inj
    ((comap_chart_eq_specIdealSheaf I _ U a).symm.trans (comap_mul_pow_chart I J' U a m))

/-- The exponent for a generator `y/cⁿ` of `J'_c`, uniform over the finitely many charts `a ∈ s`:
`(c/a)^k · (y/aⁿ) ∈ J'_a` for all `k ≥ N` and `a ∈ s`. -/
theorem exists_bound_of_mem_chartIdeal (s : Finset (I.ideal U)) (c : I.ideal U) (n : ℕ)
    {y : Γ(X, U)} (hy : y ∈ (I.ideal U) ^ n)
    (hz : affineBlowUpAlgebra.fracPow (I.ideal U) n hy ∈ chartIdeal I J' U c) :
    ∃ N : ℕ, ∀ a ∈ s, ∀ k, N ≤ k →
      affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) c.2 ^ k *
        affineBlowUpAlgebra.fracPow (I.ideal U) n hy ∈ chartIdeal I J' U a := by
  have h : ∀ a : I.ideal U, ∃ N : ℕ, affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) c.2 ^ N *
      affineBlowUpAlgebra.fracPow (I.ideal U) n hy ∈ chartIdeal I J' U a := fun a =>
    affineBlowUpAlgebra.exists_pow_frac_mul_mem (I.ideal U) c.2 a.2
      (chartIdeal_map_transition I J' U c a) n hy hz
  choose N hN using h
  obtain ⟨M, hM⟩ := Finite.exists_le (fun a : s => N a)
  exact ⟨M, fun a ha k hk => affineBlowUpAlgebra.pow_frac_mul_mem_of_le (I.ideal U) c.2 n hy (hN a)
    ((hM ⟨a, ha⟩).trans hk)⟩

/-- The membership `c^k y ∈ K_{n+k}(U)`: for `k ≥ N` (the exponent of `y/cⁿ`), the function
`c^k y ∈ I(U)^{n+k}` lies in Hironaka's `K_{n+k}(U)` — on every chart `a ∈ s` its pullback is
`a^{n+k} · ((c/a)^k · (y/aⁿ)) ∈ J'_a · (a)^{n+k}`. -/
theorem mem_descendCenter_ideal [IsLocallyNoetherian X] (s : Finset (I.ideal U))
    (hs : Ideal.span (Subtype.val '' (s : Set (I.ideal U))) = I.ideal U) (c : I.ideal U) (n : ℕ)
    {y : Γ(X, U)} (hy : y ∈ (I.ideal U) ^ n) {N : ℕ}
    (hN : ∀ a ∈ s, ∀ k, N ≤ k → affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) c.2 ^ k *
      affineBlowUpAlgebra.fracPow (I.ideal U) n hy ∈ chartIdeal I J' U a)
    (k : ℕ) (hk : N ≤ k) :
    (c : Γ(X, U)) ^ k * y ∈ (descendCenter I J' (n + k)).ideal U := by
  rw [descendCenter, ideal_inf, Pi.inf_apply, Submodule.mem_inf, ideal_pow, Pi.pow_apply,
    mem_ideal_map_iff_chart I _ U (s : Set (I.ideal U)) hs]
  refine ⟨?_, fun a ha => ?_⟩
  · rw [add_comm, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow c.2 k) hy
  · rw [chartIdeal_mul_pow, affineBlowUpAlgebra.algebraMap_pow_mul (I.ideal U) c.2 n k hy,
      mul_comm (chartIdeal I J' U a)]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) (n + k))
      (hN a ha k hk)

/-- The generator step: a generator `y/cⁿ` of `J'_c` times `c^{n+N+k}` is the pullback of the
function `c^{N+k} y ∈ K_{n+N+k}(U)`. -/
theorem fracPow_mul_algebraMap_pow_mem_map [IsLocallyNoetherian X] (s : Finset (I.ideal U))
    (hs : Ideal.span (Subtype.val '' (s : Set (I.ideal U))) = I.ideal U) (c : I.ideal U) (n : ℕ)
    {y : Γ(X, U)} (hy : y ∈ (I.ideal U) ^ n) {N : ℕ}
    (hN : ∀ a ∈ s, ∀ k, N ≤ k → affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) c.2 ^ k *
      affineBlowUpAlgebra.fracPow (I.ideal U) n hy ∈ chartIdeal I J' U a) (k : ℕ) :
    affineBlowUpAlgebra.fracPow (I.ideal U) n hy *
        algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) c ^ (n + (N + k)) ∈
      ((descendCenter I J' (n + (N + k))).ideal U).map
        (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c)) := by
  rw [affineBlowUpAlgebra.fracPow_mul_algebraMap_pow_add]
  exact Ideal.mem_map_of_mem _
    (mem_descendCenter_ideal I J' U s hs c n hy hN (N + k) (Nat.le_add_right _ _))

/-- Closure of `r ↦ r · t ∈ Q` under the span. -/
theorem mul_mem_of_mem_span {A : Type*} [CommRing A] {G : Set A} {t : A} {Q : Ideal A}
    (h : ∀ g ∈ G, g * t ∈ Q) : ∀ r ∈ Ideal.span G, r * t ∈ Q := by
  intro r hr
  refine Submodule.span_induction (p := fun r _ => r * t ∈ Q) h ?_ ?_ ?_ hr
  · rw [zero_mul]
    exact zero_mem _
  · intro r₁ r₂ _ _ h₁ h₂
    rw [add_mul]
    exact add_mem h₁ h₂
  · intro v r _ h
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ v h

/-- The generator step with the exponent bound: for a generator `g = y/cⁿ` of `J'_c` with exponent
`N` and `m ≥ n + N`, `g · c^m` is the pullback of a function of `K_m(U)`. -/
theorem gen_mul_pow_mem_map [IsLocallyNoetherian X] (s : Finset (I.ideal U))
    (hs : Ideal.span (Subtype.val '' (s : Set (I.ideal U))) = I.ideal U) (c : I.ideal U)
    (g : affineBlowUpAlgebra (I.ideal U) c) (n : ℕ) {y : Γ(X, U)} (hy : y ∈ (I.ideal U) ^ n)
    (hg : g = affineBlowUpAlgebra.fracPow (I.ideal U) n hy) {N : ℕ}
    (hN : ∀ a ∈ s, ∀ k, N ≤ k → affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) c.2 ^ k *
      affineBlowUpAlgebra.fracPow (I.ideal U) n hy ∈ chartIdeal I J' U a)
    (m : ℕ) (hm : n + N ≤ m) :
    g * algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) c ^ m ∈
      ((descendCenter I J' m).ideal U).map
        (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  have hm' : m = n + (N + k) := by omega
  subst hg
  rw [hm']
  exact fracPow_mul_algebraMap_pow_mem_map I J' U s hs c n hy hN k

/-- The chart-level inequality: on the chart of `c ∈ s`, for `m ≥ m₀(U, c)`,
`J'_c · (c)^m ≤ K_m(U) · Γ(X, U)[I(U)/c]`. -/
theorem exists_chartIdeal_mul_pow_le [IsLocallyNoetherian X] (s : Finset (I.ideal U))
    (hs : Ideal.span (Subtype.val '' (s : Set (I.ideal U))) = I.ideal U) (c : I.ideal U) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      chartIdeal I J' U c *
          Ideal.span {algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) c} ^ m ≤
        ((descendCenter I J' m).ideal U).map
          (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c)) := by
  have := IsLocallyNoetherian.component_noetherian U
  have hnoeth := isNoetherianRing_affineBlowUpAlgebra (I.ideal U) (c : Γ(X, U))
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian (chartIdeal I J' U c)
  have hrep : ∀ g : G, ∃ n : ℕ, ∃ y : Γ(X, U), ∃ hy : y ∈ (I.ideal U) ^ n,
      (g : affineBlowUpAlgebra (I.ideal U) c) = affineBlowUpAlgebra.fracPow (I.ideal U) n hy := by
    intro g
    obtain ⟨n, y, hy, hgy⟩ :=
      (mem_affineBlowUpAlgebra_iff c.2).mp (g : affineBlowUpAlgebra (I.ideal U) c).2
    exact ⟨n, y, hy, Subtype.ext hgy⟩
  choose n y hy hg using hrep
  have hbound : ∀ g : G, ∃ N : ℕ, ∀ a ∈ s, ∀ k, N ≤ k →
      affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) c.2 ^ k *
        affineBlowUpAlgebra.fracPow (I.ideal U) (n g) (hy g) ∈ chartIdeal I J' U a := fun g =>
    exists_bound_of_mem_chartIdeal I J' U s c (n g) (hy g)
      (by rw [← hg g, ← hG]; exact Ideal.subset_span g.2)
  choose N hN using hbound
  obtain ⟨M, hM⟩ := Finite.exists_le (fun g : G => n g + N g)
  refine ⟨M, fun m hm => ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.mul_le]
  intro r hr t ht
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  rw [mul_left_comm]
  refine Ideal.mul_mem_left _ u ?_
  rw [← hG] at hr
  exact mul_mem_of_mem_span (fun g hgG => gen_mul_pow_mem_map I J' U s hs c g (n ⟨g, hgG⟩)
    (hy ⟨g, hgG⟩) (hg ⟨g, hgG⟩) (hN ⟨g, hgG⟩) m ((hM ⟨g, hgG⟩).trans hm)) r hr

end Bound

end AlgebraicGeometry
