/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartRing
import Hironaka.Algebra.Local.Chart

/-!
# The birational transform of a marked ideal in the chart: definitions

For a marked ideal `(I, m)` with `m ≤ ord_Z I` on a smooth variety `X` with a smooth centre `Z`,
the birational transform is `π⁻¹_*(I, m) := (O_{B_Z X}(mF) · π^* I, m)` [Kol07, Definition 60,
(60.1)]; in local coordinates `x₁, …, xₙ` with `Z = (x₁ = ⋯ = x_r = 0)` and the chart
`yᵢ = xᵢ/x_r` (`i < r`), `y_r = x_r`, it is computed as
`π⁻¹_*(f, m) := (y_r^{-m} f(y₁ y_r, …, y_{r-1} y_r, y_r, …, yₙ), m)` [Kol07, Definition 60, (60.3)].

In the local model of `Hironaka/Algebra/Local/ChartRing.lean`: `R` is a commutative ring with a
family `x : Fin n → R` and a distinguished index `r : Fin n` (Kollár's `r`, zero-based), the centre
is `P = chartCenter x r = ⟨x₀, …, x_r⟩`, the chart ring is `R' = chartRing x r ⊆ R[1/x_r]` and
`φ = algebraMap R R'`.  This file defines

* `chartCenter x r`, the ideal `P` of the centre;
* `f ∈ P^m ⟹ φ f ∈ (x_r R')^m` (`algebraMap_mem_span_pow_of_mem_chartCenter_pow`), because
  `φ (xᵢ) = x_r · yᵢ` for `i < r` and `φ (x_r) = x_r`, so `P ≤ φ⁻¹(x_r R')` and
  `P^m ≤ φ⁻¹((x_r R')^m)` (`Ideal.le_comap_pow`); in particular `P R' = x_r R'`
  (`map_chartCenter`), the ideal of the exceptional divisor in the chart;
* the transform of a marked element, `transformElem x r f hf := f / x_r^m` (an element of
  `R[1/x_r]`, which lies in `R'` by the preceding item), and the transform of an ideal,
  `transformIdeal x r I m := ⟨{g ∈ R' | ∃ f ∈ I, x_r^m g = φ f}⟩ = {x_r^{-m} φ(f) : f ∈ I} R'`.

The transform of an ideal is defined without the hypothesis `I ≤ P^m`; the hypothesis is where
Kollár defines it and where its properties hold (`Hironaka/Algebra/Local/Transform.lean`).
Uniqueness of the quotient `x_r^{-m} φ(f)` needs no domain hypothesis: `x_r` is a unit of the
ambient ring `R[1/x_r]`, so multiplication by `x_r^m` is injective on `R'`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

/-- The ideal `P = ⟨x₀, …, x_r⟩` of the centre `Z = (x₁ = ⋯ = x_r = 0)` of [Kol07, Definition 60]
(zero-based indices, `r` included). -/
noncomputable def chartCenter : Ideal R := Ideal.span (x '' {i | i ≤ r})

theorem x_mem_chartCenter {i : Fin n} (hi : i ≤ r) : x i ∈ chartCenter x r :=
  Ideal.subset_span ⟨i, hi, rfl⟩

theorem chartCenter_le_iff {I : Ideal R} : chartCenter x r ≤ I ↔ ∀ i, i ≤ r → x i ∈ I := by
  rw [chartCenter, Ideal.span_le, Set.image_subset_iff]
  exact ⟨fun h i hi => h hi, fun h i hi => h i hi⟩

/-- `φ (xᵢ) = x_r · yᵢ` in `R'` for `i < r`. -/
theorem algebraMap_x_eq_mul_chartYR {i : Fin n} (hi : i < r) :
    algebraMap R (chartRing x r) (x i) = algebraMap R (chartRing x r) (x r) * chartYR x r i := by
  apply Subtype.ext
  have hy : ((chartYR x r i : chartRing x r) : Localization.Away (x r)) =
      Localization.mk (x i) ⟨x r, Submonoid.mem_powers _⟩ := by
    rw [coe_chartYROf]
    exact chartYOf_of_lt x r (x r) hi
  rw [Subalgebra.coe_mul, hy, mk_eq_algebraMap_mul_invX, Subalgebra.coe_algebraMap,
    Subalgebra.coe_algebraMap, mul_left_comm, algebraMap_mul_invX, mul_one]

/-- For `i ≤ r`, `φ (xᵢ) ∈ x_r R'`. -/
theorem algebraMap_x_mem_span_of_le {i : Fin n} (hi : i ≤ r) :
    algebraMap R (chartRing x r) (x i) ∈ Ideal.span {algebraMap R (chartRing x r) (x r)} := by
  rcases hi.lt_or_eq with hlt | rfl
  · rw [algebraMap_x_eq_mul_chartYR x r hlt, mul_comm]
    exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
  · exact Ideal.mem_span_singleton_self _

/-- `P ≤ φ⁻¹(x_r R')`. -/
theorem chartCenter_le_comap_span :
    chartCenter x r ≤
      (Ideal.span {algebraMap R (chartRing x r) (x r)}).comap (algebraMap R (chartRing x r)) :=
  (chartCenter_le_iff x r).mpr fun _ hi => Ideal.mem_comap.mpr (algebraMap_x_mem_span_of_le x r hi)

/-- `f ∈ P^m ⟹ φ f ∈ (x_r R')^m`: the pull-back of `(I, m)` with `I ≤ P^m` is divisible by the
`m`-th power of the exceptional divisor [Kol07, Definition 60]. -/
theorem algebraMap_mem_span_pow_of_mem_chartCenter_pow {m : ℕ} {f : R}
    (hf : f ∈ chartCenter x r ^ m) :
    algebraMap R (chartRing x r) f ∈ Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m :=
  Ideal.mem_comap.mp
    (Ideal.le_comap_pow (f := algebraMap R (chartRing x r)) m
      (Ideal.pow_right_mono (chartCenter_le_comap_span x r) m hf))

/-- The quotient `x_r^{-m} φ(f)` exists in `R'`. -/
theorem exists_algebraMap_pow_mul_eq {m : ℕ} {f : R} (hf : f ∈ chartCenter x r ^ m) :
    ∃ g : chartRing x r,
      algebraMap R (chartRing x r) (x r) ^ m * g = algebraMap R (chartRing x r) f := by
  have h := algebraMap_mem_span_pow_of_mem_chartCenter_pow x r hf
  rw [Ideal.span_singleton_pow] at h
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨g, by rw [mul_comm]; exact hg⟩

/-- `P R' = x_r R'`, the ideal of the exceptional divisor `F` of [Kol07, Definition 60] in the
chart. -/
theorem map_chartCenter :
    (chartCenter x r).map (algebraMap R (chartRing x r)) =
      Ideal.span {algebraMap R (chartRing x r) (x r)} := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr (chartCenter_le_comap_span x r)) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.mem_map_of_mem _ (x_mem_chartCenter x r le_rfl)

/-- The transform `x_r^{-m} φ(f)` of a marked element `(f, m)` with `f ∈ P^m` [Kol07,
Definition 60, (60.3)], i.e. `f / x_r^m` in `R[1/x_r]`, which lies in `R'` by
`exists_algebraMap_pow_mul_eq`. -/
noncomputable def transformElem {m : ℕ} (f : R) (hf : f ∈ chartCenter x r ^ m) : chartRing x r :=
  ⟨Localization.mk f ⟨x r ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers _) m⟩, by
    obtain ⟨g, hg⟩ := exists_algebraMap_pow_mul_eq x r hf
    have h : (g : Localization.Away (x r)) =
        Localization.mk f ⟨x r ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers _) m⟩ := by
      rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
      have h' := congrArg (fun z : chartRing x r => (z : Localization.Away (x r))) hg
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at h'
      rw [← h', map_pow, mul_comm]
    rw [← h]
    exact g.2⟩

theorem coe_transformElem {m : ℕ} (f : R) (hf : f ∈ chartCenter x r ^ m) :
    (transformElem x r f hf : Localization.Away (x r)) =
      Localization.mk f ⟨x r ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers _) m⟩ := rfl

/-- The transform of an ideal `I` with mark `m` [Kol07, Definition 60, (60.1) and (60.3)]: the
ideal `{x_r^{-m} φ(f) : f ∈ I} R'` of `R'` generated by the quotients that exist; for `I ≤ P^m`
it is the unique ideal `J` with `x_r^m J = I R'` (`Hironaka/Algebra/Local/Transform.lean`). -/
noncomputable def transformIdeal (I : Ideal R) (m : ℕ) : Ideal (chartRing x r) :=
  Ideal.span {g | ∃ f ∈ I,
    algebraMap R (chartRing x r) (x r) ^ m * g = algebraMap R (chartRing x r) f}

end IsLocalRing
