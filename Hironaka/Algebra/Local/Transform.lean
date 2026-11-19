/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.Order
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Algebra.Local.PowerSeriesRegular
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem

/-!
# The birational transform of a marked ideal in the chart: properties

Kollár defines the birational transform of a marked ideal `(I, m)` with `m ≤ ord_Z I` as
`π⁻¹_*(I, m) = (O(mF) · π^* I, m)`, computed in the chart `yᵢ = xᵢ/x_r` (`i < r`), `y_r = x_r` by
`π⁻¹_*(f, m) = y_r^{-m} f(y₁ y_r, …, y_{r-1} y_r, y_r, …, yₙ)` [Kol07, Definition 60, (60.1) and
(60.3)].  The definitions are in `Hironaka/Algebra/Local/BirationalTransform.lean`; this file proves
their properties: the defining equations and uniqueness, the calculus (products, sums, powers),
the independence of the chosen generator of the exceptional ideal, the codimension-one case,
and the example `π⁻¹_*(x₀² + x₁³, 2) = y₀² + x₁`.

**The one idea.**  `x_r` is a unit of the ambient ring `R[1/x_r]`, so multiplication by `x_r^m`
is injective on the chart ring `R'` (`algebraMap_pow_mul_right_injective`).  Hence the element
`g` with `x_r^m g = φ(f)` is unique (`eq_transformElem_of_pow_mul_eq`) and, for `I ≤ P^m`, the
ideal `J` with `x_r^m J = I R'` is unique (`eq_of_span_pow_mul_eq`); `transformIdeal x r I m` is
that ideal (`span_pow_mul_transformIdeal`: `⊆` because each generator `g` has `x_r^m g ∈ I R'`,
`⊇` because `exists_algebraMap_pow_mul_eq` produces the quotient of every `φ(f)`).  Every
algebraic law then follows from the corresponding law for `I R'` and the uniqueness:
`x_r^{m+m'} (J J') = (x_r^m J)(x_r^{m'} J') = (IR')(I'R') = (II')R'` gives multiplicativity,
`x_r^m (J ⊔ J') = IR' ⊔ I'R'` gives additivity, `x_r^{mc} J^c = (IR')^c` gives powers,
`x_r · R' = P R'` gives `π⁻¹_*(P^m, m) = R'`, and the characterization through `P R' = x_r R'` is
the coordinate independence at the level of ideals.  Kollár's "as we change coordinates, the
result of `π⁻¹_*` changes by a unit" [Kol07, Definition 60] is the elementwise half of the
latter: if `d` is any other generator of `P R'`, then `d = a x_r` with `a` a unit of `R'` (again
by cancellation), and `d^m g = φ(f)` forces `g = a^{-m} · transformElem f`.

**Codimension one.**  For `r = 0` no coordinate is divided: the chart ring is
`Algebra.adjoin R ∅ = ⊥`, the image of `R`, so `φ` is surjective, and bijective when `R` is a
regular local ring with `x` a regular system of parameters (`Hironaka/Algebra/Local/Chart.lean`).
Transporting `x_r^m J = I R'` along the bijection gives `x_r^m · φ⁻¹(J) = I` — Kollár's remark
that for a divisor `Z` "scheme-theoretically there is no change" but the order along `Z` drops
by `m` [Kol07, Definition 60].

**The example.**  For `n = 2`, `r = 1`, `f = x₀² + x₁³`: `x₁² (y₀² + x₁) = (x₁ y₀)² + x₁³ = φ(f)`,
so `π⁻¹_*(f, 2) = y₀² + x₁` by uniqueness.  It lies in `𝔪' = ⟨y₀, x₁⟩`.  That it is not in `𝔪'²`
is seen through the ring map `ψ : R[1/x₁] → Frac(R/⟨x₀⟩)` (as for `1 ∉ 𝔪'` in
`Hironaka/Algebra/Local/Chart.lean`): `R/⟨x₀⟩` is a regular local ring of dimension one with maximal
ideal `⟨x̄₁⟩` (`Hironaka/Algebra/Local/RegularSystem.lean`), so a domain in which `x̄₁ ≠ 0` and
`x̄₁ ∉ 𝔪̄²`; `ψ` kills `y₀ = x₀/x₁`, sends `R'` into `R/⟨x₀⟩` and `𝔪'` into `𝔪̄`, hence `𝔪'²`
into `𝔪̄²`, while `ψ(y₀² + x₁) = x̄₁`.  The order in the local ring `R'_{𝔪'}` is then `1`, because
`𝔪'^k R'_{𝔪'} ∩ R' = 𝔪'^k` (`𝔪'^k` is `𝔪'`-primary, `𝔪'` maximal;
`mem_pow_of_algebraMap_mem_map_pow`).
-/

public section

namespace IsLocalRing

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

/-! ### Cancellation of `x_r` and the defining equations -/

section Basic

/-- `x_r` is a unit of `R[1/x_r]`, so multiplication by `x_r^m` is injective on the chart ring. -/
theorem algebraMap_pow_mul_right_injective (m : ℕ) :
    Function.Injective fun g : chartRing x r => algebraMap R (chartRing x r) (x r) ^ m * g := by
  intro g g' h
  apply Subtype.ext
  have hu : IsUnit (algebraMap R (Localization.Away (x r)) (x r) ^ m) :=
    IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away (x r)) (x r) m
  apply hu.mul_left_cancel
  have h' := congrArg (fun z : chartRing x r => (z : Localization.Away (x r))) h
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using h'

/-- `x_r^m · π⁻¹_*(f, m) = φ(f)` [Kol07, Definition 60, (60.3)]. -/
theorem algebraMap_pow_mul_transformElem {m : ℕ} (f : R) (hf : f ∈ chartCenter x r ^ m) :
    algebraMap R (chartRing x r) (x r) ^ m * transformElem x r f hf =
      algebraMap R (chartRing x r) f := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
    coe_transformElem, Localization.mk_eq_mk', ← map_pow]
  exact IsLocalization.mk'_spec' (S := Localization.Away (x r)) (M := Submonoid.powers (x r)) _ _

/-- Uniqueness of the quotient `π⁻¹_*(f, m)`. -/
theorem eq_transformElem_of_pow_mul_eq {m : ℕ} {f : R} (hf : f ∈ chartCenter x r ^ m)
    {g : chartRing x r}
    (h : algebraMap R (chartRing x r) (x r) ^ m * g = algebraMap R (chartRing x r) f) :
    g = transformElem x r f hf :=
  algebraMap_pow_mul_right_injective x r m
    (h.trans (algebraMap_pow_mul_transformElem x r f hf).symm)

theorem transformElem_mem_transformIdeal {I : Ideal R} {m : ℕ} {f : R} (hfI : f ∈ I)
    (hf : f ∈ chartCenter x r ^ m) : transformElem x r f hf ∈ transformIdeal x r I m :=
  Ideal.subset_span ⟨f, hfI, algebraMap_pow_mul_transformElem x r f hf⟩

/-- For `I ≤ P^m`, `x_r^m · π⁻¹_*(I, m) = I R'` [Kol07, Definition 60, (60.1)]. -/
theorem span_pow_mul_transformIdeal {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) :
    Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m * transformIdeal x r I m =
      I.map (algebraMap R (chartRing x r)) := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_le_iff]
    intro g hg
    refine Submodule.span_induction (p := fun g _ =>
      algebraMap R (chartRing x r) (x r) ^ m * g ∈ I.map (algebraMap R (chartRing x r)))
      ?_ ?_ ?_ ?_ hg
    · rintro g ⟨f, hf, hfg⟩
      rw [hfg]
      exact Ideal.mem_map_of_mem _ hf
    · rw [mul_zero]
      exact zero_mem _
    · intro a b _ _ ha hb
      rw [mul_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ ha
  · refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
    rw [Ideal.mem_comap, ← algebraMap_pow_mul_transformElem x r f (hI hf)]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m)
      (transformElem_mem_transformIdeal x r hf (hI hf))

/-- Cancellation of `x_r^m` for ideals of the chart ring. -/
theorem eq_of_span_pow_mul_eq {m : ℕ} {J J' : Ideal (chartRing x r)}
    (h : Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m * J =
      Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m * J') : J = J' := by
  have key : ∀ {J J' : Ideal (chartRing x r)},
      Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m * J ≤
        Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m * J' → J ≤ J' := by
    intro J J' hle g hg
    have hmem :=
      hle (Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m) hg)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rw [← algebraMap_pow_mul_right_injective x r m hgg']
    exact hg'
  exact le_antisymm (key h.le) (key h.ge)

/-- For `I ≤ P^m`, `π⁻¹_*(I, m)` is the unique ideal `J` with `x_r^m J = I R'`. -/
theorem eq_transformIdeal_of_span_pow_mul_eq {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m)
    {J : Ideal (chartRing x r)}
    (hJ : Ideal.span {algebraMap R (chartRing x r) (x r)} ^ m * J =
      I.map (algebraMap R (chartRing x r))) : J = transformIdeal x r I m :=
  eq_of_span_pow_mul_eq x r (hJ.trans (span_pow_mul_transformIdeal x r hI).symm)

/-- `π⁻¹_*(I, m) = {x_r^{-m} φ(f) : f ∈ I} R'`. -/
theorem transformIdeal_eq_span_range_transformElem {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter x r ^ m) :
    transformIdeal x r I m = Ideal.span (Set.range fun f : I => transformElem x r f (hI f.2)) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro g ⟨f, hf, hfg⟩
    exact Ideal.subset_span ⟨⟨f, hf⟩, (eq_transformElem_of_pow_mul_eq x r (hI hf) hfg).symm⟩
  · rintro g ⟨⟨f, hf⟩, rfl⟩
    exact Ideal.subset_span ⟨f, hf, algebraMap_pow_mul_transformElem x r f (hI hf)⟩

end Basic

/-! ### The calculus of the transform -/

section Calculus

/-- `π⁻¹_*((f, m)(g, m')) = π⁻¹_*(f, m) π⁻¹_*(g, m')`. -/
theorem transformElem_mul {m m' : ℕ} {f g : R} (hf : f ∈ chartCenter x r ^ m)
    (hg : g ∈ chartCenter x r ^ m') (hfg : f * g ∈ chartCenter x r ^ (m + m')) :
    transformElem x r (f * g) hfg = transformElem x r f hf * transformElem x r g hg := by
  symm
  apply eq_transformElem_of_pow_mul_eq
  rw [pow_add, mul_mul_mul_comm, algebraMap_pow_mul_transformElem,
    algebraMap_pow_mul_transformElem, map_mul]

theorem mul_le_chartCenter_pow_add {I J : Ideal R} {m m' : ℕ} (hI : I ≤ chartCenter x r ^ m)
    (hJ : J ≤ chartCenter x r ^ m') : I * J ≤ chartCenter x r ^ (m + m') := by
  rw [pow_add]
  exact Ideal.mul_mono hI hJ

/-- `π⁻¹_*(IJ, m + m') = π⁻¹_*(I, m) π⁻¹_*(J, m')` (used silently in the proof of
[Kol07, Theorem 100]). -/
theorem transformIdeal_mul {I J : Ideal R} {m m' : ℕ} (hI : I ≤ chartCenter x r ^ m)
    (hJ : J ≤ chartCenter x r ^ m') :
    transformIdeal x r (I * J) (m + m') = transformIdeal x r I m * transformIdeal x r J m' := by
  symm
  apply eq_transformIdeal_of_span_pow_mul_eq x r (mul_le_chartCenter_pow_add x r hI hJ)
  rw [pow_add, mul_mul_mul_comm, span_pow_mul_transformIdeal x r hI,
    span_pow_mul_transformIdeal x r hJ, Ideal.map_mul]

/-- `π⁻¹_*(I + J, m) = π⁻¹_*(I, m) + π⁻¹_*(J, m)` (used silently in the proof of
[Kol07, Theorem 100]). -/
theorem transformIdeal_sup {I J : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m)
    (hJ : J ≤ chartCenter x r ^ m) :
    transformIdeal x r (I ⊔ J) m = transformIdeal x r I m ⊔ transformIdeal x r J m := by
  symm
  apply eq_transformIdeal_of_span_pow_mul_eq x r (sup_le hI hJ)
  rw [Ideal.mul_sup, span_pow_mul_transformIdeal x r hI, span_pow_mul_transformIdeal x r hJ,
    Ideal.map_sup]

/-- Monotonicity of the transform in the ideal. -/
theorem transformIdeal_mono {I J : Ideal R} {m : ℕ} (h : I ≤ J) :
    transformIdeal x r I m ≤ transformIdeal x r J m :=
  Ideal.span_mono fun _ ⟨f, hf, hfg⟩ => ⟨f, h hf, hfg⟩

/-- Additivity for arbitrary sums. -/
theorem transformIdeal_iSup {ι : Sort*} {I : ι → Ideal R} {m : ℕ}
    (hI : ∀ i, I i ≤ chartCenter x r ^ m) :
    transformIdeal x r (⨆ i, I i) m = ⨆ i, transformIdeal x r (I i) m := by
  symm
  apply eq_transformIdeal_of_span_pow_mul_eq x r (iSup_le hI)
  rw [Ideal.mul_iSup, Ideal.map_iSup]
  exact iSup_congr fun i => span_pow_mul_transformIdeal x r (hI i)

theorem pow_le_chartCenter_pow_mul {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) (c : ℕ) :
    I ^ c ≤ chartCenter x r ^ (m * c) := by
  rw [pow_mul]
  exact Ideal.pow_right_mono hI c

/-- `π⁻¹_*(I^c, mc) = π⁻¹_*(I, m)^c` (used silently in the proof of [Kol07, Theorem 100]). -/
theorem transformIdeal_pow {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) (c : ℕ) :
    transformIdeal x r (I ^ c) (m * c) = transformIdeal x r I m ^ c := by
  symm
  apply eq_transformIdeal_of_span_pow_mul_eq x r (pow_le_chartCenter_pow_mul x r hI c)
  rw [pow_mul, ← mul_pow, span_pow_mul_transformIdeal x r hI, Ideal.map_pow]

/-- `π⁻¹_*(P, 1) = R'`: the transform of the ideal of the centre is the unit ideal. -/
theorem transformIdeal_chartCenter : transformIdeal x r (chartCenter x r) 1 = ⊤ := by
  symm
  have hI : chartCenter x r ≤ chartCenter x r ^ 1 := by rw [pow_one]
  apply eq_transformIdeal_of_span_pow_mul_eq x r hI
  rw [pow_one, Ideal.mul_top, map_chartCenter]

/-- `π⁻¹_*(P^m, m) = R'`. -/
theorem transformIdeal_chartCenter_pow (m : ℕ) :
    transformIdeal x r (chartCenter x r ^ m) m = ⊤ := by
  symm
  apply eq_transformIdeal_of_span_pow_mul_eq x r le_rfl
  rw [Ideal.mul_top, Ideal.map_pow, map_chartCenter]

end Calculus

/-! ### Coordinate independence -/

section Independence

/-- `π⁻¹_*(I, m)` is the unique ideal `J` with `(P R')^m J = I R'`: the characterization
independent of the chosen generator of the exceptional ideal. -/
theorem eq_transformIdeal_of_map_chartCenter_pow_mul_eq {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter x r ^ m) {J : Ideal (chartRing x r)}
    (hJ : ((chartCenter x r).map (algebraMap R (chartRing x r))) ^ m * J =
      I.map (algebraMap R (chartRing x r))) :
    J = transformIdeal x r I m :=
  eq_transformIdeal_of_span_pow_mul_eq x r hI (by rwa [map_chartCenter] at hJ)

/-- Dividing by another generator of `P R'` changes `π⁻¹_*(f, m)` by a unit of `R'` (Kollár's "as
we change coordinates, the result of `π⁻¹_*` changes by a unit", [Kol07, Definition 60]). -/
theorem exists_unit_mul_transformElem {m : ℕ} {f : R} (hf : f ∈ chartCenter x r ^ m)
    {d : chartRing x r} (hd : Ideal.span {d} = Ideal.span {algebraMap R (chartRing x r) (x r)})
    {g : chartRing x r} (h : d ^ m * g = algebraMap R (chartRing x r) f) :
    ∃ v : (chartRing x r)ˣ, g = v * transformElem x r f hf := by
  have h1 : d ∈ Ideal.span {algebraMap R (chartRing x r) (x r)} :=
    hd ▸ Ideal.mem_span_singleton_self d
  have h2 : algebraMap R (chartRing x r) (x r) ∈ Ideal.span {d} :=
    hd.symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h2
  have hba : b * a = 1 := by
    apply algebraMap_pow_mul_right_injective x r 1
    have : algebraMap R (chartRing x r) (x r) * (b * a) = algebraMap R (chartRing x r) (x r) := by
      calc algebraMap R (chartRing x r) (x r) * (b * a)
          = b * (a * algebraMap R (chartRing x r) (x r)) := by ring
        _ = b * d := by rw [ha]
        _ = algebraMap R (chartRing x r) (x r) := hb
    change algebraMap R (chartRing x r) (x r) ^ 1 * (b * a) =
      algebraMap R (chartRing x r) (x r) ^ 1 * 1
    rw [pow_one, mul_one, this]
  have hab : a * b = 1 := by rw [mul_comm]; exact hba
  let v : (chartRing x r)ˣ := ⟨a, b, hab, hba⟩
  have hT : a ^ m * g = transformElem x r f hf := by
    apply eq_transformElem_of_pow_mul_eq
    rw [← mul_assoc, ← mul_pow, mul_comm (algebraMap R (chartRing x r) (x r)) a, ha]
    exact h
  refine ⟨v⁻¹ ^ m, ?_⟩
  rw [Units.val_pow_eq_pow_val]
  change g = b ^ m * transformElem x r f hf
  rw [← hT, ← mul_assoc, ← mul_pow, hba, one_pow, one_mul]

/-- `z / d ∈ chartRingOf x r d` for `z ∈ P` and `d = x_r`. -/
theorem mk_mem_chartRingOf_of_mem_chartCenter (d : R) (hd : d = x r) {z : R}
    (hz : z ∈ chartCenter x r) :
    Localization.mk z ⟨d, Submonoid.mem_powers d⟩ ∈ chartRingOf x r d := by
  refine Submodule.span_induction
    (p := fun z _ => Localization.mk z ⟨d, Submonoid.mem_powers d⟩ ∈ chartRingOf x r d)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, hi, rfl⟩
    rcases (show i ≤ r from hi).lt_or_eq with hlt | rfl
    · exact Algebra.subset_adjoin ⟨i, hlt, rfl⟩
    · subst hd
      have : Localization.mk (x i) ⟨x i, Submonoid.mem_powers (x i)⟩ =
          (1 : Localization.Away (x i)) := Localization.mk_self ⟨x i, Submonoid.mem_powers (x i)⟩
      rw [this]
      exact one_mem _
  · rw [Localization.mk_zero]
    exact zero_mem _
  · intro a b _ _ ha hb
    rw [← Localization.add_mk_self]
    exact add_mem ha hb
  · intro c a _ ha
    have : Localization.mk (c • a) ⟨d, Submonoid.mem_powers d⟩ =
        algebraMap R (Localization.Away d) c * Localization.mk a ⟨d, Submonoid.mem_powers d⟩ := by
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, smul_eq_mul]
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) ha

/-- Another family with the same centre and the same dividing element has the same chart ring. -/
theorem chartRingOf_eq_of_chartCenter_eq (x' : Fin n → R) (hr : x' r = x r)
    (hP : chartCenter x' r = chartCenter x r) : chartRingOf x' r (x r) = chartRing x r := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, hi, rfl⟩
    exact mk_mem_chartRingOf_of_mem_chartCenter x r (x r) rfl
      (hP ▸ x_mem_chartCenter x' r (le_of_lt hi))
  · apply Algebra.adjoin_le
    rintro _ ⟨i, hi, rfl⟩
    exact mk_mem_chartRingOf_of_mem_chartCenter x' r (x r) hr.symm
      (hP.symm ▸ x_mem_chartCenter x r (le_of_lt hi))

end Independence

/-! ### Codimension-one centre -/

section CodimOne

/-- For `r = 0` the centre is `⟨x_r⟩` (the divisorial case of [Kol07, Definition 60]). -/
theorem chartCenter_eq_span_singleton_of_val_eq_zero (hr : (r : ℕ) = 0) :
    chartCenter x r = Ideal.span {x r} := by
  have hset : {i : Fin n | i ≤ r} = {r} := by
    ext i
    constructor
    · intro h
      have h' : i ≤ r := h
      exact Fin.ext (by have := Fin.le_def.mp h'; omega)
    · intro h
      rw [Set.mem_singleton_iff] at h
      rw [h]
      exact (le_rfl : r ≤ r)
  rw [chartCenter, hset, Set.image_singleton]

/-- For `r = 0` the chart ring is the image of `R`. -/
theorem chartRing_eq_bot_of_val_eq_zero (hr : (r : ℕ) = 0) : chartRing x r = ⊥ := by
  have hset : {i : Fin n | i < r} = ∅ := by
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro h
    have h' : i < r := h
    have := Fin.lt_def.mp h'
    omega
  change chartRingOf x r (x r) = ⊥
  rw [chartRingOf, hset, Set.image_empty, Algebra.adjoin_empty]

variable [IsRegularLocalRing R]

/-- For `r = 0`, `φ : R → R'` is bijective ("`B_Z X ≅ X`", [Kol07, Definition 60]). -/
theorem algebraMap_chartRing_bijective_of_val_eq_zero
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    (hr : (r : ℕ) = 0) : Function.Bijective (algebraMap R (chartRing x r)) := by
  refine ⟨algebraMap_chartRing_injective x r hx hn, fun g => ?_⟩
  have hg : (g : Localization.Away (x r)) ∈ (⊥ : Subalgebra R (Localization.Away (x r))) := by
    rw [← chartRing_eq_bot_of_val_eq_zero x r hr]
    exact g.2
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hg
  exact ⟨a, Subtype.ext (by rw [Subalgebra.coe_algebraMap]; exact ha)⟩

/-- For `r = 0`, `x_r^m · φ⁻¹(π⁻¹_*(I, m)) = I` ("`π⁻¹_*(I, m) = x_r^{-m} I`": the order along a
divisorial centre drops by `m`, [Kol07, Definition 60]). -/
theorem span_pow_mul_comap_transformIdeal_of_val_eq_zero
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    (hr : (r : ℕ) = 0) {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) :
    Ideal.span {x r ^ m} * (transformIdeal x r I m).comap (algebraMap R (chartRing x r)) =
      I := by
  have hbij := algebraMap_chartRing_bijective_of_val_eq_zero x r hx hn hr
  have hcm : ∀ K : Ideal R,
      (K.map (algebraMap R (chartRing x r))).comap (algebraMap R (chartRing x r)) = K := by
    intro K
    rw [Ideal.comap_map_of_surjective _ hbij.2, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hbij.1, sup_bot_eq]
  have hkey : (Ideal.span {x r ^ m} *
      (transformIdeal x r I m).comap (algebraMap R (chartRing x r))).map
        (algebraMap R (chartRing x r)) = I.map (algebraMap R (chartRing x r)) := by
    rw [Ideal.map_mul, Ideal.map_comap_of_surjective _ hbij.2, Ideal.map_span,
      Set.image_singleton, map_pow, ← Ideal.span_singleton_pow, span_pow_mul_transformIdeal x r hI]
  rw [← hcm (Ideal.span {x r ^ m} * _), hkey, hcm]

end CodimOne

/-! ### The example `π⁻¹_*(x₀² + x₁³, 2) = y₀² + x₁` -/

section

variable (x : Fin 2 → R)

/-- `x₀² + x₁³ ∈ P²`. -/
theorem sq_add_cube_mem_chartCenter_sq : x 0 ^ 2 + x 1 ^ 3 ∈ chartCenter x 1 ^ 2 := by
  refine Ideal.add_mem _ (Ideal.pow_mem_pow (x_mem_chartCenter x 1 (by decide)) 2) ?_
  rw [show x 1 ^ 3 = x 1 ^ 2 * x 1 from pow_succ (x 1) 2]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (x_mem_chartCenter x 1 le_rfl) 2)

/-- `π⁻¹_*(x₀² + x₁³, 2) = y₀² + x₁`. -/
theorem transformElem_sq_add_cube (hf : x 0 ^ 2 + x 1 ^ 3 ∈ chartCenter x 1 ^ 2) :
    transformElem x 1 (x 0 ^ 2 + x 1 ^ 3) hf =
      chartYR x 1 0 ^ 2 + algebraMap R (chartRing x 1) (x 1) := by
  symm
  apply eq_transformElem_of_pow_mul_eq
  rw [map_add, map_pow, map_pow, algebraMap_x_eq_mul_chartYR x 1 (show (0 : Fin 2) < 1 by decide)]
  ring

end

/-! ### Contraction of powers of a maximal ideal from the localization -/

/-- For `P` maximal, `P^k R_P ∩ R = P^k` (`P^k` is `P`-primary). -/
theorem mem_pow_of_algebraMap_mem_map_pow {A : Type*} [CommRing A] (P : Ideal A)
    [hP : P.IsMaximal] {k : ℕ} (hk : k ≠ 0) {a : A}
    (h : algebraMap A (Localization.AtPrime P) a ∈
      (P ^ k).map (algebraMap A (Localization.AtPrime P))) : a ∈ P ^ k := by
  rw [IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)] at h
  obtain ⟨⟨b, s⟩, hbs⟩ := h
  dsimp only at hbs
  rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)] at hbs
  obtain ⟨t, ht⟩ := hbs
  have hprim : (P ^ k).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by
    rw [Ideal.radical_pow P hk, hP.isPrime.radical]
    exact hP)
  have hmem : ((t : A) * s) • a ∈ P ^ k := by
    rw [smul_eq_mul, show (t : A) * s * a = t * (a * s) by ring, ht]
    exact Ideal.mul_mem_left _ _ b.2
  rcases hprim.2 hmem with h1 | ⟨q, hq⟩
  · exact h1
  · exfalso
    have hts : (t : A) * s ∈ P.primeCompl := P.primeCompl.mul_mem t.2 s.2
    have hpow : ((t : A) * s) ^ q ∈ P ^ k := by
      have := hq (Submodule.smul_mem_pointwise_smul (1 : A) (((t : A) * s) ^ q) ⊤ Submodule.mem_top)
      rwa [smul_eq_mul, mul_one] at this
    exact hts (hP.isPrime.mem_of_pow_mem q (Ideal.pow_le_self hk hpow))

/-! ### The order of the transform at the origin of the chart, in the example -/

section

variable [IsRegularLocalRing R] (x : Fin 2 → R)

/-- The key point of the example: `y₀² + x₁ ∉ 𝔪'²`.  Proof: the ring map
`ψ : R[1/x₁] → Frac(R/⟨x₀⟩)` kills `y₀`, maps `R'` into `R/⟨x₀⟩` and `𝔪'` into its maximal ideal
`𝔪̄`, hence `𝔪'²` into `𝔪̄²`; but `ψ(y₀² + x₁) = x̄₁ ∉ 𝔪̄²`, since `R/⟨x₀⟩` is regular of
dimension one with `x̄₁` a regular system of parameters
(`Hironaka/Algebra/Local/RegularSystem.lean`). -/
theorem transformElem_sq_add_cube_notMem_chartOrigin_sq
    (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : ((2 : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    (hf : x 0 ^ 2 + x 1 ^ 3 ∈ chartCenter x 1 ^ 2) :
    transformElem x 1 (x 0 ^ 2 + x 1 ^ 3) hf ∉ chartOrigin x 1 ^ 2 := by
  classical
  intro hT
  set Q : Ideal R := Ideal.span (x '' {j : Fin 2 | j.val < 1}) with hQ
  have hreg : IsRegularLocalRing (R ⧸ Q) := isRegularLocalRing_quotient_span_image_lt x hx hn 1
  have hdim : ringKrullDim (R ⧸ Q) + ((1 : ℕ) : WithBot ℕ∞) = ringKrullDim R :=
    ringKrullDim_quotient_span_image_lt x hx hn (i := 1) (by norm_num)
  have hx1 : Ideal.Quotient.mk Q (x 1) ∉ maximalIdeal (R ⧸ Q) ^ 2 :=
    mk_notMem_maximalIdeal_sq_of x hx hn (i := 1) (by norm_num) hdim
  have hprime : Q.IsPrime := isPrime_span_image_lt x hx hn 1
  set S := R ⧸ Q with hSdef
  let F := FractionRing S
  let g : R →+* F := (algebraMap S F).comp (Ideal.Quotient.mk Q)
  have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hg : IsUnit (g (x 1)) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hx1
    have : Ideal.Quotient.mk Q (x 1) = 0 := hinj (by rw [map_zero]; exact h0)
    rw [this]
    exact zero_mem _
  let ψ : Localization.Away (x 1) →+* F := IsLocalization.Away.lift (x 1) hg
  have hψ : ∀ a, ψ (algebraMap R _ a) = g a := fun a => IsLocalization.Away.lift_eq (x 1) hg a
  have hx0Q : x 0 ∈ Q := Ideal.subset_span ⟨0, show (0 : Fin 2).val < 1 by decide, rfl⟩
  have hψy : ψ (chartY x 1 0) = 0 := by
    rw [chartY_of_lt x 1 (show (0 : Fin 2) < 1 by decide), map_mul, hψ]
    have : g (x 0) = 0 := by
      change algebraMap S F (Ideal.Quotient.mk Q (x 0)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx0Q, map_zero]
    rw [this, zero_mul]
  have hmk : ∀ i, Ideal.Quotient.mk Q (x i) ∈ maximalIdeal S := fun i => by
    rw [maximalIdeal_quotient_eq_map]
    exact Ideal.mem_map_of_mem _ (x_mem_maximalIdeal_of_span_eq x hx i)
  have hy : ∀ i, ψ (chartY x 1 i) ∈ algebraMap S F '' (maximalIdeal S : Set S) := by
    intro i
    by_cases hi : i < 1
    · have h0 : i = 0 := Fin.ext (by have := Fin.lt_def.mp hi; omega)
      subst h0
      rw [hψy]
      exact ⟨0, zero_mem _, map_zero _⟩
    · rw [chartY_eq_algebraMap_of_not_lt x 1 hi, hψ]
      exact ⟨Ideal.Quotient.mk Q (x i), hmk i, rfl⟩
  have hR' : ∀ z ∈ chartRing x 1, ψ z ∈ Set.range (algebraMap S F) := by
    intro z hz
    refine Algebra.adjoin_induction (p := fun z _ => ψ z ∈ Set.range (algebraMap S F))
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, hi, rfl⟩
      have hi' : i < 1 := hi
      obtain ⟨s, -, hs⟩ := hy i
      rw [chartY_eq_mk_of_lt x 1 hi'] at hs
      exact ⟨s, hs⟩
    · intro a
      exact ⟨Ideal.Quotient.mk Q a, (hψ a).symm⟩
    · rintro z w _ _ ⟨s, hs⟩ ⟨t, ht⟩
      exact ⟨s + t, by rw [map_add, map_add, hs, ht]⟩
    · rintro z w _ _ ⟨s, hs⟩ ⟨t, ht⟩
      exact ⟨s * t, by rw [map_mul, map_mul, hs, ht]⟩
  have hM : ∀ z ∈ chartOrigin x 1,
      ψ (z : Localization.Away (x 1)) ∈ algebraMap S F '' (maximalIdeal S : Set S) := by
    intro z hz
    refine Submodule.span_induction
      (p := fun (z : chartRing x 1) _ =>
        ψ (z : Localization.Away (x 1)) ∈ algebraMap S F '' (maximalIdeal S : Set S))
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      exact hy i
    · exact ⟨0, zero_mem _, by rw [Subalgebra.coe_zero, map_zero, map_zero]⟩
    · rintro z w _ _ ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
      exact ⟨s + t, add_mem hs ht, by rw [map_add, Subalgebra.coe_add, map_add, hs', ht']⟩
    · rintro b z _ ⟨s, hs, hs'⟩
      obtain ⟨t, ht⟩ := hR' b b.2
      exact ⟨t * s, Ideal.mul_mem_left _ _ hs,
        by rw [map_mul, smul_eq_mul, Subalgebra.coe_mul, map_mul, ht, hs']⟩
  have hM2 : ∀ z ∈ chartOrigin x 1 ^ 2, ψ (z : Localization.Away (x 1)) ∈
      algebraMap S F '' ((maximalIdeal S ^ 2 : Ideal S) : Set S) := by
    intro z hz
    rw [sq] at hz
    refine Submodule.mul_induction_on
      (C := fun (z : chartRing x 1) => ψ (z : Localization.Away (x 1)) ∈
        algebraMap S F '' ((maximalIdeal S ^ 2 : Ideal S) : Set S))
      hz ?_ ?_
    · intro a ha b hb
      obtain ⟨s, hs, hs'⟩ := hM a ha
      obtain ⟨t, ht, ht'⟩ := hM b hb
      exact ⟨s * t, by rw [sq]; exact Ideal.mul_mem_mul hs ht,
        by rw [Subalgebra.coe_mul, map_mul, map_mul, hs', ht']⟩
    · rintro a b ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
      exact ⟨s + t, add_mem hs ht, by rw [Subalgebra.coe_add, map_add, map_add, hs', ht']⟩
  have hTψ : ψ (transformElem x 1 (x 0 ^ 2 + x 1 ^ 3) hf : Localization.Away (x 1)) =
      algebraMap S F (Ideal.Quotient.mk Q (x 1)) := by
    rw [transformElem_sq_add_cube x hf, Subalgebra.coe_add, Subalgebra.coe_pow,
      Subalgebra.coe_algebraMap, map_add, map_pow, hψ,
      show ((chartYR x 1 0 : chartRing x 1) : Localization.Away (x 1)) = chartY x 1 0 from rfl,
      hψy, zero_pow two_ne_zero, zero_add]
    rfl
  obtain ⟨s, hs, hs'⟩ := hM2 _ hT
  rw [hTψ] at hs'
  exact hx1 (hinj hs' ▸ hs)

/-- `y₀² + x₁ ∈ 𝔪' ∖ 𝔪'²`. -/
theorem transformElem_sq_add_cube_mem_chartOrigin (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : ((2 : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    (hf : x 0 ^ 2 + x 1 ^ 3 ∈ chartCenter x 1 ^ 2) :
    transformElem x 1 (x 0 ^ 2 + x 1 ^ 3) hf ∈ chartOrigin x 1 ∧
      transformElem x 1 (x 0 ^ 2 + x 1 ^ 3) hf ∉ chartOrigin x 1 ^ 2 := by
  refine ⟨?_, transformElem_sq_add_cube_notMem_chartOrigin_sq x hx hn hf⟩
  rw [transformElem_sq_add_cube x hf, sq]
  exact add_mem (Ideal.mul_mem_left _ _ (chartYROf_mem_chartOriginOf x 1 (x 1) 0))
    (algebraMap_x_mem_chartOrigin x 1 1)

/-- The transform `y₀² + x₁` has order `1` at the origin of the chart. -/
theorem ordElem_transformElem_sq_add_cube (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : ((2 : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    (hf : x 0 ^ 2 + x 1 ^ 3 ∈ chartCenter x 1 ^ 2) [(chartOrigin x 1).IsPrime] :
    ordElem (algebraMap (chartRing x 1) (Localization.AtPrime (chartOrigin x 1))
      (transformElem x 1 (x 0 ^ 2 + x 1 ^ 3) hf)) = 1 := by
  obtain ⟨hmem, hnot⟩ := transformElem_sq_add_cube_mem_chartOrigin x hx hn hf
  have hmax : (chartOrigin x 1).IsMaximal := chartOrigin_isMaximal x 1 hx hn
  rw [ordElem_eq_one_iff, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  exact ⟨Ideal.mem_map_of_mem _ hmem,
    fun h => hnot (mem_pow_of_algebraMap_mem_map_pow (chartOrigin x 1) two_ne_zero h)⟩

end

section PowerSeries

/-- The coordinate family `X₀, X₁` of `ℚ⟦x₀, x₁⟧`. -/
local notation "Xq" => (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) ℚ)

/-- In `ℚ⟦x₀, x₁⟧`, `π⁻¹_*(x₀² + x₁³, 2) = y₀² + x₁`. -/
theorem transformElem_X_sq_add_X_cube (hf : Xq 0 ^ 2 + Xq 1 ^ 3 ∈ chartCenter Xq 1 ^ 2) :
    transformElem Xq 1 (Xq 0 ^ 2 + Xq 1 ^ 3) hf =
      chartYR Xq 1 0 ^ 2 + algebraMap (MvPowerSeries (Fin 2) ℚ) (chartRing Xq 1) (Xq 1) :=
  transformElem_sq_add_cube Xq hf

instance chartOrigin_X_one_isPrime : (chartOrigin Xq 1).IsPrime :=
  (chartOrigin_isMaximal Xq 1 (MvPowerSeries.maximalIdeal_eq_span_range_X (Fin 2) ℚ)
    (ringKrullDim_mvPowerSeries ℚ 2).symm).isPrime

/-- In `ℚ⟦x₀, x₁⟧` the transform has order `1` at the origin of the chart. -/
theorem ordElem_transformElem_X_sq_add_X_cube (hf : Xq 0 ^ 2 + Xq 1 ^ 3 ∈ chartCenter Xq 1 ^ 2) :
    ordElem (algebraMap (chartRing Xq 1) (Localization.AtPrime (chartOrigin Xq 1))
      (transformElem Xq 1 (Xq 0 ^ 2 + Xq 1 ^ 3) hf)) = 1 :=
  ordElem_transformElem_sq_add_cube Xq (MvPowerSeries.maximalIdeal_eq_span_range_X (Fin 2) ℚ)
    (ringKrullDim_mvPowerSeries ℚ 2).symm hf

end PowerSeries

end IsLocalRing
