/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TransformDeriv
public import Hironaka.Algebra.Local.LogDeriv
import Hironaka.Algebra.Local.Transform

/-!
# Birational transform of logarithmic derivatives

The logarithmic version of the derivative computation of
`Hironaka/Algebra/Local/TransformDeriv.lean`, [Kol07, (87.3)]: when the centre of the blow-up lies
in a smooth hypersurface `S` (the hypothesis of [Kol07, Theorem 84]), the logarithmic derivative
ideals satisfy the analogue of [Kol07, Theorem 76], `Π⁻¹_*(D^j(−log S_r)(I, m)) ⊆ D^j(−log
S)(Π⁻¹_*(I, m))`, which Kollár says is "proved the same way using (75.4)".

Setting: `R` a regular local ring containing `ℚ` with coordinates `x₀, …, x_{n−1}`, the chart of
the blow-up of `P = (x₀, …, x_r)` dividing by `x_r`, and `S = V(x_h)` with `h < r` (Kollár's
`x₁ ≠ x_r`), whose birational transform in the chart is `S₁ = V(y_h)`. The module defines the
logarithmic derivative ideal of an ideal `J` of the chart ring along `S₁`, for the transported
derivations `∂'ⱼ`: `D'(−log S₁)(J) = J + y_h ∂'_h(J) R' + ∑_{j ≠ h} ∂'ⱼ(J) R'` (`chartDlog`, the
definition of [Kol07, 87] for the chart ring; the chart ring is not local, so the logarithmic
derivative ideal `Dlog` of `Hironaka/Algebra/Local/LogDeriv.lean` does not apply to it directly),
together with its iterates `chartDlogpow`, and proves for `I ≤ Pᵐ⁺¹`

`π⁻¹_*(D(−log S)(I), m) ≤ D'(−log S₁)(π⁻¹_*(I, m+1))` (`transform_Dlog_le_chartDlog`)

and, by iteration, for `I ≤ Pᵐ⁺ʲ`,
`π⁻¹_*(D^j(−log S)(I), m) ≤ D'^j(−log S₁)(π⁻¹_*(I, m+j))` (`transform_Dlogpow_le_chartDlogpow`).

The proof follows Kollár's indication. On the generators of `D(−log S)(I)`: `f` transforms into
`x_r π⁻¹_*(f, m+1)`; `x_h ∂_h f` into `y_r y_h ∂'_h π⁻¹_*(f, m+1)` by (75.4); `∂ⱼ f` for `j ≠ h, r`
into `∂'ⱼ π⁻¹_*(f, m+1)` or `y_r ∂'ⱼ π⁻¹_*(f, m+1)` by (75.1)–(75.2); and `∂_r f` by (75.3) into a
combination of `y_r ∂'_r`, `y_h ∂'_h` and the `∂'ᵢ` (`i < r`, `i ≠ h`) applied to `π⁻¹_*(f, m+1)`,
plus a multiple of `π⁻¹_*(f, m+1)`, all logarithmic along `S₁`. To check an inclusion
`π⁻¹_*(J, m) ≤ K` on generators of `J`, the set `{g ∈ Pᵐ | π⁻¹_*(g, m) ∈ K}` is shown to be an
ideal of `R` (`transformPreimage`).

Used for the logarithmic derivations of the blow-up (`Hironaka/Algebra/Local/BlowUpLiftLog.lean`,
`Hironaka/Algebra/Local/ChartLogDerivations.lean`), for the inclusion `⊆` of [Kol07, (88.1)]
(`Hironaka/Algebra/Local/TransformDerivNormalForm.lean`), and for Theorem 76 and its logarithmic
version on manifolds (`Hironaka/Manifold/BlowUp/Transform/DerivTransform.lean`,
`Hironaka/Manifold/BlowUp/Transform/LogDerivBlowUp.lean`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n) (r : Fin n)

/-- The logarithmic derivative ideal of an ideal `J` of the chart ring along `S₁ = V(y_h)`, for
the transported derivations `∂'ⱼ`: `J + y_h ∂'_h(J) R' + ∑_{j ≠ h} ∂'ⱼ(J) R'` (the definition of
[Kol07, 87] for the chart ring). -/
noncomputable def chartDlog (h : Fin n) (J : Ideal (chartRing c.x r)) : Ideal (chartRing c.x r) :=
  J ⊔ Ideal.span ((fun z => chartYR c.x r h * c.chartDerivRing r h z) '' J) ⊔
    ⨆ (j : Fin n) (_ : j ≠ h), Ideal.span (c.chartDerivRing r j '' J)

/-- `D'^j(−log S₁)`, the `j`-th iterate of `chartDlog`. -/
noncomputable def chartDlogpow (h : Fin n) (j : ℕ) (J : Ideal (chartRing c.x r)) :
    Ideal (chartRing c.x r) :=
  (c.chartDlog r h)^[j] J

theorem le_chartDlog (h : Fin n) (J : Ideal (chartRing c.x r)) : J ≤ c.chartDlog r h J :=
  le_sup_left.trans le_sup_left

theorem chartYR_mul_chartDerivRing_mem_chartDlog (h : Fin n) {J : Ideal (chartRing c.x r)}
    {z : chartRing c.x r} (hz : z ∈ J) :
    chartYR c.x r h * c.chartDerivRing r h z ∈ c.chartDlog r h J :=
  Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨z, hz, rfl⟩))

theorem chartDerivRing_mem_chartDlog {h j : Fin n} (hj : j ≠ h) {J : Ideal (chartRing c.x r)}
    {z : chartRing c.x r} (hz : z ∈ J) : c.chartDerivRing r j z ∈ c.chartDlog r h J :=
  Ideal.mem_sup_right (Ideal.mem_iSup_of_mem j (Ideal.mem_iSup_of_mem hj
    (Ideal.subset_span ⟨z, hz, rfl⟩)))

/-- The generator description of `D'(−log S₁)(J)`: it lies in `K` if and only if `J`,
`y_h ∂'_h(J)` and the `∂'ⱼ(J)`, `j ≠ h`, do. -/
theorem chartDlog_le_iff (h : Fin n) {J K : Ideal (chartRing c.x r)} :
    c.chartDlog r h J ≤ K ↔
      J ≤ K ∧ (∀ z ∈ J, chartYR c.x r h * c.chartDerivRing r h z ∈ K) ∧
        ∀ j, j ≠ h → ∀ z ∈ J, c.chartDerivRing r j z ∈ K := by
  constructor
  · intro hle
    exact ⟨(c.le_chartDlog r h J).trans hle,
      fun _ hz => hle (c.chartYR_mul_chartDerivRing_mem_chartDlog r h hz),
      fun _ hj _ hz => hle (c.chartDerivRing_mem_chartDlog r hj hz)⟩
  · rintro ⟨h1, h2, h3⟩
    refine sup_le (sup_le h1 (Ideal.span_le.mpr ?_))
      (iSup_le fun j => iSup_le fun hj => Ideal.span_le.mpr ?_)
    · rintro _ ⟨z, hz, rfl⟩
      exact h2 z hz
    · rintro _ ⟨z, hz, rfl⟩
      exact h3 j hj z hz

theorem chartDlog_mono (h : Fin n) {J K : Ideal (chartRing c.x r)} (hJK : J ≤ K) :
    c.chartDlog r h J ≤ c.chartDlog r h K :=
  (c.chartDlog_le_iff r h).mpr ⟨hJK.trans (c.le_chartDlog r h K),
    fun _ hz => c.chartYR_mul_chartDerivRing_mem_chartDlog r h (hJK hz),
    fun _ hj _ hz => c.chartDerivRing_mem_chartDlog r hj (hJK hz)⟩

/-- `D'(−log S₁)(J) ≤ D'(J)`, the derivative ideal of the chart ring for all the `∂'ⱼ`
(`chartD`). -/
theorem chartDlog_le_chartD (h : Fin n) (J : Ideal (chartRing c.x r)) :
    c.chartDlog r h J ≤ c.chartD r J :=
  (c.chartDlog_le_iff r h).mpr ⟨c.le_chartD r J,
    fun _ hz => Ideal.mul_mem_left _ _ (c.chartDerivRing_mem_chartD r hz h),
    fun j _ _ hz => c.chartDerivRing_mem_chartD r hz j⟩

@[simp] theorem chartDlogpow_zero (h : Fin n) (J : Ideal (chartRing c.x r)) :
    c.chartDlogpow r h 0 J = J := rfl

theorem chartDlogpow_succ (h : Fin n) (j : ℕ) (J : Ideal (chartRing c.x r)) :
    c.chartDlogpow r h (j + 1) J = c.chartDlog r h (c.chartDlogpow r h j J) :=
  Function.iterate_succ_apply' _ _ _

theorem chartDlogpow_mono (h : Fin n) (j : ℕ) {J K : Ideal (chartRing c.x r)} (hJK : J ≤ K) :
    c.chartDlogpow r h j J ≤ c.chartDlogpow r h j K := by
  induction j with
  | zero => exact hJK
  | succ j ih => rw [chartDlogpow_succ, chartDlogpow_succ]; exact c.chartDlog_mono r h ih

/-! ### The marks: `D^j(−log S)(I) ≤ D^j(I) ≤ Pᵐ` for `I ≤ Pᵐ⁺ʲ` -/

theorem Dpow_le_chartCenter_pow {I : Ideal R} {m j : ℕ} (hI : I ≤ chartCenter c.x r ^ (m + j)) :
    c.Dpow j I ≤ chartCenter c.x r ^ m := by
  induction j generalizing m with
  | zero => exact hI
  | succ j ih =>
    rw [Dpow_succ]
    exact c.D_le_chartCenter_pow r (ih (by rwa [show m + 1 + j = m + (j + 1) by omega]))

theorem Dlogpow_le_chartCenter_pow (h : Fin n) {I : Ideal R} {m j : ℕ}
    (hI : I ≤ chartCenter c.x r ^ (m + j)) : c.Dlogpow h j I ≤ chartCenter c.x r ^ m :=
  (c.Dlogpow_le_Dpow h j I).trans (c.Dpow_le_chartCenter_pow r hI)

theorem Dlog_le_chartCenter_pow (h : Fin n) {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter c.x r ^ (m + 1)) : c.Dlog h I ≤ chartCenter c.x r ^ m :=
  (c.DlogE_le_D _ I).trans (c.D_le_chartCenter_pow r hI)

/-! ### The transform of the logarithmic derivative ideal -/

/-- `{g ∈ Pᵐ | π⁻¹_*(g, m) ∈ K}` is an ideal of `R`, since transforms are additive and
`R`-linear: the device for checking `π⁻¹_*(J, m) ≤ K` on generators of `J`. -/
def transformPreimage (m : ℕ) (K : Ideal (chartRing c.x r)) : Ideal R where
  carrier := {g | ∃ hg : g ∈ chartCenter c.x r ^ m, transformElem c.x r g hg ∈ K}
  add_mem' {f g} hf hg := by
    obtain ⟨hf, hfK⟩ := hf
    obtain ⟨hg, hgK⟩ := hg
    refine ⟨Ideal.add_mem _ hf hg, ?_⟩
    rw [c.transformElem_add r hf hg]
    exact Ideal.add_mem _ hfK hgK
  zero_mem' := ⟨Ideal.zero_mem _, by rw [c.transformElem_zero r]; exact Ideal.zero_mem _⟩
  smul_mem' a {g} hg := by
    obtain ⟨hg, hgK⟩ := hg
    refine ⟨Submodule.smul_mem _ a hg, ?_⟩
    rw [c.transformElem_smul r a hg]
    exact Ideal.mul_mem_left _ _ hgK

theorem mem_transformPreimage {m : ℕ} {K : Ideal (chartRing c.x r)} {g : R} :
    g ∈ c.transformPreimage r m K ↔
      ∃ hg : g ∈ chartCenter c.x r ^ m, transformElem c.x r g hg ∈ K := Iff.rfl

theorem transformIdeal_le_of_le_transformPreimage {J : Ideal R} {m : ℕ}
    (hJ : J ≤ chartCenter c.x r ^ m) {K : Ideal (chartRing c.x r)}
    (hle : J ≤ c.transformPreimage r m K) : transformIdeal c.x r J m ≤ K := by
  rw [transformIdeal_eq_span_range_transformElem _ _ hJ]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨_, hgK⟩ := (c.mem_transformPreimage r).mp (hle hg)
  exact hgK

/-- **Transform of the logarithmic derivative ideal** ([Kol07, (87.3)] for one blow-up and
`j = 1`, "proved the same way using (75.4)"): for `S = V(x_h)` with `h < r` and `I ≤ Pᵐ⁺¹`,
`π⁻¹_*(D(−log S)(I), m) ≤ D'(−log S₁)(π⁻¹_*(I, m+1))`.  On the generators of `D(−log S)(I)`:
`f ↦ x_r π⁻¹_*(f, m+1)`; `x_h ∂_h f ↦ y_r y_h ∂'_h π⁻¹_*(f, m+1)` by (75.4); `∂ⱼ f`, `j ≠ h`, by
(75.1)–(75.3), where in (75.3) the term `y_h ∂'_h π⁻¹_*(f, m+1)` of the sum is the logarithmic
generator and the other `yᵢ ∂'ᵢ π⁻¹_*(f, m+1)` are multiples of the `∂'ᵢ`, `i ≠ h`. -/
theorem transform_Dlog_le_chartDlog {h : Fin n} (hh : h < r) {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter c.x r ^ (m + 1)) :
    transformIdeal c.x r (c.Dlog h I) m ≤ c.chartDlog r h (transformIdeal c.x r I (m + 1)) := by
  have hT : ∀ (f : R) (hf : f ∈ I),
      transformElem c.x r f (hI hf) ∈ transformIdeal c.x r I (m + 1) := by
    intro f hf
    rw [transformIdeal_eq_span_range_transformElem _ _ hI]
    exact Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  refine c.transformIdeal_le_of_le_transformPreimage r (c.Dlog_le_chartCenter_pow r h hI) ?_
  refine (c.Dlog_le_iff h).mpr ⟨fun f hf => (c.mem_transformPreimage r).mpr
      ⟨Ideal.pow_le_pow_right (Nat.le_succ m) (hI hf), ?_⟩,
    fun f hf => (c.mem_transformPreimage r).mpr
      ⟨Ideal.mul_mem_left _ _ (by simpa using c.pderiv_mem_chartCenter_pow r (hI hf) h), ?_⟩,
    fun j hj f hf => (c.mem_transformPreimage r).mpr
      ⟨by simpa using c.pderiv_mem_chartCenter_pow r (hI hf) j, ?_⟩⟩
  · rw [c.transformElem_succ r (hI hf)]
    exact Ideal.mul_mem_left _ _ (c.le_chartDlog r h _ (hT f hf))
  · rw [c.transform_x_pderiv r hh (hI hf), mul_assoc]
    exact Ideal.mul_mem_left _ _ (c.chartYR_mul_chartDerivRing_mem_chartDlog r h (hT f hf))
  · rcases lt_trichotomy j r with hjr | hjr | hjr
    · rw [c.transform_pderiv_lt r hjr (hI hf)]
      exact c.chartDerivRing_mem_chartDlog r hj (hT f hf)
    · subst hjr
      rw [c.transform_pderiv_eq j (hI hf)]
      refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
      · exact Ideal.mul_mem_left _ _ (c.chartDerivRing_mem_chartDlog j hj (hT f hf))
      · refine Ideal.sum_mem _ fun i _ => ?_
        by_cases hi : i = h
        · rw [hi]
          exact c.chartYR_mul_chartDerivRing_mem_chartDlog j h (hT f hf)
        · exact Ideal.mul_mem_left _ _ (c.chartDerivRing_mem_chartDlog j hi (hT f hf))
      · exact nsmul_mem (c.le_chartDlog j h _ (hT f hf)) _
    · rw [c.transform_pderiv_gt r hjr (hI hf)]
      exact Ideal.mul_mem_left _ _ (c.chartDerivRing_mem_chartDlog r hj (hT f hf))

/-- [Kol07, (87.3)] in the chart, `j`-fold, by iterating `transform_Dlog_le_chartDlog`: for
`I ≤ Pᵐ⁺ʲ`, `π⁻¹_*(D^j(−log S)(I), m) ≤ D'^j(−log S₁)(π⁻¹_*(I, m+j))`. -/
theorem transform_Dlogpow_le_chartDlogpow {h : Fin n} (hh : h < r) {I : Ideal R} {m j : ℕ}
    (hI : I ≤ chartCenter c.x r ^ (m + j)) :
    transformIdeal c.x r (c.Dlogpow h j I) m ≤
      c.chartDlogpow r h j (transformIdeal c.x r I (m + j)) := by
  induction j generalizing m with
  | zero => exact le_rfl
  | succ j ih =>
    have hI' : I ≤ chartCenter c.x r ^ (m + 1 + j) := by
      rwa [show m + 1 + j = m + (j + 1) by omega]
    rw [Dlogpow_succ, chartDlogpow_succ]
    refine (c.transform_Dlog_le_chartDlog r hh (c.Dlogpow_le_chartCenter_pow r h hI')).trans
      (c.chartDlog_mono r h ?_)
    rw [show m + (j + 1) = m + 1 + j by omega]
    exact ih hI'

end RegularCoords

end IsLocalRing
