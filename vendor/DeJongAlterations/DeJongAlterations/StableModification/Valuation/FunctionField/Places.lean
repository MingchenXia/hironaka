import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.RingTheory.Valuation.LocalSubring


/-!
# Places of a function field of one variable

Let `E` be a field and `F/E` a *function field of one variable*: a finitely generated field
extension of transcendence degree one (`IsFunctionFieldOneVar E F`). A *place* of `F/E` is a
valuation subring `O` of `F` with `E ⊆ O ≠ F` (`IsPlace E O`). This file develops the elementary
theory of places used by Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), §6.2 (`semi-stable.tex`, Proposition 6.2.5 and Lemma 6.2.6, lines 3754–3815), where
`F` is the residue field of a finite extension of a type-2 analytic field over the algebraically
closed residue field `E = k̃`. The proofs are elementary: no Dedekind domains, normal models or
separability are used.

## Main results

* `IsFunctionFieldOneVar.finiteDimensional_adjoin`: `F/E(t)` is finite for every transcendental
  `t`; `IsFunctionFieldOneVar.of_finiteDimensional_adjoin` is the converse criterion, and
  `IsFunctionFieldOneVar.ratFunc`, `IsFunctionFieldOneVar.of_functionField` cover `E(X)` and
  Mathlib's `FunctionField`.
* `exists_forall_valuation_eq_zpow`, `exists_valuation_sub_lt_one_of_mem_adjoin`: the shape of
  `E(s)` at a valuation ring containing `E` with `|s| < 1`.
* `linearIndependent_of_valuation_ne`, `linearIndependent_of_residue`: elements with pairwise
  incongruent values modulo `|s| ^ ℤ`, or with `E`-independent residues, are `E(s)`-independent.
* `pow_finrank_le`: the **pole bound** `|x| ^ [F : E(s)] ≤ |s|` for `x` in the maximal ideal.
* `IsPlace.isDiscreteValuationRing`: **every place is a discrete valuation ring**;
  `IsPlace.exists_uniformizer` gives the normalized valuation.
* `IsPlace.exists_aeval_valuation_lt_one`: residue fields are algebraic over `E`;
  `IsPlace.exists_valuation_sub_algebraMap_lt_one`, `IsPlace.residue_surjective`: if `E` is
  algebraically closed, the residue field of every place is `E`.
* `IsPlace.eq_of_le`: places are incomparable.
* `exists_valuation_sub_one_lt_one`: an approximation lemma for finitely many incomparable
  valuation rings.
* `card_le_finrank`, `finite_setOf_valuation_lt_one`, `finite_setOf_notMem`: at most
  `[F : E(s)]` places contain `s` in their maximal ideal; every element has finitely many poles.
* `IsPlace.mem_of_isAlgebraic`, `exists_isPlace_notMem`, `forall_isPlace_mem_iff`: an element
  lies in every place if and only if it is algebraic over `E`.

## Implementation notes

Valuations are written multiplicatively, through `ValuationSubring.valuation`, so that `x ∈ O`
if and only if `O.valuation x ≤ 1`. Lemmas that only need `E ⊆ O` take the hypothesis
`hE : ∀ c : E, algebraMap E F c ∈ O` rather than `IsPlace E O`. The blueprint chapter is
`blueprint/src/sm-val-funfield.tex` (plan nodes F1, F2 of `PLAN-SM-VAL`).
-/

noncomputable section

open scoped IntermediateField
open Polynomial

namespace DeJongAlterations.StableModification.Valuation.FunctionField

variable (E F : Type*) [Field E] [Field F] [Algebra E F]

/-- `F` is a *function field of one variable* over `E`: `F` is finitely generated over `E` as a
field (equivalently, essentially of finite type) and has transcendence degree one. -/
structure IsFunctionFieldOneVar : Prop where
  essFiniteType : Algebra.EssFiniteType E F
  trdeg_eq_one : Algebra.trdeg E F = 1

variable {E F}

variable (E) in
/-- A *place* of `F/E`: a valuation subring of `F` containing (the image of) `E`, different
from `F`. -/
structure IsPlace (O : ValuationSubring F) : Prop where
  algebraMap_mem : ∀ c : E, algebraMap E F c ∈ O
  ne_top : O ≠ ⊤

namespace IsFunctionFieldOneVar

/-- A function field of one variable contains a transcendental element. -/
theorem exists_transcendental (hF : IsFunctionFieldOneVar E F) : ∃ t : F, Transcendental E t := by
  have h : Algebra.trdeg E F ≠ 0 := by rw [hF.trdeg_eq_one]; exact one_ne_zero
  exact Algebra.transcendental_def.mp (trdeg_ne_zero_iff.mp h)

/-- A function field of one variable is finite over `E(t)` for every transcendental `t`. -/
theorem finiteDimensional_adjoin (hF : IsFunctionFieldOneVar E F) {t : F}
    (ht : Transcendental E t) : FiniteDimensional E⟮t⟯ F := by
  have hind : AlgebraicIndependent E (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis E (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simp [hF.trdeg_eq_one])
  have halg := hb.isAlgebraic_field
  rw [Set.range_const] at halg
  have := hF.essFiniteType
  have : Algebra.EssFiniteType E⟮t⟯ F := Algebra.EssFiniteType.of_comp E E⟮t⟯ F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- If `F` is finite over `E(x)` for a transcendental `x`, then `F/E` is a function field of one
variable. -/
theorem of_finiteDimensional_adjoin {x : F} (hx : Transcendental E x)
    [FiniteDimensional E⟮x⟯ F] : IsFunctionFieldOneVar E F := by
  have hfg : (E⟮x⟯ : IntermediateField E F).FG :=
    IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)
  have h1 : Algebra.EssFiniteType E E⟮x⟯ := IntermediateField.essFiniteType_iff.mpr hfg
  have h2 : Algebra.EssFiniteType E⟮x⟯ F := inferInstance
  refine ⟨Algebra.EssFiniteType.comp E E⟮x⟯ F, ?_⟩
  have hind : AlgebraicIndependent E (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have halg : Algebra.IsAlgebraic (Algebra.adjoin E (Set.range fun _ : Unit => x)) F := by
    rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact Algebra.IsAlgebraic.of_finite _ _
  have hb : IsTranscendenceBasis E (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  have := hb.lift_cardinalMk_eq_trdeg
  simpa using this.symm

variable (E) in
/-- The rational function field `E(X)` is a function field of one variable. -/
theorem ratFunc : IsFunctionFieldOneVar E (RatFunc E) := by
  have : FiniteDimensional E⟮(RatFunc.X : RatFunc E)⟯ (RatFunc E) := by
    rw [RatFunc.adjoin_X]
    exact Module.finite_of_rank_eq_one IntermediateField.rank_top
  exact of_finiteDimensional_adjoin RatFunc.transcendental_X

/-- A function field in the sense of Mathlib (`FunctionField E F`: finite over `E(X)`) is a function
field of one variable. -/
theorem of_functionField [Algebra (RatFunc E) F] [IsScalarTower E (RatFunc E) F]
    [FunctionField E F] : IsFunctionFieldOneVar E F := by
  set x := algebraMap (RatFunc E) F RatFunc.X
  have hx : Transcendental E x :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc E) F).injective).mpr
      RatFunc.transcendental_X
  set φ := IsScalarTower.toAlgHom E (RatFunc E) F
  have hrange : φ.fieldRange = E⟮x⟯ := by
    rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X, IntermediateField.adjoin_map,
      Set.image_singleton]
    rfl
  let : Algebra (RatFunc E) φ.fieldRange :=
    (φ.toRingHom.codRestrict φ.fieldRange.toSubfield fun r =>
      AlgHom.mem_fieldRange.mpr ⟨r, rfl⟩).toAlgebra
  have : IsScalarTower (RatFunc E) φ.fieldRange F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional φ.fieldRange F :=
    Module.Finite.of_restrictScalars_finite (RatFunc E) φ.fieldRange F
  have : FiniteDimensional E⟮x⟯ F := hrange ▸ this
  exact of_finiteDimensional_adjoin hx

end IsFunctionFieldOneVar


section RationalAtPlace

variable {O : ValuationSubring F}

/-- Nonzero constants are units at every valuation ring containing `E`. -/
theorem valuation_algebraMap_eq_one (hE : ∀ c : E, algebraMap E F c ∈ O) {c : E} (hc : c ≠ 0) :
    O.valuation (algebraMap E F c) = 1 := by
  have h1 : O.valuation (algebraMap E F c) ≤ 1 := (O.valuation_le_one_iff _).mpr (hE c)
  have h2 : O.valuation (algebraMap E F c⁻¹) ≤ 1 := (O.valuation_le_one_iff _).mpr (hE c⁻¹)
  rw [map_inv₀, map_inv₀] at h2
  have h0 : O.valuation (algebraMap E F c) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (_root_.map_ne_zero _).mpr hc
  exact le_antisymm h1 (by
    have := (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2
    exact this)

/-- Polynomial expressions in an element of `O` with coefficients in `E` lie in `O`. -/
theorem aeval_mem (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F} (hs : s ∈ O) (a : E[X]) :
    aeval s a ∈ O := by
  rw [aeval_eq_sum_range]
  refine O.toSubring.sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hE _) (pow_mem hs _)

/-- If `|s| < 1` then `|a(s) - a(0)| < 1` for every `a ∈ E[X]`. -/
theorem valuation_aeval_sub_lt_one (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F}
    (hs : O.valuation s < 1) (a : E[X]) :
    O.valuation (aeval s a - algebraMap E F (a.coeff 0)) < 1 := by
  have hsO : s ∈ O := (O.valuation_le_one_iff _).mp hs.le
  have key : aeval s a - algebraMap E F (a.coeff 0) = aeval s a.divX * s := by
    conv_lhs => rw [← divX_mul_X_add a]
    simp
  rw [key, map_mul]
  calc O.valuation (aeval s a.divX) * O.valuation s ≤ 1 * O.valuation s := by
        gcongr
        exact (O.valuation_le_one_iff _).mpr (aeval_mem hE hsO _)
    _ < 1 := by rwa [one_mul]

/-- If `|s| < 1` and `a(0) ≠ 0` then `|a(s)| = 1`. -/
theorem valuation_aeval_eq_one (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F}
    (hs : O.valuation s < 1) {a : E[X]} (ha : a.coeff 0 ≠ 0) :
    O.valuation (aeval s a) = 1 := by
  rw [← valuation_algebraMap_eq_one hE ha]
  apply Valuation.map_eq_of_sub_lt
  rw [valuation_algebraMap_eq_one hE ha]
  exact valuation_aeval_sub_lt_one hE hs a

omit [Algebra E F] in
/-- A nonzero polynomial is `X ^ k * b` with `b(0) ≠ 0`. -/
theorem exists_eq_X_pow_mul_coeff_zero_ne_zero {a : E[X]} (ha : a ≠ 0) :
    ∃ (k : ℕ) (b : E[X]), a = X ^ k * b ∧ b.coeff 0 ≠ 0 := by
  obtain ⟨b, hb, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha 0
  refine ⟨_, b, by simpa using hb, ?_⟩
  rwa [map_zero, sub_zero, X_dvd_iff] at hndvd

/-- Every nonzero element of `E(s)` is `s ^ m * a(s) / b(s)` with `a(0), b(0)` nonzero. -/
theorem exists_eq_zpow_mul_div {s : F} (hs : s ≠ 0) {d : F} (hd : d ∈ E⟮s⟯) (hd0 : d ≠ 0) :
    ∃ (m : ℤ) (a b : E[X]), a.coeff 0 ≠ 0 ∧ b.coeff 0 ≠ 0 ∧
      d = s ^ m * (aeval s a / aeval s b) := by
  obtain ⟨r, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff E d).mp hd
  have hr : aeval s r ≠ 0 := fun h => hd0 (by simp [h])
  have hq : aeval s q ≠ 0 := fun h => hd0 (by simp [h])
  obtain ⟨k, a, rfl, ha⟩ :=
    exists_eq_X_pow_mul_coeff_zero_ne_zero (fun h : r = 0 => hr (by simp [h]))
  obtain ⟨l, b, rfl, hb⟩ :=
    exists_eq_X_pow_mul_coeff_zero_ne_zero (fun h : q = 0 => hq (by simp [h]))
  refine ⟨(k : ℤ) - l, a, b, ha, hb, ?_⟩
  simp only [map_mul, map_pow, aeval_X] at hq ⊢
  have hsl : s ^ l ≠ 0 := pow_ne_zero _ hs
  have hb0 : aeval s b ≠ 0 := right_ne_zero_of_mul hq
  rw [zpow_sub₀ hs, zpow_natCast, zpow_natCast]
  field_simp

/-- The valuation of a nonzero element of `E(s)` at every valuation ring containing `E` in whose
maximal ideal `s` lies is a fixed integral power of the valuation of `s`. -/
theorem exists_forall_valuation_eq_zpow {s : F} (hs : s ≠ 0) {d : F} (hd : d ∈ E⟮s⟯)
    (hd0 : d ≠ 0) :
    ∃ m : ℤ, ∀ O : ValuationSubring F, (∀ c : E, algebraMap E F c ∈ O) →
      O.valuation s < 1 → O.valuation d = O.valuation s ^ m := by
  obtain ⟨m, a, b, ha, hb, rfl⟩ := exists_eq_zpow_mul_div hs hd hd0
  refine ⟨m, fun O hE hsO => ?_⟩
  rw [map_mul, map_div₀, valuation_aeval_eq_one hE hsO ha, valuation_aeval_eq_one hE hsO hb,
    div_one, mul_one, map_zpow₀]

/-- An element of `E(s)` that is integral at `O` (with `|s| < 1`) is congruent to a constant
modulo the maximal ideal. -/
theorem exists_valuation_sub_lt_one_of_mem_adjoin (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F}
    (hs0 : s ≠ 0) (hs : O.valuation s < 1) {d : F} (hd : d ∈ E⟮s⟯) (hd1 : O.valuation d ≤ 1) :
    ∃ e : E, O.valuation (d - algebraMap E F e) < 1 := by
  by_cases hd0 : d = 0
  · exact ⟨0, by simp [hd0]⟩
  obtain ⟨m, a, b, ha, hb, rfl⟩ := exists_eq_zpow_mul_div hs0 hd hd0
  have hσ0 : 0 < O.valuation s := (Valuation.pos_iff _).mpr hs0
  have hA := valuation_aeval_eq_one hE hs ha
  have hB := valuation_aeval_eq_one hE hs hb
  have hval : O.valuation (s ^ m * (aeval s a / aeval s b)) = O.valuation s ^ m := by
    rw [map_mul, map_div₀, hA, hB, div_one, mul_one, map_zpow₀]
  rw [hval] at hd1
  have hm : 0 ≤ m := (zpow_le_one_iff_right_of_lt_one₀ hσ0 hs).mp hd1
  rcases hm.lt_or_eq with hm | rfl
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, hval]
    exact (zpow_lt_one_iff_right_of_lt_one₀ hσ0 hs).mpr hm
  refine ⟨a.coeff 0 / b.coeff 0, ?_⟩
  set A := aeval s a
  set B := aeval s b
  set α := algebraMap E F (a.coeff 0)
  set β := algebraMap E F (b.coeff 0)
  have hB0 : B ≠ 0 := by intro h; rw [h, map_zero] at hB; exact zero_ne_one hB
  have hβ0 : β ≠ 0 := (_root_.map_ne_zero _).mpr hb
  have key : s ^ (0 : ℤ) * (A / B) - algebraMap E F (a.coeff 0 / b.coeff 0) =
      (β * (A - α) - α * (B - β)) / (B * β) := by
    have hαβ : algebraMap E F (a.coeff 0 / b.coeff 0) = α / β := map_div₀ _ _ _
    rw [hαβ, zpow_zero, one_mul]
    field_simp
    ring
  rw [key, map_div₀, map_mul, hB, valuation_algebraMap_eq_one hE hb, mul_one, div_one]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, valuation_algebraMap_eq_one hE hb, one_mul]
    exact valuation_aeval_sub_lt_one hE hs a
  · rw [map_mul]
    calc O.valuation α * O.valuation (B - β) ≤ 1 * O.valuation (B - β) := by
          gcongr; exact (O.valuation_le_one_iff _).mpr (hE _)
      _ < 1 := by rw [one_mul]; exact valuation_aeval_sub_lt_one hE hs b

end RationalAtPlace

section Independence

variable {O : ValuationSubring F}

/-- Elements whose values are pairwise incongruent modulo `|s| ^ ℤ` are linearly independent
over `E(s)`. -/
theorem linearIndependent_of_valuation_ne (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F}
    (hs0 : s ≠ 0) (hs : O.valuation s < 1) {ι : Type*} {y : ι → F} (hy0 : ∀ i, y i ≠ 0)
    (hy : ∀ i j, i ≠ j → ∀ m : ℤ, O.valuation (y i) ≠ O.valuation (y j) * O.valuation s ^ m) :
    LinearIndependent E⟮s⟯ y := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum i hi
  by_contra hgi
  set t' := t.filter (fun k => g k ≠ 0) with ht'
  have hit' : i ∈ t' := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image t' (fun k => O.valuation ((g k : F) * y k))
    ⟨i, hit'⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hsum' : ∑ k ∈ t', (g k : F) * y k = 0 := by
    rw [ht', Finset.sum_filter_of_ne (fun k _ h => ?_)]
    · simpa [IntermediateField.smul_def, smul_eq_mul] using hsum
    · intro hgk; simp [hgk] at h
  have hval := Valuation.map_sum_eq_of_lt O.valuation (f := fun k => (g k : F) * y k) hj
    (fun k hk => by
      obtain ⟨hk, hkj⟩ := Finset.mem_sdiff.mp hk
      rw [Finset.mem_singleton] at hkj
      refine lt_of_le_of_ne (hjmax k hk) fun heq => ?_
      have hgk : g k ≠ 0 := (Finset.mem_filter.mp hk).2
      have hgk' : (g k : F) ≠ 0 := by simpa using hgk
      have hgj' : (g j : F) ≠ 0 := by simpa using hgj
      obtain ⟨mk, hmk⟩ := exists_forall_valuation_eq_zpow hs0 (g k).2 hgk'
      obtain ⟨mj, hmj⟩ := exists_forall_valuation_eq_zpow hs0 (g j).2 hgj'
      have hσ0 : O.valuation s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0
      apply hy k j hkj (mj - mk)
      simp only [map_mul, hmk O hE hs, hmj O hE hs] at heq
      rw [zpow_sub₀ hσ0]
      have hk0 : O.valuation s ^ mk ≠ 0 := zpow_ne_zero _ hσ0
      field_simp
      rw [mul_comm, heq, mul_comm])
  rw [hsum', map_zero] at hval
  have : (g j : F) * y j ≠ 0 := mul_ne_zero (by simpa using hgj) (hy0 j)
  exact this ((Valuation.zero_iff _).mp hval.symm)

/-- Elements of `O` whose residues are linearly independent over `E` are linearly independent
over `E(s)`. -/
theorem linearIndependent_of_residue (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F}
    (hs0 : s ≠ 0) (hs : O.valuation s < 1) {ι : Type*} {x : ι → F}
    (hx : ∀ i, O.valuation (x i) ≤ 1)
    (hres : ∀ (t : Finset ι) (e : ι → E), O.valuation (∑ i ∈ t, e i • x i) < 1 →
      ∀ i ∈ t, e i = 0) :
    LinearIndependent E⟮s⟯ x := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum i hi
  by_contra hgi
  set t' := t.filter (fun k => g k ≠ 0) with ht'
  have hit' : i ∈ t' := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image t' (fun k => O.valuation (g k : F))
    ⟨i, hit'⟩
  have hjt : j ∈ t := (Finset.mem_filter.mp hj).1
  have hgj : (g j : F) ≠ 0 := by simpa using (Finset.mem_filter.mp hj).2
  have hgj0 : 0 < O.valuation (g j : F) := (Valuation.pos_iff _).mpr hgj
  set d : ι → F := fun k => (g k : F) / (g j : F) with hd
  have hdmem : ∀ k, d k ∈ E⟮s⟯ := fun k => div_mem (g k).2 (g j).2
  have hd1 : ∀ k ∈ t, O.valuation (d k) ≤ 1 := by
    intro k hk
    by_cases hgk : g k = 0
    · simp [hd, hgk]
    · rw [hd, map_div₀, div_le_one₀ hgj0]
      exact hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
  have H : ∀ k, ∃ e : E, k ∈ t → O.valuation (d k - algebraMap E F e) < 1 := by
    intro k
    by_cases hk : k ∈ t
    · obtain ⟨e, he⟩ := exists_valuation_sub_lt_one_of_mem_adjoin hE hs0 hs (hdmem k) (hd1 k hk)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose e he using H
  have hsumd : ∑ k ∈ t, d k * x k = 0 := by
    have : ∑ k ∈ t, d k * x k = (g j : F)⁻¹ * ∑ k ∈ t, g k • x k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd, IntermediateField.smul_def, smul_eq_mul]
      ring
    rw [this, hsum, mul_zero]
  have hsume : ∑ k ∈ t, e k • x k = -∑ k ∈ t, (d k - algebraMap E F (e k)) * x k := by
    rw [← sub_eq_zero, sub_neg_eq_add, ← Finset.sum_add_distrib]
    rw [← hsumd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def]
    ring
  have hlt : O.valuation (∑ k ∈ t, e k • x k) < 1 := by
    rw [hsume, Valuation.map_neg]
    refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
    rw [map_mul]
    calc O.valuation (d k - algebraMap E F (e k)) * O.valuation (x k)
        ≤ O.valuation (d k - algebraMap E F (e k)) * 1 := by gcongr; exact hx k
      _ < 1 := by rw [mul_one]; exact he k hk
  have hej := hres t e hlt j hjt
  have := he j hjt
  rw [hej, map_zero, sub_zero, hd] at this
  simp only [div_self hgj, map_one, lt_irrefl] at this

omit [Field E] [Algebra E F] in
/-- Auxiliary inequality for the pole bound: if `0 < γ < 1` and `σ < γ ^ n`, the powers
`γ ^ i`, `i ≤ n`, are pairwise incongruent modulo `σ ^ ℤ`. -/
private theorem aux_pow_ne {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {γ σ : Γ} {n : ℕ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hσ0 : 0 < σ) (hσ : σ < γ ^ n) {i j : ℕ} (hi : i ≤ n)
    (hj : j ≤ n) (hij : i ≠ j) (m : ℤ) : γ ^ i ≠ γ ^ j * σ ^ m := by
  have hσ1 : σ ≤ 1 := hσ.le.trans (pow_le_one₀ hγ0.le hγ1.le)
  -- `γ ^ b * σ ^ k < γ ^ a` whenever `a ≤ b + n` and `0 < k`
  have key : ∀ a b : ℕ, a ≤ b + n → ∀ k : ℤ, 0 < k → γ ^ b * σ ^ k < γ ^ a := by
    intro a b hab k hk
    have h1 : σ ^ k ≤ σ := by
      simpa using zpow_le_zpow_right_of_le_one₀ hσ0 hσ1 (show (1 : ℤ) ≤ k by omega)
    calc γ ^ b * σ ^ k ≤ γ ^ b * σ := by gcongr
      _ < γ ^ b * γ ^ n := mul_lt_mul_of_pos_left hσ (pow_pos hγ0 _)
      _ = γ ^ (b + n) := (pow_add _ _ _).symm
      _ ≤ γ ^ a := (pow_le_pow_iff_right_of_lt_one₀ hγ0 hγ1).mpr hab
  intro h
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have h' : γ ^ j = γ ^ i * σ ^ (-m) := by
      rw [h, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hσ0.ne'), mul_one]
    exact (key j i (by omega) (-m) (by omega)).ne h'.symm
  · rw [zpow_zero, mul_one] at h
    exact hij (pow_right_injective₀ hγ0 hγ1.ne h)
  · exact (key i j (by omega) m hm).ne h.symm

/-- **Pole bound.** If `[F : E(s)] = n` is finite and `|s| < 1`, then `|x| ^ n ≤ |s|` for every
`x` in the maximal ideal. -/
theorem pow_finrank_le (hE : ∀ c : E, algebraMap E F c ∈ O) {s : F} (hs0 : s ≠ 0)
    (hs : O.valuation s < 1) [FiniteDimensional E⟮s⟯ F] {x : F} (hx : O.valuation x < 1) :
    O.valuation x ^ Module.finrank E⟮s⟯ F ≤ O.valuation s := by
  set n := Module.finrank E⟮s⟯ F with hn
  have hnpos : 0 < n := Module.finrank_pos
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, zero_pow hnpos.ne']; exact zero_le
  by_contra! hlt
  have hγ0 : 0 < O.valuation x := (Valuation.pos_iff _).mpr hx0
  have hσ0 : 0 < O.valuation s := (Valuation.pos_iff _).mpr hs0
  have hli : LinearIndependent E⟮s⟯ (fun i : Fin (n + 1) => x ^ (i : ℕ)) := by
    refine linearIndependent_of_valuation_ne hE hs0 hs (fun i => pow_ne_zero _ hx0) ?_
    intro i j hij m
    simp only [map_pow]
    exact aux_pow_ne hγ0 hx hσ0 hlt (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)
      (fun h => hij (Fin.ext h)) m
  have := hli.fintype_card_le_finrank
  simp [← hn] at this

end Independence

section Places

variable {O : ValuationSubring F}

namespace IsPlace

/-- The valuation of a place is trivial on `E`. -/
theorem isTrivialOn (hO : IsPlace E O) : O.valuation.IsTrivialOn E :=
  ⟨fun _ hc => valuation_algebraMap_eq_one hO.algebraMap_mem hc⟩

/-- A place is a proper subring. -/
theorem exists_notMem (hO : IsPlace E O) : ∃ y : F, y ∉ O := by
  by_contra! h
  exact hO.ne_top (eq_top_iff.mpr fun y _ => h y)

/-- A place has a nonzero element of its maximal ideal. -/
theorem exists_valuation_lt_one (hO : IsPlace E O) : ∃ t : F, t ≠ 0 ∧ O.valuation t < 1 := by
  obtain ⟨y, hy⟩ := hO.exists_notMem
  have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
  refine ⟨y⁻¹, inv_ne_zero hy0, ?_⟩
  have : 1 < O.valuation y := by
    rw [← not_le, O.valuation_le_one_iff]; exact hy
  exact (O.valuation.one_lt_val_iff hy0).mp this

/-- Nonzero elements of the maximal ideal of a place are transcendental. -/
theorem transcendental_of_valuation_lt_one (hO : IsPlace E O) {t : F} (ht0 : t ≠ 0)
    (ht : O.valuation t < 1) : Transcendental E t := by
  have := hO.isTrivialOn
  exact Valuation.transcendental_of_ne_one E t ht0 ht.ne

/-- Elements algebraic over `E` lie in every place. -/
theorem mem_of_isAlgebraic (hO : IsPlace E O) {x : F} (hx : IsAlgebraic E x) : x ∈ O := by
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
  have h1 : 1 < O.valuation x := by rw [← not_le, O.valuation_le_one_iff]; exact hxO
  have h2 := (O.valuation.one_lt_val_iff hx0).mp h1
  exact hO.transcendental_of_valuation_lt_one (inv_ne_zero hx0) h2 (IsAlgebraic.inv_iff.mpr hx)

/-- A place has a nonzero, necessarily transcendental, element of its maximal ideal. -/
theorem exists_transcendental_valuation_lt_one (hO : IsPlace E O) :
    ∃ t : F, t ≠ 0 ∧ O.valuation t < 1 ∧ Transcendental E t := by
  obtain ⟨t, ht0, ht⟩ := hO.exists_valuation_lt_one
  exact ⟨t, ht0, ht, hO.transcendental_of_valuation_lt_one ht0 ht⟩

end IsPlace

/-- A transcendental element has a pole. -/
theorem exists_isPlace_notMem {f : F} (hf : Transcendental E f) : ∃ O, IsPlace E O ∧ f ∉ O := by
  have hfR : f ∉ (integralClosure E F).toSubring := fun h => hf h.isAlgebraic
  obtain ⟨V, hRV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hfR
  refine ⟨V, ⟨fun c => hRV ((integralClosure E F).algebraMap_mem c), fun h => ?_⟩, hfV⟩
  exact hfV (h ▸ ValuationSubring.mem_top f)

/-- An element lies in every place if and only if it is algebraic. -/
theorem forall_isPlace_mem_iff {f : F} : (∀ O, IsPlace E O → f ∈ O) ↔ IsAlgebraic E f := by
  refine ⟨fun h => ?_, fun hf O hO => hO.mem_of_isAlgebraic hf⟩
  by_contra hf
  obtain ⟨O, hO, hfO⟩ := exists_isPlace_notMem hf
  exact hfO (h O hO)

/-- If `E` is algebraically closed in `F`, every nonconstant element has a pole. -/
theorem exists_isPlace_notMem_of_notMem_range
    (halg : ∀ x : F, IsAlgebraic E x → x ∈ (algebraMap E F).range) {f : F}
    (hf : f ∉ (algebraMap E F).range) : ∃ O, IsPlace E O ∧ f ∉ O :=
  exists_isPlace_notMem fun h => hf (halg f h)

/-- An algebraically closed field is algebraically closed in every extension. -/
theorem mem_range_of_isAlgebraic [IsAlgClosed E] {x : F} (hx : IsAlgebraic E x) :
    x ∈ (algebraMap E F).range := by
  rw [← minpoly.natDegree_eq_one_iff]
  exact Polynomial.natDegree_eq_of_degree_eq_some
    (IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hx.isIntegral))

/-- In a function field of one variable, every value `γ = |x|` at a place satisfies
`γ ^ n! ∈ |t| ^ ℤ` for `t` in the maximal ideal, `n = [F : E(t)]`. -/
theorem exists_valuation_pow_factorial_eq_zpow (hE : ∀ c : E, algebraMap E F c ∈ O) {t : F}
    (ht0 : t ≠ 0) (ht : O.valuation t < 1) [FiniteDimensional E⟮t⟯ F] {x : F} (hx0 : x ≠ 0) :
    ∃ m : ℤ, O.valuation x ^ (Module.finrank E⟮t⟯ F).factorial = O.valuation t ^ m := by
  set n := Module.finrank E⟮t⟯ F with hn
  set γ := O.valuation x
  set σ := O.valuation t
  have hγ0 : γ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  by_contra! hneg
  have hli : LinearIndependent E⟮t⟯ (fun i : Fin (n + 1) => x ^ (i : ℕ)) := by
    refine linearIndependent_of_valuation_ne hE ht0 ht (fun i => pow_ne_zero _ hx0) ?_
    intro i j hij m h
    simp only [map_pow] at h
    have hij' : (i : ℕ) ≠ j := fun h' => hij (Fin.ext h')
    rcases Nat.lt_or_gt_of_ne hij' with hlt | hlt
    · -- `γ ^ (j - i) = σ ^ (-m)`
      have hd : γ ^ ((j : ℕ) - i) = σ ^ (-m) := by
        have h1 : γ ^ (j : ℕ) = γ ^ (i : ℕ) * γ ^ ((j : ℕ) - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [h1, mul_assoc] at h
        have h2 : γ ^ ((j : ℕ) - i) * σ ^ m = 1 := by
          have := mul_left_cancel₀ (pow_ne_zero (i : ℕ) hγ0) (h.symm.trans (mul_one _).symm)
          exact this
        rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h2
      obtain ⟨q, hq⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt)
        (by have := j.2; omega : (j : ℕ) - i ≤ n)
      apply hneg (-m * q)
      rw [hq, pow_mul, hd, zpow_mul, zpow_natCast]
    · have hd : γ ^ ((i : ℕ) - j) = σ ^ m := by
        have h1 : γ ^ (i : ℕ) = γ ^ (j : ℕ) * γ ^ ((i : ℕ) - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [h1] at h
        exact mul_left_cancel₀ (pow_ne_zero (j : ℕ) hγ0) h
      obtain ⟨q, hq⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt)
        (by have := i.2; omega : (i : ℕ) - j ≤ n)
      apply hneg (m * q)
      rw [hq, pow_mul, hd, zpow_mul, zpow_natCast]
  have := hli.fintype_card_le_finrank
  simp [← hn] at this

namespace IsPlace

/-- **Places are discrete valuation rings.** -/
theorem isDiscreteValuationRing (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) :
    IsDiscreteValuationRing O := by
  obtain ⟨t, ht0, ht, htr⟩ := hO.exists_transcendental_valuation_lt_one
  have := hF.finiteDimensional_adjoin htr
  set N := (Module.finrank E⟮t⟯ F).factorial
  have hN : N ≠ 0 := Nat.factorial_ne_zero _
  have hσ0 : O.valuation t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  set σ : O.ValueGroupˣ := Units.mk0 _ hσ0
  have hmem : ∀ u : O.ValueGroupˣ, u ^ N ∈ Subgroup.zpowers σ := by
    intro u
    obtain ⟨x, hx⟩ := O.valuation_surjective (u : O.ValueGroup)
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [map_zero] at hx; exact u.ne_zero hx.symm
    obtain ⟨m, hm⟩ := exists_valuation_pow_factorial_eq_zpow hO.algebraMap_mem ht0 ht hx0
    refine ⟨m, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_pow_eq_pow_val, ← hx, hm]
  let f : O.ValueGroupˣ →* Subgroup.zpowers σ := (powMonoidHom N).codRestrict _ hmem
  have hf : Function.Injective f := by
    intro u w h
    have : u ^ N = w ^ N := congrArg Subtype.val h
    exact pow_left_injective hN this
  have hcyc : IsCyclic O.ValueGroupˣ := isCyclic_of_injective f hf
  have hcyc' : IsCyclic (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass O.valuation)) :=
    Subgroup.isCyclic _
  have hnt : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass O.valuation)) := by
    refine ⟨⟨⟨σ, MonoidWithZeroHom.mem_valueGroup _ ⟨t, rfl⟩⟩, 1, fun h => ?_⟩⟩
    exact ht.ne (by simpa [σ, Subtype.ext_iff, Units.ext_iff] using h)
  have := Valuation.valuationSubring_isDiscreteValuationRing O.valuation
  rwa [O.valuationSubring_valuation] at this

end IsPlace

namespace IsPlace

/-- **Residues are algebraic.** Every element of a place is a root modulo the maximal ideal of a
nonzero polynomial over `E` of degree at most `[F : E(t)]`. -/
theorem exists_aeval_valuation_lt_one (hO : IsPlace E O) {t : F} (ht0 : t ≠ 0)
    (ht : O.valuation t < 1) [FiniteDimensional E⟮t⟯ F] {x : F} (hx : O.valuation x ≤ 1) :
    ∃ a : E[X], a ≠ 0 ∧ a.natDegree ≤ Module.finrank E⟮t⟯ F ∧ O.valuation (aeval x a) < 1 := by
  classical
  set n := Module.finrank E⟮t⟯ F with hn
  have hnli : ¬ LinearIndependent E⟮t⟯ (fun i : Fin (n + 1) => x ^ (i : ℕ)) := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp [← hn] at this
  have hres : ¬ ∀ (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → E),
      O.valuation (∑ i ∈ s, e i • x ^ (i : ℕ)) < 1 → ∀ i ∈ s, e i = 0 := fun h =>
    hnli (linearIndependent_of_residue hO.algebraMap_mem ht0 ht (fun i => by
      rw [map_pow]; exact pow_le_one₀ zero_le hx) h)
  push Not at hres
  obtain ⟨s, e, hlt, i, hi, hei⟩ := hres
  refine ⟨∑ k ∈ s, monomial (k : ℕ) (e k), ?_, ?_, ?_⟩
  · intro h
    apply hei
    have := congrArg (fun a => Polynomial.coeff a (i : ℕ)) h
    simp only [finsetSum_coeff, coeff_monomial, coeff_zero] at this
    rw [Finset.sum_eq_single i (fun k _ hk => if_neg (fun h' => hk (Fin.ext h')))
      (fun h' => (h' hi).elim), if_pos rfl] at this
    exact this
  · refine (natDegree_sum_le_of_forall_le _ _ fun k _ => ?_)
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp k.2)
  · simpa [map_sum, aeval_monomial, Algebra.smul_def] using hlt

/-- **Residue field over an algebraically closed field.** If `E` is algebraically closed, every
element of a place is congruent to a constant. -/
theorem exists_valuation_sub_algebraMap_lt_one [IsAlgClosed E] (hF : IsFunctionFieldOneVar E F)
    (hO : IsPlace E O) {x : F} (hx : O.valuation x ≤ 1) :
    ∃ c : E, O.valuation (x - algebraMap E F c) < 1 := by
  obtain ⟨t, ht0, ht, htr⟩ := hO.exists_transcendental_valuation_lt_one
  have := hF.finiteDimensional_adjoin htr
  obtain ⟨a, ha0, -, ha⟩ := hO.exists_aeval_valuation_lt_one ht0 ht hx
  -- strong induction on the degree
  induction h : a.natDegree using Nat.strong_induction_on generalizing a with
  | _ d ih =>
    by_cases hd : a.degree = 0
    · obtain ⟨c, rfl⟩ : ∃ c, a = C c := ⟨a.coeff 0, eq_C_of_degree_eq_zero hd⟩
      have hc : c ≠ 0 := fun hc => ha0 (by simp [hc])
      rw [aeval_C, valuation_algebraMap_eq_one hO.algebraMap_mem hc] at ha
      exact (lt_irrefl _ ha).elim
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root a hd
    have hfac := mul_divByMonic_eq_iff_isRoot.mpr hα
    set q := a /ₘ (X - C α)
    have hq0 : q ≠ 0 := fun hq => ha0 (by rw [← hfac, hq, mul_zero])
    have hval : O.valuation (x - algebraMap E F α) * O.valuation (aeval x q) < 1 := by
      rw [← map_mul]
      have : aeval x a = (x - algebraMap E F α) * aeval x q := by
        conv_lhs => rw [← hfac]
        simp
      rwa [← this]
    by_cases h1 : O.valuation (x - algebraMap E F α) < 1
    · exact ⟨α, h1⟩
    push Not at h1
    have hq1 : O.valuation (aeval x q) < 1 := by
      by_contra! hq1
      exact (not_lt.mpr (one_le_mul_of_one_le_of_one_le h1 hq1)) hval
    refine ih q.natDegree ?_ q hq0 hq1 rfl
    rw [← h]
    have := natDegree_divByMonic a (monic_X_sub_C α)
    rw [this, natDegree_X_sub_C]
    have : 0 < a.natDegree := natDegree_pos_iff_degree_pos.mpr
      (lt_of_le_of_ne (zero_le_degree_iff.mpr ha0) (Ne.symm hd))
    omega

/-- Over an algebraically closed field, `E → κ(O)` is surjective (hence an isomorphism). -/
theorem residue_surjective [IsAlgClosed E] (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) :
    Function.Surjective
      (fun c : E => IsLocalRing.residue O ⟨algebraMap E F c, hO.algebraMap_mem c⟩) := by
  intro y
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ :=
    hO.exists_valuation_sub_algebraMap_lt_one hF ((O.valuation_le_one_iff _).mpr y.2)
  refine ⟨c, ?_⟩
  simp only
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have : (⟨algebraMap E F c, hO.algebraMap_mem c⟩ - y : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [← Valuation.map_neg]
    simpa using hc
  exact this

/-- **Places are incomparable.** A valuation ring containing a place and different from `F`
equals it. -/
theorem eq_of_le (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) {O' : ValuationSubring F}
    (hle : O ≤ O') (hO' : O' ≠ ⊤) : O' = O := by
  have := hO.isDiscreteValuationRing hF
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : (π : F) ≠ 0 := by simpa using hπ.ne_zero
  refine le_antisymm (fun x hx => ?_) hle
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := F) hπ hx0
  have huO' : ∀ w : Oˣ, ((w : O) : F) ∈ O' := fun w => hle (w : O).2
  have hπO : (π : F) ∈ O' := hle π.2
  have hn : n < 0 := by
    by_contra! hn
    apply hxO
    lift n to ℕ using hn
    rw [hu, Units.smul_def, zpow_natCast, Algebra.smul_def]
    exact mul_mem (u : O).2 (pow_mem π.2 _)
  -- `π⁻¹ ∈ O'`
  have hπinv : (π : F)⁻¹ ∈ O' := by
    have hpow : ((π : F)⁻¹) ^ (-n).toNat ∈ O' := by
      have : ((π : F)⁻¹) ^ (-n).toNat = ((u⁻¹ : Oˣ) : O) * x := by
        rw [hu, Units.smul_def, Algebra.smul_def, ← mul_assoc]
        have h1 : algebraMap O F ((u⁻¹ : Oˣ) : O) * algebraMap O F (u : O) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [show (algebraMap O F) ((u⁻¹ : Oˣ) : O) = ((u⁻¹ : Oˣ) : O) from rfl] at h1
        rw [show (algebraMap O F) (u : O) = ((u : O) : F) from rfl] at h1
        rw [show (algebraMap O F) π = (π : F) from rfl]
        rw [show (algebraMap O F) (u : O) = ((u : O) : F) from rfl, h1, one_mul,
          ← zpow_natCast, inv_zpow', Int.toNat_of_nonneg (by omega), neg_neg]
      rw [this]
      exact mul_mem (huO' _) hx
    by_contra hnot
    have h1 : 1 < O'.valuation ((π : F)⁻¹) := by
      rw [← not_le, O'.valuation_le_one_iff]; exact hnot
    have h2 : 1 < O'.valuation (((π : F)⁻¹) ^ (-n).toNat) := by
      rw [map_pow]; exact one_lt_pow₀ h1 (by omega)
    exact (not_le.mpr h2) ((O'.valuation_le_one_iff _).mpr hpow)
  apply hO'
  refine eq_top_iff.mpr fun z _ => ?_
  by_cases hz : z = 0
  · rw [hz]; exact O'.zero_mem
  obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := F) hπ hz
  rw [hw, Units.smul_def, Algebra.smul_def]
  refine mul_mem (huO' w) ?_
  show (π : F) ^ k ∈ O'
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [zpow_natCast]; exact pow_mem hπO _
  · have : (π : F) ^ k = ((π : F)⁻¹) ^ (-k).toNat := by
      rw [← zpow_natCast, inv_zpow', Int.toNat_of_nonneg (by omega), neg_neg]
    rw [this]; exact pow_mem hπinv _

/-- **Normalized valuation.** A place has an element `π` of maximal value `< 1`, and the value of
every nonzero element is an integral power of `|π|`. -/
theorem exists_uniformizer (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) :
    ∃ π : F, 0 < O.valuation π ∧ O.valuation π < 1 ∧
      (∀ x : F, O.valuation x < 1 → O.valuation x ≤ O.valuation π) ∧
      ∀ f : F, f ≠ 0 → ∃ m : ℤ, O.valuation f = O.valuation π ^ m := by
  have := hO.isDiscreteValuationRing hF
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : (π : F) ≠ 0 := by simpa using hπ.ne_zero
  have hπm : π ∈ IsLocalRing.maximalIdeal O := hπ.not_isUnit
  refine ⟨π, (Valuation.pos_iff _).mpr hπ0, (O.valuation_lt_one_iff π).mp hπm, fun x hx => ?_,
    fun f hf => ?_⟩
  · have hxO : x ∈ O := (O.valuation_le_one_iff x).mp hx.le
    have hxm : (⟨x, hxO⟩ : O) ∈ IsLocalRing.maximalIdeal O := (O.valuation_lt_one_iff _).mpr hx
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hxm
    obtain ⟨y, hy⟩ := hxm
    have hx' : x = (y : F) * π := by
      have := congrArg (fun z : O => (z : F)) hy
      simpa using this.symm
    rw [hx', map_mul]
    calc O.valuation (y : F) * O.valuation (π : F) ≤ 1 * O.valuation (π : F) := by
          gcongr; exact (O.valuation_le_one_iff _).mpr y.2
      _ = O.valuation (π : F) := one_mul _
  · obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := F) hπ hf
    refine ⟨m, ?_⟩
    rw [hu, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀]
    have : O.valuation (algebraMap O F (u : O)) = 1 := O.valuation_unit u
    rw [this, one_mul]
    rfl

end IsPlace

end Places

section Approximation

omit [Field E] [Algebra E F]

/-- **Approximation, first step.** If `O₀` is incomparable with every member of a finite set `S`
of valuation rings, there is `z` with `|z|₀ < 1` and `|z|_O > 1` for all `O ∈ S`. -/
theorem exists_valuation_lt_one_one_lt (O₀ : ValuationSubring F)
    (S : Finset (ValuationSubring F)) (hS : ∀ O ∈ S, ¬ O₀ ≤ O ∧ ¬ O ≤ O₀) :
    ∃ z : F, O₀.valuation z < 1 ∧ ∀ O ∈ S, 1 < O.valuation z := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert O' S hO'S ih =>
    obtain ⟨z, hz0, hzS⟩ := ih fun O hO => hS O (Finset.mem_insert_of_mem hO)
    obtain ⟨h1, h2⟩ := hS O' (Finset.mem_insert_self _ _)
    obtain ⟨a, haO₀, haO'⟩ := SetLike.not_le_iff_exists.mp h1
    obtain ⟨b, hbO', hbO₀⟩ := SetLike.not_le_iff_exists.mp h2
    have hb0 : b ≠ 0 := fun h => hbO₀ (h ▸ O₀.zero_mem)
    set u := a / b with hu
    have hu₀ : O₀.valuation u < 1 := by
      rw [hu, map_div₀]
      have hb1 : 1 < O₀.valuation b := by rw [← not_le, O₀.valuation_le_one_iff]; exact hbO₀
      rw [div_lt_one₀ (zero_lt_one.trans hb1)]
      exact lt_of_le_of_lt ((O₀.valuation_le_one_iff _).mpr haO₀) hb1
    have hu' : 1 < O'.valuation u := by
      rw [hu, map_div₀]
      have hb1 : O'.valuation b ≤ 1 := (O'.valuation_le_one_iff _).mpr hbO'
      have ha1 : 1 < O'.valuation a := by rw [← not_le, O'.valuation_le_one_iff]; exact haO'
      have hb0' : 0 < O'.valuation b := (Valuation.pos_iff _).mpr hb0
      rw [one_lt_div₀ hb0']
      exact lt_of_le_of_lt hb1 ha1
    have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hu'; exact not_lt.mpr zero_le hu'
    by_cases hzO' : 1 < O'.valuation z
    · refine ⟨z, hz0, fun O hO => ?_⟩
      rcases Finset.mem_insert.mp hO with rfl | hO
      · exact hzO'
      · exact hzS O hO
    push Not at hzO'
    -- choose an exponent `m + 1` avoiding the finitely many coincidences
    set bad : Finset ℕ := (Finset.range (S.card + 1)).filter
      (fun m => ∃ O ∈ S, O.valuation u ^ (m + 1) = O.valuation z) with hbad
    have hbad_le : bad.card ≤ S.card := by
      have hsub : bad ⊆ S.biUnion (fun O => (Finset.range (S.card + 1)).filter
          (fun m => O.valuation u ^ (m + 1) = O.valuation z)) := by
        intro m hm
        obtain ⟨hmr, O, hO, hOm⟩ := Finset.mem_filter.mp hm
        exact Finset.mem_biUnion.mpr ⟨O, hO, Finset.mem_filter.mpr ⟨hmr, hOm⟩⟩
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      refine (Finset.sum_le_sum fun O hO => (?_ : _ ≤ 1)).trans (by simp)
      rw [Finset.card_le_one]
      intro m₁ hm₁ m₂ hm₂
      have e₁ := (Finset.mem_filter.mp hm₁).2
      have e₂ := (Finset.mem_filter.mp hm₂).2
      have hz1 := hzS O hO
      have hvu0 : 0 < O.valuation u := (Valuation.pos_iff _).mpr hu0
      have hvu1 : O.valuation u ≠ 1 := by
        intro h; rw [h, one_pow] at e₁; rw [← e₁] at hz1; exact lt_irrefl _ hz1
      have := pow_right_injective₀ hvu0 hvu1 (e₁.trans e₂.symm)
      omega
    obtain ⟨m, hm, hmbad⟩ : ∃ m ∈ Finset.range (S.card + 1), m ∉ bad := by
      by_contra! h
      have : Finset.range (S.card + 1) ⊆ bad := fun m hm => h m hm
      have := Finset.card_le_card this
      simp at this; omega
    have hmS : ∀ O ∈ S, O.valuation u ^ (m + 1) ≠ O.valuation z := fun O hO h =>
      hmbad (Finset.mem_filter.mpr ⟨hm, O, hO, h⟩)
    refine ⟨z + u ^ (m + 1), ?_, fun O hO => ?_⟩
    · refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hz0 ?_)
      rw [map_pow]; exact pow_lt_one₀ zero_le hu₀ (Nat.succ_ne_zero m)
    · rcases Finset.mem_insert.mp hO with rfl | hO
      · have : 1 < O.valuation (u ^ (m + 1)) := by
          rw [map_pow]; exact one_lt_pow₀ hu' (Nat.succ_ne_zero m)
        rw [Valuation.map_add_eq_of_lt_right _ (lt_of_le_of_lt hzO' this)]
        exact this
      · rw [Valuation.map_add_of_distinct_val _ (by rw [map_pow]; exact (hmS O hO).symm)]
        exact lt_of_lt_of_le (hzS O hO) (le_max_left _ _)

/-- **Approximation.** If `O₀` is incomparable with every member of a finite set `S` of valuation
rings, there is `y` with `|y - 1|₀ < 1` and `|y|_O < 1` for all `O ∈ S`. -/
theorem exists_valuation_sub_one_lt_one (O₀ : ValuationSubring F)
    (S : Finset (ValuationSubring F)) (hS : ∀ O ∈ S, ¬ O₀ ≤ O ∧ ¬ O ≤ O₀) :
    ∃ y : F, O₀.valuation (y - 1) < 1 ∧ ∀ O ∈ S, O.valuation y < 1 := by
  obtain ⟨z, hz0, hzS⟩ := exists_valuation_lt_one_one_lt O₀ S hS
  have h1z : O₀.valuation (1 + z) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have h1z0 : 1 + z ≠ 0 := fun h => by rw [h, map_zero] at h1z; exact zero_ne_one h1z
  refine ⟨(1 + z)⁻¹, ?_, fun O hO => ?_⟩
  · have : (1 + z)⁻¹ - 1 = -z / (1 + z) := by field_simp; ring
    rw [this, map_div₀, h1z, div_one, Valuation.map_neg]
    exact hz0
  · have h := hzS O hO
    have : O.valuation (1 + z) = O.valuation z := by
      rw [Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
    rw [map_inv₀, this]
    exact inv_lt_one_of_one_lt₀ h

end Approximation

section Poles

/-- **At most `[F : E(s)]` places contain `s` in their maximal ideal.** -/
theorem card_le_finrank (hF : IsFunctionFieldOneVar E F) {s : F} (hs0 : s ≠ 0)
    [FiniteDimensional E⟮s⟯ F] (S : Finset (ValuationSubring F))
    (hS : ∀ O ∈ S, IsPlace E O ∧ O.valuation s < 1) : S.card ≤ Module.finrank E⟮s⟯ F := by
  classical
  -- approximating elements `y O` for `O ∈ S`
  have hy : ∀ O : S, ∃ y : F, O.1.valuation (y - 1) < 1 ∧
      ∀ O' ∈ S.erase O.1, O'.valuation y < 1 := by
    intro ⟨O, hO⟩
    refine exists_valuation_sub_one_lt_one O (S.erase O) fun O' hO' => ?_
    obtain ⟨hne, hO'S⟩ := Finset.mem_erase.mp hO'
    refine ⟨fun hle => hne ((hS O hO).1.eq_of_le hF hle (hS O' hO'S).1.ne_top),
      fun hle => hne ((hS O' hO'S).1.eq_of_le hF hle (hS O hO).1.ne_top).symm⟩
  choose y hy1 hyS using hy
  have hli : LinearIndependent E⟮s⟯ y := by
    rw [linearIndependent_iff']
    intro t g hsum i hi
    by_contra hgi
    set t' := t.filter (fun k => g k ≠ 0) with ht'
    have hit' : i ∈ t' := Finset.mem_filter.mpr ⟨hi, hgi⟩
    have hm : ∀ k : S, ∃ m : ℤ, g k ≠ 0 → ∀ O : ValuationSubring F,
        (∀ c : E, algebraMap E F c ∈ O) → O.valuation s < 1 →
          O.valuation (g k : F) = O.valuation s ^ m := by
      intro k
      by_cases hk : g k = 0
      · exact ⟨0, fun h => (h hk).elim⟩
      · obtain ⟨m, hm⟩ := exists_forall_valuation_eq_zpow hs0 (g k).2 (by simpa using hk)
        exact ⟨m, fun _ => hm⟩
    choose m hm using hm
    obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image t' m ⟨i, hit'⟩
    obtain ⟨hkt, hgk⟩ := Finset.mem_filter.mp hk
    have hgk' : (g k : F) ≠ 0 := by simpa using hgk
    obtain ⟨hOk, hsk⟩ := hS k.1 k.2
    have hσ0 : 0 < k.1.valuation s := (Valuation.pos_iff _).mpr hs0
    set d : S → F := fun j => (g j : F) / (g k : F) with hd
    have hdk : d k = 1 := by simp [hd, div_self hgk']
    have hd1 : ∀ j ∈ t, k.1.valuation (d j) ≤ 1 := by
      intro j hj
      by_cases hgj : g j = 0
      · simp [hd, hgj]
      rw [hd, map_div₀, hm j hgj _ hOk.algebraMap_mem hsk, hm k hgk _ hOk.algebraMap_mem hsk,
        ← zpow_sub₀ hσ0.ne']
      exact (zpow_le_one_iff_right_of_lt_one₀ hσ0 hsk).mpr
        (sub_nonneg.mpr (hkmin j (Finset.mem_filter.mpr ⟨hj, hgj⟩)))
    have hsumd : ∑ j ∈ t, d j * y j = 0 := by
      have : ∑ j ∈ t, d j * y j = (g k : F)⁻¹ * ∑ j ∈ t, g j • y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hd, IntermediateField.smul_def, smul_eq_mul]
        ring
      rw [this, hsum, mul_zero]
    have hlt : k.1.valuation (∑ j ∈ t, d j * y j - 1) < 1 := by
      rw [← Finset.add_sum_erase t _ hkt, hdk, one_mul, add_sub_right_comm]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hy1 k) ?_)
      refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
      obtain ⟨hjk, hjt⟩ := Finset.mem_erase.mp hj
      rw [map_mul]
      have hyj : k.1.valuation (y j) < 1 :=
        hyS j k.1 (Finset.mem_erase.mpr ⟨fun h => hjk (Subtype.ext h).symm, k.2⟩)
      calc k.1.valuation (d j) * k.1.valuation (y j) ≤ 1 * k.1.valuation (y j) := by
            gcongr; exact hd1 j hjt
        _ < 1 := by rw [one_mul]; exact hyj
    rw [hsumd, zero_sub, Valuation.map_neg, map_one] at hlt
    exact lt_irrefl _ hlt
  have := hli.fintype_card_le_finrank
  simpa using this

/-- The places in whose maximal ideal a transcendental element lies form a finite set. -/
theorem finite_setOf_valuation_lt_one (hF : IsFunctionFieldOneVar E F) {s : F}
    (hs : Transcendental E s) :
    {O : ValuationSubring F | IsPlace E O ∧ O.valuation s < 1}.Finite := by
  have := hF.finiteDimensional_adjoin hs
  have hs0 : s ≠ 0 := fun h => hs (h ▸ isAlgebraic_zero)
  by_contra hinf
  obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank E⟮s⟯ F + 1)
  have := card_le_finrank hF hs0 S fun O hO => hSsub hO
  omega

/-- **Finiteness of poles.** Every element has only finitely many poles. -/
theorem finite_setOf_notMem (hF : IsFunctionFieldOneVar E F) (f : F) :
    {O : ValuationSubring F | IsPlace E O ∧ f ∉ O}.Finite := by
  by_cases hf : IsAlgebraic E f
  · convert Set.finite_empty
    ext O
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hO => hO.mem_of_isAlgebraic hf
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  refine (finite_setOf_valuation_lt_one hF (s := f⁻¹)
    (fun h => hf (IsAlgebraic.inv_iff.mp h))).subset fun O ⟨hO, hfO⟩ => ⟨hO, ?_⟩
  have : 1 < O.valuation f := by rw [← not_le, O.valuation_le_one_iff]; exact hfO
  exact (O.valuation.one_lt_val_iff hf0).mp this

end Poles

end DeJongAlterations.StableModification.Valuation.FunctionField

end
