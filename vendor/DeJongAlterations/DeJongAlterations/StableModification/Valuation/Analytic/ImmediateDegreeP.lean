/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Defect
import DeJongAlterations.StableModification.Valuation.Analytic.Hensel
import DeJongAlterations.StableModification.Valuation.Analytic.TypeFour.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Immediate extensions of degree `p` and critical cosets

Let `K` be an analytic field of characteristic `p` and `L/K` a finite immediate extension
(`e_{L/K} = f_{L/K} = 1`). This file attaches to the two kinds of degree-`p` steps occurring in
the towers of `Towers.lean` — purely inseparable steps `L ∋ γ` with `γ ^ p ∈ K`, and
Artin–Schreier steps `L ∋ α` with `α ^ p - α ∈ K` — a special coset of `K` (in the sense of
`Analytic/Cosets.lean`) without minimal element which splits over `L`. This replaces Temkin's
disc argument for Proposition 6.1.4(i) (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `semi-stable.tex` lines 3508–3530 and 3557–3640; plan
simplification S6 of `PLAN-SM-VAL.md`). Radii `r(x) = inf_{c ∈ K} ‖x - c‖` are
`DeJongAlterations.StableModification.Valuation.radius`.

## Main definitions

* `IsImmediate K L`: `e_{L/K} = f_{L/K} = 1`.

## Main results

* `IsImmediate.exists_norm_sub_lt`, `isImmediate_of_forall_exists_norm_sub_lt`: `L/K` is immediate
  iff every `x ≠ 0` is approximated by `c ∈ K` with `‖x - c‖ < ‖x‖`; so radii of elements of
  `L ∖ K` are not attained (`IsImmediate.radius_lt_norm_sub`) and positive
  (`IsImmediate.radius_pos`).
* `one_le_norm_pow_char_sub`, `norm_pow_char_sub_eq_of_pow_char_sub_mem`: Hensel's lemma for
  Artin–Schreier equations.
* `IsImmediate.isSpecialCoset_pow_char` (purely inseparable step),
  `IsImmediate.isSpecialCoset_artinSchreier_one` (Artin–Schreier step of radius `1`),
  `IsImmediate.isSpecialCoset_artinSchreier_zero` (Artin–Schreier step of radius `> 1`),
  `IsImmediate.exists_isSpecialCoset`: **the replacement of Temkin's Proposition 6.1.4(i)**.
* `exists_root_of_isSplitCoset_one`: Temkin's 6.1.4(iii): a split coset `b + S_{1,1}` gives a root
  of `X ^ p - X + b`.

## References

Blueprint chapter `sm-val-cosets-ramif.tex`.
-/

noncomputable section

open IsLocalRing Polynomial
open scoped NNReal

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### Immediate extensions -/

section Immediate

variable (K L : Type*) [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

/-- A finite extension `L/K` of non-archimedean normed fields is **immediate** if its ramification
index and residue degree are both `1`. -/
def IsImmediate : Prop :=
  ramificationIndex K L = 1 ∧ inertiaDegree K L = 1

variable {K L}

omit [NormedAlgebra K L] in
/-- If `e_{L/K} = 1`, every absolute value of `L` is one of `K`. -/
theorem exists_norm_eq_of_ramificationIndex_eq_one (h : ramificationIndex K L = 1) {x : L}
    (hx : x ≠ 0) : ∃ c : K, ‖c‖ = ‖x‖ := by
  have hle : valueGroup L ≤ valueGroup K := Subgroup.relIndex_eq_one.mp h
  have hmem : (Units.mk0 ‖x‖₊ (nnnorm_ne_zero_iff.mpr hx) : ℝ≥0ˣ) ∈ valueGroup L :=
    mem_valueGroup_iff.mpr ⟨x, rfl⟩
  obtain ⟨c, hc⟩ := mem_valueGroup_iff.mp (hle hmem)
  refine ⟨c, ?_⟩
  have : ‖c‖₊ = ‖x‖₊ := hc
  rw [← coe_nnnorm, this, coe_nnnorm]

/-- If `f_{L/K} = 1`, every element of `L°` is congruent modulo `L°°` to an element of `K°`. -/
theorem exists_norm_sub_lt_one_of_inertiaDegree_eq_one (h : inertiaDegree K L = 1) {x : L}
    (hx : ‖x‖ ≤ 1) : ∃ c : K, ‖c‖ ≤ 1 ∧ ‖x - algebraMap K L c‖ < 1 := by
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : ResidueField (unitBall L)) one_ne_zero).mp h
      (residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩)
  obtain ⟨c, rfl⟩ := residue_surjective c
  refine ⟨c, norm_coe_unitBall_le_one c, ?_⟩
  rw [Algebra.smul_def, mul_one, algebraMap_residue, residue_eq_residue_iff] at hc
  rw [norm_sub_rev]
  exact hc

/-- In an immediate extension every `x ≠ 0` is approximated by an element of `K` to within less
than `‖x‖`. -/
theorem IsImmediate.exists_norm_sub_lt (h : IsImmediate K L) {x : L} (hx : x ≠ 0) :
    ∃ c : K, ‖x - algebraMap K L c‖ < ‖x‖ := by
  obtain ⟨c₁, hc₁⟩ := exists_norm_eq_of_ramificationIndex_eq_one h.1 hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hc₁
    exact hxpos.ne hc₁
  have hc₁N : ‖algebraMap K L c₁‖ = ‖x‖ := by rw [norm_algebraMap', hc₁]
  have hc₁N0 : algebraMap K L c₁ ≠ 0 := (_root_.map_ne_zero _).mpr hc₁0
  have hu : ‖x / algebraMap K L c₁‖ ≤ 1 := by
    rw [norm_div, hc₁N, div_self hxpos.ne']
  obtain ⟨c₂, -, hc₂⟩ := exists_norm_sub_lt_one_of_inertiaDegree_eq_one h.2 hu
  refine ⟨c₁ * c₂, ?_⟩
  have heq : x - algebraMap K L (c₁ * c₂) =
      algebraMap K L c₁ * (x / algebraMap K L c₁ - algebraMap K L c₂) := by
    rw [map_mul, mul_sub, mul_div_cancel₀ _ hc₁N0]
  rw [heq, norm_mul, hc₁N]
  calc ‖x‖ * ‖x / algebraMap K L c₁ - algebraMap K L c₂‖ < ‖x‖ * 1 :=
        mul_lt_mul_of_pos_left hc₂ hxpos
    _ = ‖x‖ := mul_one _

/-- Conversely, if every `x ≠ 0` is approximated by `c ∈ K` with `‖x - c‖ < ‖x‖`, then `L/K` is
immediate. -/
theorem isImmediate_of_forall_exists_norm_sub_lt [FiniteDimensional K L]
    (h : ∀ x : L, x ≠ 0 → ∃ c : K, ‖x - algebraMap K L c‖ < ‖x‖) : IsImmediate K L := by
  refine ⟨Subgroup.relIndex_eq_one.mpr fun γ hγ => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := mem_valueGroup_iff.mp hγ
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [nnnorm_zero] at hx
      exact γ.ne_zero hx.symm
    obtain ⟨c, hc⟩ := h x hx0
    have hcx : ‖algebraMap K L c‖ = ‖x‖ := norm_eq_of_norm_sub_lt hc
    rw [norm_algebraMap'] at hcx
    refine mem_valueGroup_iff.mpr ⟨c, ?_⟩
    rw [← hx]
    ext
    simp [hcx]
  · refine (finrank_eq_one_iff_of_nonzero' (1 : ResidueField (unitBall L)) one_ne_zero).mpr
      fun w => ?_
    obtain ⟨y, rfl⟩ := residue_surjective w
    rcases lt_or_eq_of_le (norm_coe_unitBall_le_one y) with hlt | heq
    · refine ⟨0, ?_⟩
      rw [zero_smul, eq_comm, residue_eq_zero_iff_norm_lt_one]
      exact hlt
    · have hy0 : (y : L) ≠ 0 := fun h0 => by rw [h0, norm_zero] at heq; exact zero_ne_one heq
      obtain ⟨c, hc⟩ := h y hy0
      have hcn : ‖c‖ = 1 := by
        have := norm_eq_of_norm_sub_lt hc
        rwa [norm_algebraMap', heq] at this
      refine ⟨residue (unitBall K) ⟨c, mem_unitBall.mpr hcn.le⟩, ?_⟩
      rw [Algebra.smul_def, mul_one, algebraMap_residue, residue_eq_residue_iff,
        coe_algebraMap_unitBall, norm_sub_rev]
      rw [heq] at hc
      exact hc

/-- In an immediate extension, radii of elements of `L ∖ K` are not attained. -/
theorem IsImmediate.exists_norm_sub_lt_norm_sub (h : IsImmediate K L) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (c : K) :
    ∃ c' : K, ‖x - algebraMap K L c'‖ < ‖x - algebraMap K L c‖ := by
  have hxc : x - algebraMap K L c ≠ 0 := fun h0 => hx ⟨c, (sub_eq_zero.mp h0).symm⟩
  obtain ⟨c'', hc''⟩ := h.exists_norm_sub_lt hxc
  refine ⟨c + c'', ?_⟩
  rwa [map_add, ← sub_sub]

theorem IsImmediate.radius_lt_norm_sub (h : IsImmediate K L) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (c : K) : radius K x < ‖x - algebraMap K L c‖ :=
  Valuation.radius_lt_norm_sub (h.exists_norm_sub_lt_norm_sub hx) c

theorem IsImmediate.radius_pos [CompleteSpace K] (h : IsImmediate K L) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) : 0 < radius K x :=
  radius_pos_of_completeSpace (h.exists_norm_sub_lt_norm_sub hx)

end Immediate

/-! ### Infima of powers -/

/-- The infimum of `f i ^ n` is `(inf f) ^ n` for nonnegative `f`. -/
theorem isGLB_range_pow {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    IsGLB (Set.range fun i => f i ^ n) ((⨅ i, f i) ^ n) := by
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨i, rfl⟩; exact hf i⟩
  have hr0 : 0 ≤ ⨅ i, f i := le_ciInf hf
  refine ⟨?_, fun l hl => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact pow_le_pow_left₀ hr0 (ciInf_le hbdd i) n
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.mp (continuous_pow n) (⨅ i, f i)
      (l - (⨅ i, f i) ^ n) (by linarith)
    obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt (f := f) (by linarith : ⨅ i, f i < (⨅ i, f i) + δ)
    have hdist : dist (f i) (⨅ i, f i) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ciInf_le hbdd i]
    have h1 := hcont _ hdist
    rw [Real.dist_eq, abs_lt] at h1
    have h2 := hl ⟨i, rfl⟩
    linarith [h1.2]

/-! ### Artin–Schreier equations and Hensel's lemma -/

section ArtinSchreierHensel

variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ) [hp : Fact p.Prime]
  [CharP F p]

omit [IsUltrametricDist F] in
/-- In characteristic `p` the solutions of `t ^ p = t` are the elements of the prime field. -/
theorem exists_intCast_eq_of_pow_char_eq {t : F} (ht : t ^ p = t) : ∃ n : ℤ, (n : F) = t := by
  have : t ∈ (⊥ : Subfield F) := (Subfield.mem_bot_iff_pow_eq_self F p).mpr ht
  exact (mem_bot_iff_intCast p F).mp this

omit [CharP F p] in
/-- **Hensel's lemma for `X ^ p - X - b`**: for `‖b‖ < 1` in a complete field there is `x ∈ F°`
with `x ^ p - x = b`. -/
theorem exists_pow_char_sub_eq [CompleteSpace F] {b : F} (hb : ‖b‖ < 1) :
    ∃ x : F, ‖x‖ ≤ 1 ∧ x ^ p - x = b := by
  set b₁ : unitBall F := ⟨b, mem_unitBall.mpr hb.le⟩
  set G : (unitBall F)[X] := X ^ p - X - C b₁ with hG_def
  have hGmonic : G.Monic := by
    rw [hG_def, sub_sub]
    refine monic_X_pow_sub ?_
    rw [degree_add_eq_left_of_degree_lt] <;> rw [degree_X]
    · exact_mod_cast hp.out.one_lt
    · exact (degree_C_le).trans_lt (by norm_num)
  have hG0 : ‖((G.eval 0 : unitBall F) : F)‖ < 1 := by
    simpa [hG_def, zero_pow hp.out.ne_zero, b₁] using hb
  have hGd : IsUnit (G.derivative.eval 0) := by
    rw [isUnit_unitBall_iff]
    simp [hG_def, derivative_X_pow, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt)]
  obtain ⟨x, hx, -⟩ := exists_isRoot_norm_sub_le G hGmonic 0 hG0 hGd
  refine ⟨x, norm_coe_unitBall_le_one x, ?_⟩
  have := congrArg Subtype.val hx.eq_zero
  simp only [hG_def, eval_sub, eval_pow, eval_X, eval_C] at this
  push_cast at this
  linear_combination this

/-- **Split cosets with `a = 1` give roots** (Temkin, Proposition 6.1.4(iii), characteristic
`p`): if `b + S_{1,1}(F)` is split, `X ^ p - X + b` has a root in `F`. -/
theorem exists_root_of_isSplitCoset_one [CompleteSpace F] {b : F}
    (h : IsSplitCoset p (1 : F) 1 b) : ∃ x : F, x ^ p - x + b = 0 := by
  obtain ⟨c, d, hd, hcd⟩ := h
  rw [asMap_one_left] at hcd
  obtain ⟨x₀, -, hx₀⟩ := exists_pow_char_sub_eq p hd
  refine ⟨x₀ + c, ?_⟩
  rw [add_pow_char]
  linear_combination hx₀ + hcd

end ArtinSchreierHensel

section ASNorm

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedField L]
  [IsUltrametricDist L] [NormedAlgebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

omit [IsUltrametricDist L] in
/-- **Hensel's lemma for Artin–Schreier equations**: if `y ∉ K` and `y ^ p - y ∈ K`, then
`‖y ^ p - y‖ ≥ 1`. -/
theorem one_le_norm_pow_char_sub {y : L} (hy : y ∉ Set.range (algebraMap K L)) {b : K}
    (hb : algebraMap K L b = y ^ p - y) : 1 ≤ ‖y ^ p - y‖ := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  by_contra hlt
  rw [not_le, ← hb, norm_algebraMap'] at hlt
  obtain ⟨x, -, hx⟩ := exists_pow_char_sub_eq p hlt
  have ht : (y - algebraMap K L x) ^ p = y - algebraMap K L x := by
    rw [sub_pow_char, ← map_pow]
    have : x ^ p = x + b := by rw [← hx]; ring
    rw [this, map_add, hb]
    ring
  obtain ⟨n, hn⟩ := exists_intCast_eq_of_pow_char_eq p ht
  exact hy ⟨x + n, by rw [map_add, map_intCast, hn]; ring⟩

/-- If `y ∉ K` and `y ^ p - y ∈ K`, then `‖y‖ ≥ 1`. -/
theorem one_le_norm_of_pow_char_sub_mem {y : L} (hy : y ∉ Set.range (algebraMap K L)) {b : K}
    (hb : algebraMap K L b = y ^ p - y) : 1 ≤ ‖y‖ := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := one_le_norm_pow_char_sub p hy hb
  have : ‖y ^ p - y‖ < 1 := by
    refine (norm_sub_le_max _ _).trans_lt (max_lt ?_ hlt)
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hlt hp.out.ne_zero
  linarith

/-- If `y ∉ K` and `y ^ p - y ∈ K`, then `‖y ^ p - y‖ = ‖y‖ ^ p`. -/
theorem norm_pow_char_sub_eq_of_pow_char_sub_mem {y : L} (hy : y ∉ Set.range (algebraMap K L))
    {b : K} (hb : algebraMap K L b = y ^ p - y) : ‖y ^ p - y‖ = ‖y‖ ^ p := by
  have h1 := one_le_norm_of_pow_char_sub_mem p hy hb
  rcases lt_or_eq_of_le h1 with hgt | heq
  · have hlt : ‖y‖ < ‖y ^ p‖ := by
      rw [norm_pow]
      exact lt_self_pow₀ hgt hp.out.one_lt
    rw [← norm_pow, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hlt.ne'),
      norm_neg, max_eq_left hlt.le]
  · have h2 := one_le_norm_pow_char_sub p hy hb
    have h3 : ‖y ^ p - y‖ ≤ 1 := by
      refine (norm_sub_le_max _ _).trans (max_le ?_ heq.symm.le)
      rw [norm_pow, ← heq, one_pow]
    rw [← heq, one_pow]
    exact le_antisymm h3 h2

end ASNorm

/-! ### The coset attached to an immediate step of degree `p` -/

section Coset

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

omit [IsUltrametricDist L] in
/-- A critical coset whose absolute values are `p`-th powers of distances to an element whose
radius is not attained has no minimal element. -/
theorem not_exists_isMinimalInCoset_of_forall_norm_eq {a b : K} {x : L}
    (hcrit : IsCriticalCoset p a (radius K x ^ p) b)
    (hφ : ∀ c : K, ∃ c' : K, ‖asMap p a c + b‖ = ‖x - algebraMap K L c'‖ ^ p)
    (hna : ∀ c' : K, radius K x < ‖x - algebraMap K L c'‖) :
    ¬ ∃ y, IsMinimalInCoset p a (radius K x ^ p) b y := by
  rintro ⟨y, hy⟩
  have hys : ‖y‖ = radius K x ^ p := hcrit.norm_eq_of_isMinimalInCoset hy
  obtain ⟨c, d, hd, hcd⟩ := hy.1
  have hyd : ‖y - d‖ = ‖y‖ := by
    have := norm_eq_of_norm_sub_lt (x := y) (y := y - d) (by rwa [sub_sub_cancel, hys])
    exact this
  obtain ⟨c', hc'⟩ := hφ c
  have heq : asMap p a c + b = y - d := by linear_combination hcd
  rw [heq, hyd, hys] at hc'
  have := (pow_left_inj₀ (radius_nonneg x) (norm_nonneg _) hp.out.ne_zero).mp hc'
  exact (hna c').ne this

variable [CompleteSpace K]

/-- **The purely inseparable step** (replaces Temkin, Proposition 6.1.4(i), inseparable case):
if `L/K` is immediate, `γ ∈ L ∖ K` and `β = γ ^ p ∈ K`, then with `s = r(γ) ^ p` the coset
`-β + S_{0,s}(K)` is special, has no minimal element, and splits over `L`. -/
theorem IsImmediate.isSpecialCoset_pow_char (h : IsImmediate K L) {γ : L}
    (hγ : γ ∉ Set.range (algebraMap K L)) {β : K} (hβ : algebraMap K L β = γ ^ p) :
    IsSpecialCoset p 0 (radius K γ ^ p) (-β) ∧
      (¬ ∃ x, IsMinimalInCoset p 0 (radius K γ ^ p) (-β) x) ∧
      IsSplitCoset p (0 : L) (radius K γ ^ p) (algebraMap K L (-β)) := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hr := h.radius_pos hγ
  have hs : 0 < radius K γ ^ p := pow_pos hr p
  have hnorm : ∀ c : K, ‖asMap p 0 c + -β‖ = ‖γ - algebraMap K L c‖ ^ p := by
    intro c
    rw [asMap_zero_left, ← norm_algebraMap' L, map_add, map_neg, map_pow, hβ, ← sub_eq_add_neg,
      ← sub_pow_char, norm_pow, norm_sub_rev]
  have hcrit : IsCriticalCoset p 0 (radius K γ ^ p) (-β) := by
    rw [isCriticalCoset_iff_isGLB hs]
    have hfun : (fun c => ‖asMap p 0 c + -β‖) = fun c => ‖γ - algebraMap K L c‖ ^ p :=
      funext hnorm
    rw [hfun]
    exact isGLB_range_pow _ (fun _ => norm_nonneg _) p
  refine ⟨⟨hcrit, Or.inl rfl⟩, not_exists_isMinimalInCoset_of_forall_norm_eq p hcrit
    (fun c => ⟨c, hnorm c⟩) (h.radius_lt_norm_sub hγ), ?_⟩
  refine ⟨γ, 0, by rw [norm_zero]; exact hs, ?_⟩
  rw [asMap_zero_left, map_neg, ← hβ]
  ring

/-- **Artin–Schreier steps**: if `α ∈ L ∖ K` and `β = α ^ p - α ∈ K`, then `r(α) ≥ 1` and
`‖c ^ p - c - β‖ = ‖α - c‖ ^ p` for all `c ∈ K`. -/
theorem one_le_radius_of_artinSchreier {α : L}
    (hα : α ∉ Set.range (algebraMap K L)) {β : K} (hβ : algebraMap K L β = α ^ p - α) :
    1 ≤ radius K α ∧ ∀ c : K, ‖c ^ p - c - β‖ = ‖α - algebraMap K L c‖ ^ p := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hmem : ∀ c : K, algebraMap K L (β - (c ^ p - c)) =
      (α - algebraMap K L c) ^ p - (α - algebraMap K L c) := by
    intro c
    rw [map_sub, map_sub, map_pow, hβ, sub_pow_char]
    ring
  have hnot : ∀ c : K, α - algebraMap K L c ∉ Set.range (algebraMap K L) := by
    rintro c ⟨c', hc'⟩
    exact hα ⟨c' + c, by rw [map_add, hc']; ring⟩
  refine ⟨le_ciInf fun c => one_le_norm_of_pow_char_sub_mem p (hnot c) (hmem c), fun c => ?_⟩
  rw [← norm_pow_char_sub_eq_of_pow_char_sub_mem p (hnot c) (hmem c), ← hmem c, norm_algebraMap',
    ← norm_neg]
  congr 1
  ring

/-- **The Artin–Schreier step of radius `1`**: the coset `-β + S_{1,1}(K)` is special, has no
minimal element, and splits over `L`. -/
theorem IsImmediate.isSpecialCoset_artinSchreier_one (h : IsImmediate K L) {α : L}
    (hα : α ∉ Set.range (algebraMap K L)) {β : K} (hβ : algebraMap K L β = α ^ p - α)
    (hr : radius K α = 1) :
    IsSpecialCoset p 1 1 (-β) ∧ (¬ ∃ x, IsMinimalInCoset p 1 1 (-β) x) ∧
      IsSplitCoset p (1 : L) 1 (algebraMap K L (-β)) := by
  obtain ⟨-, hnorm⟩ := one_le_radius_of_artinSchreier p hα hβ
  have hnorm' : ∀ c : K, ‖asMap p 1 c + -β‖ = ‖α - algebraMap K L c‖ ^ p := by
    intro c
    rw [asMap_one_left, ← hnorm c]
    ring_nf
  have hs : radius K α ^ p = 1 := by rw [hr, one_pow]
  have hcrit : IsCriticalCoset p 1 (radius K α ^ p) (-β) := by
    rw [isCriticalCoset_iff_isGLB (by rw [hs]; exact one_pos)]
    have hfun : (fun c => ‖asMap p 1 c + -β‖) = fun c => ‖α - algebraMap K L c‖ ^ p :=
      funext hnorm'
    rw [hfun]
    exact isGLB_range_pow _ (fun _ => norm_nonneg _) p
  have hmin := not_exists_isMinimalInCoset_of_forall_norm_eq p hcrit
    (fun c => ⟨c, hnorm' c⟩) (h.radius_lt_norm_sub hα)
  rw [hs] at hcrit hmin
  refine ⟨⟨hcrit, Or.inr ⟨rfl, rfl⟩⟩, hmin, ?_⟩
  refine ⟨α, 0, by rw [norm_zero]; exact one_pos, ?_⟩
  rw [asMap_one_left, map_neg, hβ]
  ring

/-- **The Artin–Schreier step of radius `> 1`**: if `r = r(α) > 1`, `s = r ^ p` and
`‖α - c₀‖ < s`, then with `β₀ = β - (c₀ ^ p - c₀)` the coset `-β₀ + S_{0,s}(K)` is special, has no
minimal element, and splits over `L`. -/
theorem IsImmediate.isSpecialCoset_artinSchreier_zero (h : IsImmediate K L) {α : L}
    (hα : α ∉ Set.range (algebraMap K L)) {β : K} (hβ : algebraMap K L β = α ^ p - α)
    {c₀ : K} (hc₀ : ‖α - algebraMap K L c₀‖ < radius K α ^ p) :
    IsSpecialCoset p 0 (radius K α ^ p) (-(β - (c₀ ^ p - c₀))) ∧
      (¬ ∃ x, IsMinimalInCoset p 0 (radius K α ^ p) (-(β - (c₀ ^ p - c₀))) x) ∧
      IsSplitCoset p (0 : L) (radius K α ^ p) (algebraMap K L (-(β - (c₀ ^ p - c₀)))) := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set α₀ := α - algebraMap K L c₀ with hα₀_def
  set β₀ := β - (c₀ ^ p - c₀) with hβ₀_def
  have hβ₀ : algebraMap K L β₀ = α₀ ^ p - α₀ := by
    rw [hβ₀_def, hα₀_def, map_sub, map_sub, map_pow, hβ, sub_pow_char]
    ring
  have hr := h.radius_pos hα
  have hs : 0 < radius K α ^ p := pow_pos hr p
  have hnorm : ∀ c : K, ‖asMap p 0 c + -β₀‖ = ‖α - algebraMap K L (c₀ + c)‖ ^ p := by
    intro c
    have hid : algebraMap K L c - α₀ = -(α - algebraMap K L (c₀ + c)) := by
      rw [hα₀_def, map_add]
      ring
    have hfar : ‖α₀‖ < ‖(algebraMap K L c - α₀) ^ p‖ := by
      rw [hid, norm_pow, norm_neg]
      exact hc₀.trans_le (pow_le_pow_left₀ (radius_nonneg α) (radius_le α _) p)
    have heq : algebraMap K L (asMap p 0 c + -β₀) = (algebraMap K L c - α₀) ^ p + α₀ := by
      rw [asMap_zero_left, map_add, map_neg, map_pow, hβ₀, sub_pow_char (algebraMap K L c) α₀]
      ring
    rw [← norm_algebraMap' L, heq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hfar.ne',
      max_eq_left hfar.le, hid, norm_pow, norm_neg]
  have hrange : (Set.range fun c => ‖α - algebraMap K L (c₀ + c)‖ ^ p) =
      Set.range fun c => ‖α - algebraMap K L c‖ ^ p := by
    ext t
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c₀ + c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c - c₀, by simp⟩
  have hcrit : IsCriticalCoset p 0 (radius K α ^ p) (-β₀) := by
    rw [isCriticalCoset_iff_isGLB hs]
    have hfun : (fun c => ‖asMap p 0 c + -β₀‖) = fun c => ‖α - algebraMap K L (c₀ + c)‖ ^ p :=
      funext hnorm
    rw [hfun, hrange]
    exact isGLB_range_pow _ (fun _ => norm_nonneg _) p
  refine ⟨⟨hcrit, Or.inl rfl⟩, not_exists_isMinimalInCoset_of_forall_norm_eq p hcrit
    (fun c => ⟨c₀ + c, hnorm c⟩) (h.radius_lt_norm_sub hα), ?_⟩
  refine ⟨α₀, -α₀, by rw [norm_neg]; exact hc₀, ?_⟩
  rw [asMap_zero_left, map_neg, hβ₀]
  ring

/-- **Immediate degree-`p` steps give special cosets without minimal element** (the replacement
of Temkin's Proposition 6.1.4(i)): if `L/K` is immediate and contains `γ ∉ K` with `γ ^ p ∈ K`,
or `α ∉ K` with `α ^ p - α ∈ K`, then `K` has a special coset without minimal element which
splits over `L`. -/
theorem IsImmediate.exists_isSpecialCoset (h : IsImmediate K L)
    (hstep : (∃ γ : L, γ ∉ Set.range (algebraMap K L) ∧ γ ^ p ∈ Set.range (algebraMap K L)) ∨
      (∃ α : L, α ∉ Set.range (algebraMap K L) ∧ α ^ p - α ∈ Set.range (algebraMap K L))) :
    ∃ (a : K) (s : ℝ) (b : K), (a = 0 ∨ (a = 1 ∧ s = 1)) ∧ IsSpecialCoset p a s b ∧
      (¬ ∃ x, IsMinimalInCoset p a s b x) ∧
      IsSplitCoset p (algebraMap K L a) s (algebraMap K L b) := by
  rcases hstep with ⟨γ, hγ, β, hβ⟩ | ⟨α, hα, β, hβ⟩
  · obtain ⟨h1, h2, h3⟩ := h.isSpecialCoset_pow_char p hγ hβ
    exact ⟨0, _, _, Or.inl rfl, h1, h2, by rwa [map_zero]⟩
  · obtain ⟨hr1, -⟩ := one_le_radius_of_artinSchreier p hα hβ
    rcases lt_or_eq_of_le hr1 with hr | hr
    · have hlt : radius K α < radius K α ^ p := lt_self_pow₀ hr (Fact.out : p.Prime).one_lt
      obtain ⟨c₀, hc₀⟩ := exists_norm_sub_lt_of_radius_lt hlt
      obtain ⟨h1, h2, h3⟩ := h.isSpecialCoset_artinSchreier_zero p hα hβ hc₀
      exact ⟨0, _, _, Or.inl rfl, h1, h2, by rwa [map_zero]⟩
    · obtain ⟨h1, h2, h3⟩ := h.isSpecialCoset_artinSchreier_one p hα hβ hr.symm
      exact ⟨1, 1, _, Or.inr ⟨rfl, rfl⟩, h1, h2, by rwa [map_one]⟩

end Coset

end DeJongAlterations.StableModification.Valuation.Analytic
