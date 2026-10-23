import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Critical cosets in characteristic `p`

This file sets up the cosets of Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), §6.1 (`semi-stable.tex`, lines 3435–3500), for a field `K` of
characteristic `p` with a non-archimedean absolute value (Lean: `[NormedField K]
[IsUltrametricDist K] [CharP K p]`). Completeness is not assumed.

For `a ∈ K` and `s : ℝ`, Temkin's group is
`S_{a,s}(K) = {c ^ p - a c + d : c, d ∈ K, ‖d‖ < s}`; in characteristic `p` the condition
`|p c ^ p| < s` of the source is vacuous and the map `℘_a : c ↦ c ^ p - a c` is additive, so
`S_{a,s}(K)` is an additive subgroup as soon as `s > 0`. A coset `b + S_{a,s}(K)` is *split* if it
contains `0`, *critical* if `s > 0`, it is not split and `inf ‖b + S_{a,s}(K)‖ ≤ s` (equivalently
`= s`), and *special* if it is critical and `a = 0`, or `a = 1` and `s = 1`.

## Main definitions

* `asMap p a c = c ^ p - a * c`: the twisted Artin–Schreier map `℘_a`.
* `asSet p a s`: the set `S_{a,s}(K)`; `asAddSubgroup p a hs` is the same set as an
  `AddSubgroup` (for `0 < s`, in characteristic `p`).
* `MemCoset p a s b x`: `x ∈ b + S_{a,s}(K)`.
* `IsSplitCoset`, `IsCriticalCoset`, `IsSpecialCoset`: Temkin's split, critical and special
  cosets; `IsMinimalInCoset p a s b x`: `x` is an element of minimal absolute value of the coset.

## Main results

* `asMap_add`, `asAddSubgroup`: `℘_a` is additive and `S_{a,s}(K)` is a group.
* `MemCoset.memCoset_iff` and the `MemCoset.*_iff` lemmas: cosets of elements of a coset agree,
  so all notions depend only on the coset.
* `isSplitCoset_iff`, `le_norm_of_not_isSplitCoset`, `isCriticalCoset_iff_isGLB`: Temkin's
  Lemma 6.1.2(i) in characteristic `p`: a coset is critical iff `s = inf_c ‖℘_a(c) + b‖`.
* `exists_mem_memCoset_of_dense`, `IsCriticalCoset.exists_mem_dense`: approximation of coset
  elements by elements of a dense subset.
* `IsSpecialCoset.isMinimalInCoset_of_orthogonal`: an element of a special coset that is
  orthogonal to `K ^ p` is minimal (extracted from Temkin's proof of Proposition 6.2.4 for types 2
  and 3, lines 3958–3964); `IsCriticalCoset.norm_eq_of_isMinimalInCoset`: minimal elements of a
  critical coset have absolute value `s`.

## References

The blueprint chapter `sm-val-cosets.tex` (nodes `def:sm-an-coset`, `lem:sm-an-coset-group`,
`lem:sm-an-critical-coset-charp`, `lem:sm-an-coset-dense`, `lem:sm-an-coset-orthogonal`).
-/

noncomputable section

open IsUltrametricDist

namespace DeJongAlterations.StableModification.Valuation

/-! ### Non-archimedean inequalities for differences -/

section Ultra

variable {E : Type*} [SeminormedAddGroup E] [IsUltrametricDist E]

/-- The non-archimedean triangle inequality for differences. -/
theorem norm_sub_le_max_norm (x y : E) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using norm_add_le_max x (-y)

/-- In a non-archimedean group, `‖x - y‖ = max ‖x‖ ‖y‖` when `‖x‖ ≠ ‖y‖`. -/
theorem norm_sub_eq_max_norm_of_ne {x y : E} (h : ‖x‖ ≠ ‖y‖) : ‖x - y‖ = max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max_of_norm_ne_norm (y := -y) (by simpa using h)

/-- If `‖x - y‖ < ‖x‖` then `‖y‖ = ‖x‖` (non-archimedean). -/
theorem norm_eq_of_norm_sub_lt_norm {x y : E} (h : ‖x - y‖ < ‖x‖) : ‖y‖ = ‖x‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [norm_sub_eq_max_norm_of_ne hlt.ne', max_eq_left hlt.le] at h
    exact lt_irrefl _ h
  · rw [norm_sub_eq_max_norm_of_ne hlt.ne, max_eq_right hlt.le] at h
    exact lt_irrefl _ (h.trans hlt)

end Ultra

variable {K : Type*} [NormedField K] (p : ℕ)

/-- The twisted Artin–Schreier map `℘_a(c) = c ^ p - a * c` of Temkin §6.1. -/
def asMap (a c : K) : K := c ^ p - a * c

/-- Temkin's set `S_{a,s}(K) = {c ^ p - a c + d : c, d ∈ K, ‖d‖ < s}` (§6.1, characteristic
`p`). It is an additive subgroup when `0 < s` (`asAddSubgroup`). -/
def asSet (a : K) (s : ℝ) : Set K := {x | ∃ c d : K, ‖d‖ < s ∧ asMap p a c + d = x}

/-- `MemCoset p a s b x`: the element `x` lies in the coset `b + S_{a,s}(K)`. -/
def MemCoset (a : K) (s : ℝ) (b x : K) : Prop := x - b ∈ asSet p a s

/-- The coset `b + S_{a,s}(K)` is *split* if it contains `0`. -/
def IsSplitCoset (a : K) (s : ℝ) (b : K) : Prop := MemCoset p a s b 0

/-- The coset `b + S_{a,s}(K)` is *critical* (Temkin §6.1): `s > 0`, it is not split, and it
contains elements of absolute value arbitrarily close to `s`. Since a non-split coset has no
element of absolute value `< s` (`le_norm_of_not_isSplitCoset`), the last condition says that the
infimum of the absolute values of its elements is `s`. -/
def IsCriticalCoset (a : K) (s : ℝ) (b : K) : Prop :=
  0 < s ∧ ¬ IsSplitCoset p a s b ∧ ∀ t, s < t → ∃ x, MemCoset p a s b x ∧ ‖x‖ < t

/-- The coset `b + S_{a,s}(K)` is *special* (Temkin §6.1): it is critical, and either `a = 0`, or
`a = 1` and `s = 1`. -/
def IsSpecialCoset (a : K) (s : ℝ) (b : K) : Prop :=
  IsCriticalCoset p a s b ∧ (a = 0 ∨ (a = 1 ∧ s = 1))

/-- `x` is an element of minimal absolute value of the coset `b + S_{a,s}(K)`. -/
def IsMinimalInCoset (a : K) (s : ℝ) (b x : K) : Prop :=
  MemCoset p a s b x ∧ ∀ y, MemCoset p a s b y → ‖x‖ ≤ ‖y‖

variable {p}

theorem asMap_zero_left (c : K) : asMap p 0 c = c ^ p := by simp [asMap]

theorem asMap_one_left (c : K) : asMap p 1 c = c ^ p - c := by simp [asMap]

theorem MemCoset.pos {a : K} {s : ℝ} {b x : K} (h : MemCoset p a s b x) : 0 < s := by
  obtain ⟨c, d, hd, -⟩ := h
  exact (norm_nonneg d).trans_lt hd

theorem IsCriticalCoset.pos {a : K} {s : ℝ} {b : K} (h : IsCriticalCoset p a s b) : 0 < s := h.1

theorem IsCriticalCoset.not_isSplitCoset {a : K} {s : ℝ} {b : K} (h : IsCriticalCoset p a s b) :
    ¬ IsSplitCoset p a s b := h.2.1

theorem IsCriticalCoset.exists_norm_lt {a : K} {s : ℝ} {b : K} (h : IsCriticalCoset p a s b)
    {t : ℝ} (ht : s < t) : ∃ x, MemCoset p a s b x ∧ ‖x‖ < t := h.2.2 t ht

theorem IsSpecialCoset.isCriticalCoset {a : K} {s : ℝ} {b : K} (h : IsSpecialCoset p a s b) :
    IsCriticalCoset p a s b := h.1

theorem asMap_mem_asSet {a : K} {s : ℝ} (hs : 0 < s) (c : K) : asMap p a c ∈ asSet p a s :=
  ⟨c, 0, by simpa using hs, by simp⟩

theorem continuous_asMap (a : K) : Continuous (asMap p a) :=
  (continuous_pow p).sub (continuous_const.mul continuous_id)

/-! ### Characteristic `p`: the group `S_{a,s}(K)` -/

section CharP

variable [Fact p.Prime]

@[simp]
theorem asMap_zero (a : K) : asMap p a 0 = 0 := by
  simp [asMap, (Fact.out : p.Prime).ne_zero]

theorem mem_asSet_of_norm_lt {a d : K} {s : ℝ} (hd : ‖d‖ < s) : d ∈ asSet p a s :=
  ⟨0, d, hd, by simp⟩

theorem zero_mem_asSet {a : K} {s : ℝ} (hs : 0 < s) : (0 : K) ∈ asSet p a s :=
  mem_asSet_of_norm_lt (by simpa using hs)

variable [CharP K p]

theorem asMap_add (a c c' : K) : asMap p a (c + c') = asMap p a c + asMap p a c' := by
  simp only [asMap, add_pow_char]
  ring

theorem asMap_neg (a c : K) : asMap p a (-c) = -asMap p a c := by
  have h := asMap_add a c (-c)
  rw [add_neg_cancel, asMap_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem asMap_sub (a c c' : K) : asMap p a (c - c') = asMap p a c - asMap p a c' := by
  rw [sub_eq_add_neg, asMap_add, asMap_neg, ← sub_eq_add_neg]

/-- `℘_a` as an additive group homomorphism (characteristic `p`). -/
def asMapHom (a : K) : K →+ K where
  toFun := asMap p a
  map_zero' := asMap_zero a
  map_add' := asMap_add a

@[simp]
theorem asMapHom_apply (a c : K) : asMapHom (p := p) a c = asMap p a c := rfl

theorem neg_mem_asSet {a x : K} {s : ℝ} (hx : x ∈ asSet p a s) : -x ∈ asSet p a s := by
  obtain ⟨c, d, hd, rfl⟩ := hx
  exact ⟨-c, -d, by simpa using hd, by rw [asMap_neg]; ring⟩

variable [IsUltrametricDist K]

theorem add_mem_asSet {a x y : K} {s : ℝ} (hx : x ∈ asSet p a s) (hy : y ∈ asSet p a s) :
    x + y ∈ asSet p a s := by
  obtain ⟨c, d, hd, rfl⟩ := hx
  obtain ⟨c', d', hd', rfl⟩ := hy
  refine ⟨c + c', d + d', (norm_add_le_max d d').trans_lt (max_lt hd hd'), ?_⟩
  rw [asMap_add]
  ring

theorem sub_mem_asSet {a x y : K} {s : ℝ} (hx : x ∈ asSet p a s) (hy : y ∈ asSet p a s) :
    x - y ∈ asSet p a s := by
  rw [sub_eq_add_neg]
  exact add_mem_asSet hx (neg_mem_asSet hy)

/-- Temkin's `S_{a,s}(K)` as an additive subgroup of `K` (characteristic `p`, `0 < s`). -/
def asAddSubgroup (a : K) {s : ℝ} (hs : 0 < s) : AddSubgroup K where
  carrier := asSet p a s
  zero_mem' := zero_mem_asSet hs
  add_mem' := add_mem_asSet
  neg_mem' := neg_mem_asSet

@[simp]
theorem coe_asAddSubgroup (a : K) {s : ℝ} (hs : 0 < s) :
    (asAddSubgroup (p := p) a hs : Set K) = asSet p a s := rfl

theorem asMapHom_range_le (a : K) {s : ℝ} (hs : 0 < s) :
    (asMapHom (p := p) a).range ≤ asAddSubgroup a hs := by
  rintro _ ⟨c, rfl⟩
  exact asMap_mem_asSet hs c

/-! ### Cosets -/

variable {a : K} {s : ℝ} {b x y : K}

omit [CharP K p] [IsUltrametricDist K] in
theorem memCoset_self (hs : 0 < s) (b : K) : MemCoset p a s b b := by
  simpa [MemCoset] using zero_mem_asSet (p := p) (a := a) hs

/-- If `x ∈ b + S_{a,s}(K)` then `x + S_{a,s}(K) = b + S_{a,s}(K)`. -/
theorem MemCoset.memCoset_iff (hx : MemCoset p a s b x) :
    MemCoset p a s x y ↔ MemCoset p a s b y := by
  unfold MemCoset at *
  constructor
  · intro hy
    simpa using add_mem_asSet hy hx
  · intro hy
    simpa using sub_mem_asSet hy hx

theorem MemCoset.symm (hx : MemCoset p a s b x) : MemCoset p a s x b :=
  hx.memCoset_iff.mpr (memCoset_self hx.pos b)

theorem MemCoset.trans (hx : MemCoset p a s b x) (hy : MemCoset p a s x y) :
    MemCoset p a s b y :=
  hx.memCoset_iff.mp hy

theorem MemCoset.add_mem (hx : MemCoset p a s b x) {y : K} (hy : y ∈ asSet p a s) :
    MemCoset p a s b (x + y) := by
  unfold MemCoset at *
  simpa [add_sub_right_comm] using add_mem_asSet hx hy

theorem MemCoset.add_asMap (hx : MemCoset p a s b x) (c : K) :
    MemCoset p a s b (x + asMap p a c) :=
  hx.add_mem (asMap_mem_asSet hx.pos c)

theorem MemCoset.sub_asMap (hx : MemCoset p a s b x) (c : K) :
    MemCoset p a s b (x - asMap p a c) := by
  simpa [sub_eq_add_neg, asMap_neg] using hx.add_asMap (-c)

theorem MemCoset.add_of_norm_lt (hx : MemCoset p a s b x) {d : K} (hd : ‖d‖ < s) :
    MemCoset p a s b (x + d) :=
  hx.add_mem (mem_asSet_of_norm_lt hd)

theorem MemCoset.sub_of_norm_lt (hx : MemCoset p a s b x) {d : K} (hd : ‖d‖ < s) :
    MemCoset p a s b (x - d) := by
  simpa [sub_eq_add_neg] using hx.add_of_norm_lt (d := -d) (by simpa using hd)

theorem MemCoset.isSplitCoset_iff (hx : MemCoset p a s b x) :
    IsSplitCoset p a s x ↔ IsSplitCoset p a s b :=
  hx.memCoset_iff

theorem MemCoset.isCriticalCoset_iff (hx : MemCoset p a s b x) :
    IsCriticalCoset p a s x ↔ IsCriticalCoset p a s b := by
  unfold IsCriticalCoset
  simp only [hx.isSplitCoset_iff, hx.memCoset_iff]

theorem MemCoset.isSpecialCoset_iff (hx : MemCoset p a s b x) :
    IsSpecialCoset p a s x ↔ IsSpecialCoset p a s b := by
  unfold IsSpecialCoset
  rw [hx.isCriticalCoset_iff]

theorem MemCoset.isMinimalInCoset_iff (hx : MemCoset p a s b x) :
    IsMinimalInCoset p a s x y ↔ IsMinimalInCoset p a s b y := by
  unfold IsMinimalInCoset
  simp only [hx.memCoset_iff]

/-! ### Temkin's Lemma 6.1.2(i) in characteristic `p` -/

/-- A coset is split iff it contains an element of absolute value `< s`. -/
theorem isSplitCoset_iff : IsSplitCoset p a s b ↔ ∃ x, MemCoset p a s b x ∧ ‖x‖ < s := by
  constructor
  · intro h
    exact ⟨0, h, by simpa using h.pos⟩
  · rintro ⟨x, hx, hxs⟩
    simpa [IsSplitCoset] using hx.sub_of_norm_lt hxs

/-- Every element of a non-split coset has absolute value at least `s`. -/
theorem le_norm_of_not_isSplitCoset (h : ¬ IsSplitCoset p a s b) (hx : MemCoset p a s b x) :
    s ≤ ‖x‖ := by
  by_contra hlt
  exact h (isSplitCoset_iff.mpr ⟨x, hx, not_le.mp hlt⟩)

/-- In a non-split coset, adding an element of absolute value `< s` does not change the absolute
value. -/
theorem norm_add_eq_of_not_isSplitCoset (h : ¬ IsSplitCoset p a s b) (hx : MemCoset p a s b x)
    {d : K} (hd : ‖d‖ < s) : ‖x + d‖ = ‖x‖ := by
  have hlt : ‖d‖ < ‖x‖ := hd.trans_le (le_norm_of_not_isSplitCoset h hx)
  rw [norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- **Temkin, Lemma 6.1.2(i)** (characteristic `p`): for `s > 0`, the coset `b + S_{a,s}(K)` is
critical iff `s = inf_{c ∈ K} ‖℘_a(c) + b‖`. -/
theorem isCriticalCoset_iff_isGLB (hs : 0 < s) :
    IsCriticalCoset p a s b ↔ IsGLB (Set.range fun c => ‖asMap p a c + b‖) s := by
  constructor
  · rintro ⟨-, hns, hinf⟩
    refine ⟨?_, fun l hl => ?_⟩
    · rintro _ ⟨c, rfl⟩
      refine le_norm_of_not_isSplitCoset hns ?_
      simpa [add_comm] using (memCoset_self hs b).add_asMap (a := a) c
    · by_contra hls
      obtain ⟨x, ⟨c, d, hd, hx⟩, hxl⟩ := hinf l (not_le.mp hls)
      have hx' : asMap p a c + b = x - d := by linear_combination hx
      have : ‖asMap p a c + b‖ < l := by
        rw [hx']
        exact (norm_sub_le_max_norm x d).trans_lt (max_lt hxl (hd.trans (not_le.mp hls)))
      exact (lt_irrefl _ (this.trans_le (hl ⟨c, rfl⟩)))
  · intro h
    refine ⟨hs, ?_, fun t ht => ?_⟩
    · rintro ⟨c, d, hd, hx⟩
      have hx' : asMap p a c + b = -d := by
        have : asMap p a c + d = -b := by simpa using hx
        linear_combination this
      have := h.1 ⟨c, rfl⟩
      simp only at this
      rw [hx', norm_neg] at this
      exact lt_irrefl _ (hd.trans_le this)
    · obtain ⟨_, ⟨c, rfl⟩, -, hct⟩ := h.exists_between ht
      refine ⟨asMap p a c + b, ?_, hct⟩
      simpa [add_comm] using (memCoset_self hs b).add_asMap (a := a) c

/-! ### Approximation by a dense subset -/

/-- A nonempty coset meets every dense subset. -/
theorem exists_mem_memCoset_of_dense {A : Set K} (hA : Dense A) (hx : MemCoset p a s b x) :
    ∃ y ∈ A, MemCoset p a s b y := by
  obtain ⟨y, hyA, hxy⟩ := hA.exists_dist_lt x hx.pos
  refine ⟨y, hyA, ?_⟩
  have := hx.add_of_norm_lt (d := y - x) (by rwa [dist_eq_norm, norm_sub_rev] at hxy)
  simpa using this

omit [Fact (Nat.Prime p)] [CharP K p] in
/-- In a critical coset `b + S_{a,s}(K)`, for every `t > s` there are `c, d` in a given dense
subset with `‖d‖ < s` and `‖b + ℘_a(c) + d‖ < t`. -/
theorem IsCriticalCoset.exists_mem_dense (h : IsCriticalCoset p a s b) {A : Set K}
    (hA : Dense A) {t : ℝ} (ht : s < t) :
    ∃ c ∈ A, ∃ d ∈ A, ‖d‖ < s ∧ ‖b + asMap p a c + d‖ < t := by
  have hs := h.pos
  obtain ⟨x, ⟨γ, δ, hδ, hx⟩, hxt⟩ := h.exists_norm_lt ht
  obtain ⟨ε, hε, hcont⟩ := Metric.continuous_iff.mp (continuous_asMap (p := p) a) γ
    (s - ‖δ‖) (by linarith)
  obtain ⟨c, hcA, hc⟩ := hA.exists_dist_lt γ hε
  have hc' := hcont c (by rwa [dist_comm] at hc)
  rw [dist_eq_norm] at hc'
  set δ₁ := δ + asMap p a γ - asMap p a c with hδ₁
  have hδ₁s : ‖δ₁‖ < s := by
    calc ‖δ₁‖ = ‖δ - (asMap p a c - asMap p a γ)‖ := by rw [hδ₁]; ring_nf
      _ ≤ max ‖δ‖ ‖asMap p a c - asMap p a γ‖ := norm_sub_le_max_norm _ _
      _ < s := max_lt hδ (by linarith [norm_nonneg δ])
  obtain ⟨d, hdA, hd⟩ := hA.exists_dist_lt δ₁ hs
  rw [dist_eq_norm] at hd
  refine ⟨c, hcA, d, hdA, ?_, ?_⟩
  · calc ‖d‖ = ‖δ₁ - (δ₁ - d)‖ := by ring_nf
      _ ≤ max ‖δ₁‖ ‖δ₁ - d‖ := norm_sub_le_max_norm _ _
      _ < s := max_lt hδ₁s hd
  · have heq : b + asMap p a c + d = x - (δ₁ - d) := by
      rw [hδ₁]; linear_combination hx
    rw [heq]
    exact (norm_sub_le_max_norm _ _).trans_lt (max_lt hxt (hd.trans ht))

/-! ### Minimal elements -/

/-- **Orthogonality criterion** (from Temkin's proof of Proposition 6.2.4, types 2 and 3,
lines 3958–3964): an element `u` of a special coset that is orthogonal to `K ^ p`, i.e.
`‖u‖ ≤ ‖u + c ^ p‖` for all `c`, is an element of minimal absolute value of the coset. -/
theorem IsSpecialCoset.isMinimalInCoset_of_orthogonal (h : IsSpecialCoset p a s b)
    {u : K} (hu : MemCoset p a s b u) (horth : ∀ c : K, ‖u‖ ≤ ‖u + c ^ p‖) :
    IsMinimalInCoset p a s b u := by
  refine ⟨hu, fun y hy => ?_⟩
  have hns : ¬ IsSplitCoset p a s b := h.1.not_isSplitCoset
  obtain ⟨c, d, hd, hcd⟩ := hu.memCoset_iff.mpr hy
  have hy' : y = (u + asMap p a c) + d := by linear_combination -hcd
  have hmem : MemCoset p a s b (u + asMap p a c) := hu.add_asMap c
  rw [hy', norm_add_eq_of_not_isSplitCoset hns hmem hd]
  rcases h.2 with rfl | ⟨rfl, rfl⟩
  · simpa [asMap_zero_left] using horth c
  · by_contra hlt
    rw [not_le, asMap_one_left] at hlt
    have hmem' : MemCoset p 1 1 b (u + (c ^ p - c)) := by simpa [asMap_one_left] using hmem
    have h1 : 1 ≤ ‖u + (c ^ p - c)‖ := le_norm_of_not_isSplitCoset hns hmem'
    have hu1 : 1 < ‖u‖ := h1.trans_lt hlt
    have heq : ‖c ^ p - c‖ = ‖u‖ := by
      by_contra hne
      have := norm_add_eq_max_of_norm_ne_norm (Ne.symm hne)
      rw [this] at hlt
      exact (lt_irrefl _ (hlt.trans_le (le_max_left _ _)))
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hc1 : 1 < ‖c‖ := by
      by_contra hc
      rw [not_lt] at hc
      have : ‖c ^ p - c‖ ≤ 1 := by
        refine (norm_sub_le_max_norm _ _).trans (max_le ?_ hc)
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg c) hc
      linarith
    have hcp : ‖c‖ < ‖c ^ p‖ := by
      rw [norm_pow]
      calc ‖c‖ = ‖c‖ ^ 1 := (pow_one _).symm
        _ < ‖c‖ ^ p := pow_lt_pow_right₀ hc1 (by omega)
    have hcu : ‖c‖ < ‖u‖ := by
      rw [← heq, norm_sub_eq_max_norm_of_ne hcp.ne', max_eq_left hcp.le]
      exact hcp
    have : ‖u + c ^ p‖ < ‖u‖ := by
      calc ‖u + c ^ p‖ = ‖(u + (c ^ p - c)) + c‖ := by ring_nf
        _ ≤ max ‖u + (c ^ p - c)‖ ‖c‖ := norm_add_le_max _ _
        _ < ‖u‖ := max_lt hlt hcu
    exact lt_irrefl _ (this.trans_le (horth c))

/-- A minimal element of a critical coset has absolute value `s`. -/
theorem IsCriticalCoset.norm_eq_of_isMinimalInCoset (h : IsCriticalCoset p a s b)
    (hx : IsMinimalInCoset p a s b x) : ‖x‖ = s := by
  refine le_antisymm (le_of_forall_gt fun t ht => ?_)
    (le_norm_of_not_isSplitCoset h.not_isSplitCoset hx.1)
  obtain ⟨y, hy, hyt⟩ := h.exists_norm_lt ht
  exact (hx.2 y hy).trans_lt hyt

end CharP

end DeJongAlterations.StableModification.Valuation
