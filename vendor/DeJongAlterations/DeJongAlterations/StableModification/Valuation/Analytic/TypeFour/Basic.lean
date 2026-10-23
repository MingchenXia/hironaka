import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import DeJongAlterations.StableModification.Valuation.Analytic.Basic
import DeJongAlterations.StableModification.Valuation.Analytic.Cosets

/-!
# Type 4 generators: the radius, Lemma 6.2.7, immediacy and density

Let `k` be an algebraically closed field with a non-archimedean absolute value and `K` a
non-archimedean valued field containing `k` isometrically (Lean: `[NormedField k] [IsAlgClosed k]
[NormedField K] [IsUltrametricDist K] [NormedAlgebra k K]`). Neither field is assumed complete.
This file develops the basic theory of Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), §6.2 (`semi-stable.tex`, lines 3817–3842) for fields topologically
generated over `k` by an element `z` of type 4.

## Main definitions

* `radius k z = inf_{a ∈ k} ‖z - a‖`, Temkin's `r = inf |z - k|`.
* `IsTypeFourGenerator k z`: `k(z)` is dense in `K`, the infimum `radius k z` is not attained,
  and `radius k z > 0`.

## Main results

* `inv_mem_closure_of_norm_sub_lt`, `dense_of_forall_inv_mem_closure`: geometric series and a
  density criterion for subrings of a valued field.
* `induction_on_X_sub_C_mul`: induction over the factorization of polynomials over an
  algebraically closed field.
* `norm_aeval_eq_mul_prod_roots`, `norm_leadingCoeff_mul_pow_le_norm_aeval`,
  `norm_leadingCoeff_mul_radius_pow_lt_norm_aeval`: **Temkin, Lemma 6.2.7**
  `‖g(z)‖ ≥ ‖lc g‖ r ^ deg g`, strict if `deg g > 0` and the radius is not attained.
* `exists_norm_aeval_sub_lt`, `IsTypeFourGenerator.dense_aeval`,
  `IsTypeFourGenerator.exists_norm_sub_lt`: `k[z]` is dense in `K`, and every `x ≠ 0` satisfies
  `‖x - c‖ < ‖x‖` for some `c ∈ k`; hence `|K^×| = |k^×|` (`IsTypeFourGenerator.exists_norm_eq`)
  and the residue field of `K` is that of `k` (`IsTypeFourGenerator.exists_norm_sub_lt_one`).
  In the vocabulary of `Analytic/Basic.lean`: `IsTypeFourGenerator.valueGroup_eq` and
  `IsTypeFourGenerator.bijective_algebraMap_residueField` (Temkin's `E_{K/k} = F_{K/k} = 0`).
* `radius_pos_of_completeSpace`: over a complete `k` a non-attained radius is positive.

## References

Blueprint `sm-val-onedim-t34.tex`: `def:sm-an-type4-generator`, `lem:sm-an-type4-radius-pos`,
`lem:sm-an-type4-basics`, `lem:sm-an-dense-inverse`, `lem:sm-an-type4-immediate`.
-/

noncomputable section

open Polynomial Filter Topology

namespace DeJongAlterations.StableModification.Valuation

/-! ### Inverses in the closure of a subring -/

section DenseInverse

variable {F : Type*} [NormedField F]

/-- **Geometric series.** If `y, c` lie in a subring `A`, `c⁻¹ ∈ A` and `‖y - c‖ < ‖c‖`, then
`y⁻¹` lies in the closure of `A`. -/
theorem inv_mem_closure_of_norm_sub_lt {A : Subring F} {y c : F} (hy : y ∈ A) (hc : c ∈ A)
    (hc' : c⁻¹ ∈ A) (h : ‖y - c‖ < ‖c‖) : y⁻¹ ∈ closure (A : Set F) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [sub_zero, norm_zero] at h
    exact (norm_nonneg y).not_gt h
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at h
  set ε := c⁻¹ * y - 1 with hε
  have hεA : ε ∈ A := A.sub_mem (A.mul_mem hc' hy) A.one_mem
  have hε' : ε = c⁻¹ * (y - c) := by rw [hε, mul_sub, inv_mul_cancel₀ hc0]
  have hεn : ‖-ε‖ < 1 := by
    rw [norm_neg, hε', norm_mul, norm_inv]
    exact (inv_mul_lt_one₀ (norm_pos_iff.mpr hc0)).mpr h
  have hyc : y = c * (1 - -ε) := by rw [hε]; field_simp; ring
  set Q : ℕ → F := fun N => c⁻¹ * ∑ n ∈ Finset.range N, (-ε) ^ n with hQ
  have hQA : ∀ N, Q N ∈ A := fun N =>
    A.mul_mem hc' (A.sum_mem fun n _ => A.pow_mem (A.neg_mem hεA) n)
  have hQ' : ∀ N, Q N = y⁻¹ * (1 - (-ε) ^ N) := by
    intro N
    rw [← mul_neg_geom_sum, hyc, hQ]
    have h1 : (1 - -ε) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hyc
      exact hy0 hyc
    field_simp
  have htend : Tendsto Q atTop (𝓝 y⁻¹) := by
    have h0 : Tendsto (fun N => (-ε) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hεn
    have := (tendsto_const_nhds (x := (1 : F))).sub h0 |>.const_mul y⁻¹
    simp only [sub_zero, mul_one] at this
    exact this.congr fun N => (hQ' N).symm
  exact mem_closure_of_tendsto htend (Eventually.of_forall hQA)

/-- **Density criterion.** Let `E ⊆ F` be dense and `A ⊆ F` a subring such that every element of
`E` is `y₁ * y₂⁻¹` with `y₁, y₂ ∈ A` and `y₂⁻¹` in the closure of `A`. Then `A` is dense. -/
theorem dense_of_forall_inv_mem_closure {E : Set F} (hE : Dense E) (A : Subring F)
    (h : ∀ x ∈ E, ∃ y₁ ∈ A, ∃ y₂ ∈ A, y₂⁻¹ ∈ closure (A : Set F) ∧ x = y₁ * y₂⁻¹) :
    Dense (A : Set F) := by
  have hsub : E ⊆ closure (A : Set F) := by
    intro x hx
    obtain ⟨y₁, hy₁, y₂, -, hy₂, rfl⟩ := h x hx
    have h₁ : y₁ ∈ A.topologicalClosure := A.le_topologicalClosure hy₁
    have h₂ : y₂⁻¹ ∈ A.topologicalClosure := hy₂
    exact A.topologicalClosure.mul_mem h₁ h₂
  exact dense_closure.mp (hE.mono hsub)

end DenseInverse

/-! ### Factorization over an algebraically closed field -/

section Factor

variable {k : Type*} [Field k]

/-- Induction over the factorization of a polynomial over an algebraically closed field: a
property of polynomials that holds for constants and is preserved by multiplication with linear
factors `X - C a` holds for all polynomials. -/
theorem induction_on_X_sub_C_mul [IsAlgClosed k] {P : k[X] → Prop} (hC : ∀ c, P (C c))
    (hmul : ∀ a g, P g → P ((X - C a) * g)) (g : k[X]) : P g := by
  rw [(IsAlgClosed.splits g).eq_prod_roots]
  generalize g.leadingCoeff = c
  induction g.roots using Multiset.induction_on with
  | empty => simpa using hC c
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm]
    exact hmul a _ ih

end Factor

/-! ### The radius -/

section Radius

variable (k : Type*) {K : Type*} [NormedField k] [NormedField K] [NormedAlgebra k K]

/-- The radius `r(z) = inf_{a ∈ k} ‖z - a‖` of `z` over `k` (Temkin, §6.2, `r = inf |z - k|`). -/
def radius (z : K) : ℝ := ⨅ a : k, ‖z - algebraMap k K a‖

variable {k}

theorem radius_nonneg (z : K) : 0 ≤ radius k z :=
  Real.iInf_nonneg fun _ => norm_nonneg _

theorem radius_le (z : K) (a : k) : radius k z ≤ ‖z - algebraMap k K a‖ :=
  ciInf_le ⟨0, by rintro _ ⟨b, rfl⟩; exact norm_nonneg _⟩ a

theorem exists_norm_sub_lt_of_radius_lt {z : K} {t : ℝ} (h : radius k z < t) :
    ∃ a : k, ‖z - algebraMap k K a‖ < t :=
  exists_lt_of_ciInf_lt h

/-- If the radius is not attained, it is strictly smaller than every distance `‖z - a‖`. -/
theorem radius_lt_norm_sub {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖) (a : k) :
    radius k z < ‖z - algebraMap k K a‖ := by
  obtain ⟨a', ha'⟩ := h a
  exact (radius_le z a').trans_lt ha'

variable (k) in
/-- `z` is a **type 4 generator** of `K` over `k`: `k(z)` is dense in `K`, the radius
`r(z) = inf_{a ∈ k} ‖z - a‖` is not attained, and `r(z) > 0` (Temkin, §6.2, lines 3817–3842:
`K = \overline{k(z)}` of type 4 over an algebraically closed `k`). -/
structure IsTypeFourGenerator (z : K) : Prop where
  /-- `k(z)` is dense in `K`. -/
  dense_adjoin : Dense (IntermediateField.adjoin k {z} : Set K)
  /-- The radius is not attained. -/
  exists_norm_sub_lt_norm_sub : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖
  /-- The radius is positive. -/
  radius_pos : 0 < radius k z

/-- Over a complete field `k`, a radius that is not attained is positive. -/
theorem radius_pos_of_completeSpace [CompleteSpace k] {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖) :
    0 < radius k z := by
  by_contra hr
  have hr0 : radius k z = 0 := le_antisymm (not_lt.mp hr) (radius_nonneg z)
  have hcl : IsClosed (Set.range (algebraMap k K)) :=
    (algebraMap_isometry k K).isUniformInducing.isComplete_range.isClosed
  have hz : z ∈ closure (Set.range (algebraMap k K)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨a, ha⟩ := exists_norm_sub_lt_of_radius_lt (k := k) (z := z) (t := ε) (by rwa [hr0])
    exact ⟨algebraMap k K a, ⟨a, rfl⟩, by rwa [dist_eq_norm]⟩
  rw [hcl.closure_eq] at hz
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨a', ha'⟩ := h a
  simp only [sub_self, norm_zero] at ha'
  exact (norm_nonneg _).not_gt ha'

end Radius

/-! ### Temkin, Lemma 6.2.7 -/

section LowerBound

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [NormedAlgebra k K]

/-- The absolute value of `g(z)` in terms of the roots of `g` (Temkin, proof of Lemma 6.2.7). -/
theorem norm_aeval_eq_mul_prod_roots (g : k[X]) (z : K) :
    ‖aeval z g‖ = ‖g.leadingCoeff‖ * (g.roots.map fun a => ‖z - algebraMap k K a‖).prod := by
  conv_lhs => rw [(IsAlgClosed.splits g).eq_prod_roots]
  rw [map_mul, aeval_C, norm_mul, norm_algebraMap', map_multiset_prod, Multiset.map_map]
  congr 1
  rw [show ∀ s : Multiset K, ‖s.prod‖ = (s.map (‖·‖)).prod from
    fun s => map_multiset_prod (normHom (α := K)) s, Multiset.map_map]
  congr 1
  ext a
  simp

/-- **Temkin, Lemma 6.2.7** (lower bound): if `0 ≤ r ≤ ‖z - a‖` for all `a ∈ k` (for instance
`r = radius k z`), then `‖lc g‖ r ^ deg g ≤ ‖g(z)‖`. -/
theorem norm_leadingCoeff_mul_pow_le_norm_aeval {z : K} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ a : k, r ≤ ‖z - algebraMap k K a‖) (g : k[X]) :
    ‖g.leadingCoeff‖ * r ^ g.natDegree ≤ ‖aeval z g‖ := by
  induction g using induction_on_X_sub_C_mul with
  | hC c => simp
  | hmul a g ih =>
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    rw [natDegree_mul (X_sub_C_ne_zero a) hg, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul,
      natDegree_X_sub_C, map_mul, norm_mul, map_sub, aeval_X, aeval_C, add_comm, pow_succ,
      ← mul_assoc, mul_comm _ ‖aeval z g‖]
    exact mul_le_mul ih (hr a) hr0 (norm_nonneg _)

/-- **Temkin, Lemma 6.2.7** (strict form): if the radius is not attained and `deg g > 0`, then
`‖lc g‖ r(z) ^ deg g < ‖g(z)‖`; moreover `g(z) ≠ 0` for `g ≠ 0`. -/
theorem norm_aeval_pos_and_lt {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖) (g : k[X]) :
    g ≠ 0 → 0 < ‖aeval z g‖ ∧
      (0 < g.natDegree → ‖g.leadingCoeff‖ * radius k z ^ g.natDegree < ‖aeval z g‖) := by
  induction g using induction_on_X_sub_C_mul with
  | hC c =>
    intro hc
    have hc' : c ≠ 0 := by rintro rfl; simp at hc
    refine ⟨by simpa using hc', fun h0 => by simp at h0⟩
  | hmul a g ih =>
    intro hg'
    have hg : g ≠ 0 := by rintro rfl; simp at hg'
    obtain ⟨hpos, -⟩ := ih hg
    have hlt := radius_lt_norm_sub h a
    have hr0 := radius_nonneg (k := k) z
    have hza : 0 < ‖z - algebraMap k K a‖ := hr0.trans_lt hlt
    have heval : ‖aeval z ((X - C a) * g)‖ = ‖aeval z g‖ * ‖z - algebraMap k K a‖ := by
      rw [map_mul, norm_mul, map_sub, aeval_X, aeval_C, mul_comm]
    refine ⟨by rw [heval]; exact mul_pos hpos hza, fun _ => ?_⟩
    rw [natDegree_mul (X_sub_C_ne_zero a) hg, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul,
      natDegree_X_sub_C, heval, add_comm, pow_succ, ← mul_assoc]
    calc ‖g.leadingCoeff‖ * radius k z ^ g.natDegree * radius k z
        ≤ ‖aeval z g‖ * radius k z :=
          mul_le_mul_of_nonneg_right
            (norm_leadingCoeff_mul_pow_le_norm_aeval hr0 (radius_le z) g) hr0
      _ < ‖aeval z g‖ * ‖z - algebraMap k K a‖ := mul_lt_mul_of_pos_left hlt hpos

/-- **Temkin, Lemma 6.2.7** (strict form). -/
theorem norm_leadingCoeff_mul_radius_pow_lt_norm_aeval {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖) {g : k[X]}
    (hg : 0 < g.natDegree) :
    ‖g.leadingCoeff‖ * radius k z ^ g.natDegree < ‖aeval z g‖ :=
  (norm_aeval_pos_and_lt h g (by rintro rfl; simp at hg)).2 hg

theorem aeval_ne_zero_of_not_attained {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖) {g : k[X]}
    (hg : g ≠ 0) : aeval z g ≠ 0 :=
  norm_pos_iff.mp (norm_aeval_pos_and_lt h g hg).1

theorem IsTypeFourGenerator.aeval_ne_zero {z : K} (hz : IsTypeFourGenerator k z) {g : k[X]}
    (hg : g ≠ 0) : aeval z g ≠ 0 :=
  aeval_ne_zero_of_not_attained hz.exists_norm_sub_lt_norm_sub hg

/-- A type 4 generator is transcendental over `k`. -/
theorem IsTypeFourGenerator.transcendental {z : K} (hz : IsTypeFourGenerator k z) :
    Transcendental k z :=
  transcendental_iff.mpr fun _ hg => by_contra fun hg0 => hz.aeval_ne_zero hg0 hg

end LowerBound

/-! ### Type 4 fields are immediate over `k`; density of `k[z]` -/

section Immediate

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K]
  [NormedAlgebra k K]

omit [IsAlgClosed k] in
/-- Products of elements approximable by constants are approximable by constants. -/
theorem norm_mul_sub_algebraMap_lt {x y : K} {c c' : k} (hx : ‖x - algebraMap k K c‖ < ‖x‖)
    (hy : ‖y - algebraMap k K c'‖ < ‖y‖) :
    ‖x * y - algebraMap k K (c * c')‖ < ‖x * y‖ := by
  have hxpos : 0 < ‖x‖ := (norm_nonneg _).trans_lt hx
  have hc' : ‖algebraMap k K c'‖ = ‖y‖ := norm_eq_of_norm_sub_lt_norm hy
  have heq : x * y - algebraMap k K (c * c') =
      x * (y - algebraMap k K c') + (x - algebraMap k K c) * algebraMap k K c' := by
    rw [map_mul]; ring
  rw [heq, norm_mul x y]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_mul_of_pos_left hy hxpos
  · rw [norm_mul, hc']
    exact mul_lt_mul_of_pos_right hx ((norm_nonneg _).trans_lt hy)

/-- **Immediacy for polynomials**: if the radius of `z` is not attained, then every nonzero
`g(z)`, `g ∈ k[X]`, satisfies `‖g(z) - c‖ < ‖g(z)‖` for some `c ∈ k`. -/
theorem exists_norm_aeval_sub_lt {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖) {g : k[X]}
    (hg : g ≠ 0) : ∃ c : k, ‖aeval z g - algebraMap k K c‖ < ‖aeval z g‖ := by
  induction g using induction_on_X_sub_C_mul with
  | hC c =>
    have hc : c ≠ 0 := by rintro rfl; simp at hg
    exact ⟨c, by simpa using hc⟩
  | hmul a g ih =>
    have hg' : g ≠ 0 := by rintro rfl; simp at hg
    obtain ⟨c, hc⟩ := ih hg'
    obtain ⟨a', ha'⟩ := h a
    have hlin : ‖(z - algebraMap k K a) - algebraMap k K (a' - a)‖ < ‖z - algebraMap k K a‖ := by
      rw [map_sub, sub_sub_sub_cancel_right]; exact ha'
    refine ⟨(a' - a) * c, ?_⟩
    rw [map_mul, map_sub, aeval_X, aeval_C]
    exact norm_mul_sub_algebraMap_lt hlin hc

/-- **Density of `k[z]`**: if `k(z)` is dense in `K` and the radius is not attained, then the
polynomials `g(z)`, `g ∈ k[X]`, are dense in `K`. -/
theorem dense_aeval_of_dense_adjoin {z : K}
    (h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖)
    (hd : Dense (IntermediateField.adjoin k {z} : Set K)) :
    Dense (Set.range fun g : k[X] => aeval z g) := by
  set A : Subring K := (aeval z : k[X] →ₐ[k] K).range.toSubring with hA
  have hmem : ∀ g : k[X], aeval z g ∈ A := fun g => ⟨g, rfl⟩
  have hrange : Set.range (fun g : k[X] => aeval z g) = (A : Set K) := by
    ext x
    simp [hA]
  rw [hrange]
  refine dense_of_forall_inv_mem_closure hd A fun x hx => ?_
  obtain ⟨g₁, g₂, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k x).mp hx
  refine ⟨aeval z g₁, hmem g₁, aeval z g₂, hmem g₂, ?_, div_eq_mul_inv _ _⟩
  rcases eq_or_ne g₂ 0 with rfl | hg₂
  · simpa using subset_closure A.zero_mem
  obtain ⟨c, hc⟩ := exists_norm_aeval_sub_lt h hg₂
  have hcn : ‖algebraMap k K c‖ = ‖aeval z g₂‖ := norm_eq_of_norm_sub_lt_norm hc
  have hcA : algebraMap k K c ∈ A := by simpa using hmem (C c)
  have hcA' : (algebraMap k K c)⁻¹ ∈ A := by simpa using hmem (C c⁻¹)
  exact inv_mem_closure_of_norm_sub_lt (hmem g₂) hcA hcA' (hc.trans_eq hcn.symm)

theorem IsTypeFourGenerator.dense_aeval {z : K} (hz : IsTypeFourGenerator k z) :
    Dense (Set.range fun g : k[X] => aeval z g) :=
  dense_aeval_of_dense_adjoin hz.exists_norm_sub_lt_norm_sub hz.dense_adjoin

/-- **Type 4 fields are immediate over `k`**: every nonzero `x ∈ K` satisfies `‖x - c‖ < ‖x‖`
for some `c ∈ k`. -/
theorem IsTypeFourGenerator.exists_norm_sub_lt {z : K} (hz : IsTypeFourGenerator k z) {x : K}
    (hx : x ≠ 0) : ∃ c : k, ‖x - algebraMap k K c‖ < ‖x‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨_, ⟨g, rfl⟩, hxg⟩ := hz.dense_aeval.exists_dist_lt x hxpos
  rw [dist_eq_norm] at hxg
  have hgx : ‖aeval z g‖ = ‖x‖ := norm_eq_of_norm_sub_lt_norm hxg
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hgx
    exact hx (norm_eq_zero.mp hgx.symm)
  obtain ⟨c, hc⟩ := exists_norm_aeval_sub_lt hz.exists_norm_sub_lt_norm_sub hg
  refine ⟨c, ?_⟩
  calc ‖x - algebraMap k K c‖ = ‖(x - aeval z g) + (aeval z g - algebraMap k K c)‖ := by ring_nf
    _ ≤ max ‖x - aeval z g‖ ‖aeval z g - algebraMap k K c‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ < ‖x‖ := max_lt hxg (hc.trans_eq hgx)

/-- The value group of a type 4 field is that of `k`: `|K^×| = |k^×|`. -/
theorem IsTypeFourGenerator.exists_norm_eq {z : K} (hz : IsTypeFourGenerator k z) (x : K) :
    ∃ c : k, ‖c‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨c, hc⟩ := hz.exists_norm_sub_lt hx
  exact ⟨c, by rw [← norm_algebraMap' K c]; exact norm_eq_of_norm_sub_lt_norm hc⟩

/-- The residue field of a type 4 field is that of `k`: every `x` with `‖x‖ ≤ 1` is congruent
modulo the open unit ball to an element of the unit ball of `k`. -/
theorem IsTypeFourGenerator.exists_norm_sub_lt_one {z : K} (hz : IsTypeFourGenerator k z)
    {x : K} (hx : ‖x‖ ≤ 1) : ∃ c : k, ‖c‖ ≤ 1 ∧ ‖x - algebraMap k K c‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨c, hc⟩ := hz.exists_norm_sub_lt hx0
  refine ⟨c, ?_, hc.trans_le hx⟩
  rw [← norm_algebraMap' K c, norm_eq_of_norm_sub_lt_norm hc]
  exact hx

end Immediate

/-! ### Value group and residue field in the vocabulary of `Analytic/Basic.lean` -/

section AnalyticBridge

open IsLocalRing Analytic

variable {k K : Type*} [NormedField k] [IsUltrametricDist k] [IsAlgClosed k] [NormedField K]
  [IsUltrametricDist K] [NormedAlgebra k K]

/-- A type 4 field has the value group of `k`: `|K^×| = |k^×|` (Temkin's `E_{K/k} = 0`). -/
theorem IsTypeFourGenerator.valueGroup_eq {z : K} (hz : IsTypeFourGenerator k z) :
    valueGroup K = valueGroup k := by
  refine le_antisymm (fun γ hγ ↦ ?_) valueGroup_le_valueGroup
  obtain ⟨x, hx⟩ := mem_valueGroup_iff.mp hγ
  obtain ⟨c, hc⟩ := hz.exists_norm_eq x
  exact mem_valueGroup_iff.mpr ⟨c, by rw [← hx]; ext; simp [hc]⟩

/-- A type 4 field has the residue field of `k` (Temkin's `F_{K/k} = 0`): the residue field
extension `k̃ → K̃` is bijective. -/
theorem IsTypeFourGenerator.bijective_algebraMap_residueField {z : K}
    (hz : IsTypeFourGenerator k z) :
    Function.Bijective
      (algebraMap (ResidueField (unitBall k)) (ResidueField (unitBall K))) := by
  refine ⟨(algebraMap (ResidueField (unitBall k)) (ResidueField (unitBall K))).injective, ?_⟩
  intro w
  obtain ⟨x, rfl⟩ := residue_surjective w
  obtain ⟨c, hc1, hc⟩ := hz.exists_norm_sub_lt_one (norm_coe_unitBall_le_one x)
  refine ⟨residue (unitBall k) ⟨c, mem_unitBall.mpr hc1⟩, ?_⟩
  rw [algebraMap_residue, residue_eq_residue_iff, coe_algebraMap_unitBall, norm_sub_rev]
  exact hc

end AnalyticBridge

end DeJongAlterations.StableModification.Valuation
