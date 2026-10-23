import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.CharP.Algebra
import DeJongAlterations.StableModification.Valuation.Analytic.TypeFour.Basic

/-!
# Annulus fields: Laurent polynomials, the Gauss formula and density

Let `k` be an algebraically closed non-archimedean field and `K ⊇ k` a non-archimedean field.
An element `T ∈ K` is an *annulus generator* if `k(T)` is dense in `K` and `‖T‖ ∉ |k|`. This is
the type 3 field `K ≅ \widehat{k(T)} = k{r⁻¹T, rT⁻¹}`, `r = |T| ∉ |k^×|`, of Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §6.2
(`semi-stable.tex`, lines 3709–3712 and 3746–3753). Instead of Temkin's description of `K` by
Laurent series with the Schauder basis `T^ℤ`, only Laurent polynomials are used here: their
absolute value is given by the Gauss formula and they are dense in `K`.

## Main definitions

* `IsAnnulusGenerator k T`.
* `laurent k T : (ℤ →₀ k) →ₗ[k] K`, `f ↦ ∑ fᵢ Tⁱ`, and `laurentSubring k T`, its range
  `span_k {Tⁱ : i ∈ ℤ}`, a subring of `K`.

## Main results

* `IsAnnulusGenerator.norm_smul_zpow_ne`: monomials with nonzero coefficients and distinct
  exponents have distinct absolute values.
* `IsAnnulusGenerator.norm_laurent`, `IsAnnulusGenerator.norm_coeff_mul_le`: the Gauss formula
  `‖∑ fᵢ Tⁱ‖ = max ‖fᵢ‖ ‖T‖ⁱ`.
* `IsAnnulusGenerator.exists_dominant`, `IsAnnulusGenerator.dense_laurent`: dominant monomials
  and density of Laurent polynomials.
* `IsAnnulusGenerator.exists_norm_sub_lt`, `IsAnnulusGenerator.exists_norm_sub_lt_one`: every
  `x ≠ 0` is approximated by a monomial `c Tʲ` to within less than `‖x‖`, and the residue field of
  `K` is that of `k`; in the vocabulary of `Analytic/Basic.lean`,
  `IsAnnulusGenerator.valueGroup_eq` (`|K^×| = |k^×| ‖T‖^ℤ`) and
  `IsAnnulusGenerator.bijective_algebraMap_residueField`.
* `IsAnnulusGenerator.norm_le_norm_add_pow_char`: in characteristic `p`, the span of the
  `T^e` with `p ∤ e` is orthogonal to `K ^ p`.

## References

Blueprint `sm-val-onedim-t34.tex`: `def:sm-an-annulus-generator`, `lem:sm-an-annulus`,
`lem:sm-an-annulus-orthogonal`.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.StableModification.Valuation

variable (k : Type*) {K : Type*} [NormedField k] [NormedField K] [NormedAlgebra k K]

/-- `T` is an **annulus generator** of `K` over `k`: `k(T)` is dense in `K` and `‖T‖` is not the
absolute value of an element of `k` (Temkin's type 3 field `k{r⁻¹T, rT⁻¹}`, `r = |T| ∉ |k^×|`). -/
structure IsAnnulusGenerator (T : K) : Prop where
  /-- `k(T)` is dense in `K`. -/
  dense_adjoin : Dense (IntermediateField.adjoin k {T} : Set K)
  /-- `‖T‖ ∉ |k|`. -/
  norm_ne : ∀ c : k, ‖T‖ ≠ ‖c‖

/-- Laurent polynomials in `T`: `f ↦ ∑ fᵢ Tⁱ`. -/
def laurent (T : K) : (ℤ →₀ k) →ₗ[k] K := Finsupp.linearCombination k fun i : ℤ => T ^ i

/-- The `k`-span of the powers `Tⁱ`, `i ∈ ℤ`: the ring of Laurent polynomials in `T`. -/
def laurentSubring (T : K) : Subring K where
  carrier := Submodule.span k (Set.range fun i : ℤ => T ^ i)
  mul_mem' {x y} hx hy := by
    have hle : Submodule.span k (Set.range fun i : ℤ => T ^ i) *
        Submodule.span k (Set.range fun i : ℤ => T ^ i) ≤
        Submodule.span k (Set.range fun i : ℤ => T ^ i) := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      by_cases hT : T = 0
      · by_cases hi : i = 0
        · exact ⟨j, by simp [hi]⟩
        · exact ⟨i, by simp [hT, zero_zpow i hi]⟩
      · exact ⟨i + j, by simp [zpow_add₀ hT]⟩
    exact hle (Submodule.mul_mem_mul hx hy)
  one_mem' := Submodule.subset_span ⟨0, zpow_zero T⟩
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  neg_mem' := Submodule.neg_mem _

variable {k}

theorem mem_laurentSubring_iff {T x : K} :
    x ∈ laurentSubring k T ↔ ∃ f : ℤ →₀ k, laurent k T f = x := by
  change x ∈ Submodule.span k _ ↔ _
  rw [← Finsupp.range_linearCombination]
  rfl

theorem laurent_mem_laurentSubring (T : K) (f : ℤ →₀ k) : laurent k T f ∈ laurentSubring k T :=
  mem_laurentSubring_iff.mpr ⟨f, rfl⟩

theorem smul_zpow_mem_laurentSubring (T : K) (c : k) (i : ℤ) :
    c • T ^ i ∈ laurentSubring k T :=
  Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)

theorem laurent_apply (T : K) (f : ℤ →₀ k) :
    laurent k T f = ∑ i ∈ f.support, f i • T ^ i := by
  rw [laurent, Finsupp.linearCombination_apply, Finsupp.sum]

theorem aeval_mem_laurentSubring (T : K) (g : k[X]) : aeval T g ∈ laurentSubring k T := by
  rw [aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  have := smul_zpow_mem_laurentSubring (k := k) T (g.coeff i) i
  rwa [zpow_natCast] at this

namespace IsAnnulusGenerator

variable {T : K} (hT : IsAnnulusGenerator k T)
include hT

theorem ne_zero : T ≠ 0 := by
  intro h
  exact hT.norm_ne 0 (by simp [h])

theorem norm_pos : 0 < ‖T‖ := norm_pos_iff.mpr hT.ne_zero

/-- No nonzero integral power of `‖T‖` is the absolute value of an element of `k`. -/
theorem norm_zpow_ne [IsAlgClosed k] {i : ℤ} (hi : i ≠ 0) (c : k) : ‖T‖ ^ i ≠ ‖c‖ := by
  have hpos := hT.norm_pos
  have key : ∀ n : ℕ, n ≠ 0 → ∀ c : k, ‖T‖ ^ n ≠ ‖c‖ := by
    intro n hn c h
    obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn)
    rw [← he, norm_pow] at h
    exact hT.norm_ne e ((pow_left_inj₀ hpos.le (norm_nonneg e) hn).mp h)
  rcases lt_or_gt_of_ne hi with hneg | hpos'
  · intro h
    obtain ⟨n, hn⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨i.natAbs, by omega⟩
    have hn0 : n ≠ 0 := by omega
    apply key n hn0 c⁻¹
    rw [norm_inv, ← h, hn, zpow_neg, zpow_natCast, inv_inv]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = n := ⟨i.natAbs, by omega⟩
    rw [hn, zpow_natCast]
    exact key n (by omega) c

/-- **Distinct monomial values**: for `c, c' ≠ 0` and `i ≠ j`, `‖c Tⁱ‖ ≠ ‖c' Tʲ‖`. -/
theorem norm_smul_zpow_ne [IsAlgClosed k] {c c' : k} (hc : c ≠ 0) {i j : ℤ} (hij : i ≠ j) :
    ‖c • T ^ i‖ ≠ ‖c' • T ^ j‖ := by
  have hpos := hT.norm_pos
  rw [norm_smul, norm_smul, norm_zpow, norm_zpow]
  intro h
  apply hT.norm_zpow_ne (sub_ne_zero.mpr hij) (c' / c)
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [zpow_sub₀ hpos.ne', norm_div]
  field_simp
  linarith [h]

/-- **Gauss formula** for Laurent polynomials in an annulus generator. -/
theorem norm_laurent [IsAlgClosed k] [IsUltrametricDist K] (f : ℤ →₀ k) (hf : f ≠ 0) :
    ‖laurent k T f‖ =
      f.support.sup' (Finsupp.support_nonempty_iff.mpr hf) fun i => ‖f i‖ * ‖T‖ ^ i := by
  rw [laurent_apply, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne
    (Finsupp.support_nonempty_iff.mpr hf)]
  · simp only [norm_smul, norm_zpow]
  · intro i hi j _ hij
    exact hT.norm_smul_zpow_ne (Finsupp.mem_support_iff.mp hi) hij

/-- Coefficient bound from the Gauss formula: `‖fᵢ‖ ‖T‖ⁱ ≤ ‖∑ fⱼ Tʲ‖`. -/
theorem norm_coeff_mul_le [IsAlgClosed k] [IsUltrametricDist K] (f : ℤ →₀ k) (i : ℤ) :
    ‖f i‖ * ‖T‖ ^ i ≤ ‖laurent k T f‖ := by
  by_cases hi : i ∈ f.support
  · have hf : f ≠ 0 := by rintro rfl; simp at hi
    rw [hT.norm_laurent f hf]
    exact Finset.le_sup' (fun i => ‖f i‖ * ‖T‖ ^ i) hi
  · rw [Finsupp.notMem_support_iff.mp hi, norm_zero, zero_mul]
    exact norm_nonneg _

/-- **Dominant monomial**: every nonzero Laurent polynomial `x` has a monomial `c Tʲ`, `c ≠ 0`,
with `‖x - c Tʲ‖ < ‖x‖`. -/
theorem exists_dominant [IsAlgClosed k] [IsUltrametricDist K] {x : K}
    (hx : x ∈ laurentSubring k T) (hx0 : x ≠ 0) :
    ∃ c : k, ∃ j : ℤ, c ≠ 0 ∧ ‖x - c • T ^ j‖ < ‖x‖ := by
  classical
  obtain ⟨f, rfl⟩ := mem_laurentSubring_iff.mp hx
  have hf : f ≠ 0 := by rintro rfl; simp at hx0
  have hne := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_mem_eq_sup' hne fun i => ‖f i‖ * ‖T‖ ^ i
  refine ⟨f j, j, Finsupp.mem_support_iff.mp hj, ?_⟩
  have hsplit : laurent k T f = f j • T ^ j + laurent k T (Finsupp.erase j f) := by
    conv_lhs => rw [← Finsupp.single_add_erase j f]
    rw [map_add, laurent, Finsupp.linearCombination_single]
  have hsub : laurent k T f - f j • T ^ j = laurent k T (Finsupp.erase j f) := by
    rw [hsplit, add_sub_cancel_left]
  rw [hsub, hT.norm_laurent f hf, hjmax]
  by_cases he : Finsupp.erase j f = 0
  · rw [he, map_zero, norm_zero]
    exact mul_pos (norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hj)) (zpow_pos hT.norm_pos j)
  rw [hT.norm_laurent _ he, Finset.sup'_lt_iff]
  intro i hi
  rw [Finsupp.support_erase, Finset.mem_erase] at hi
  rw [Finsupp.erase_ne hi.1]
  refine lt_of_le_of_ne ?_ ?_
  · rw [← hjmax]
    exact Finset.le_sup' (fun i => ‖f i‖ * ‖T‖ ^ i) hi.2
  · have := hT.norm_smul_zpow_ne (c' := f j) (Finsupp.mem_support_iff.mp hi.2) hi.1
    rwa [norm_smul, norm_smul, norm_zpow, norm_zpow] at this

/-- **Density of Laurent polynomials** in an annulus field. -/
theorem dense_laurent [IsAlgClosed k] [IsUltrametricDist K] :
    Dense (laurentSubring k T : Set K) := by
  refine dense_of_forall_inv_mem_closure hT.dense_adjoin _ fun x hx => ?_
  obtain ⟨g₁, g₂, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k x).mp hx
  refine ⟨aeval T g₁, aeval_mem_laurentSubring T g₁, aeval T g₂, aeval_mem_laurentSubring T g₂,
    ?_, div_eq_mul_inv _ _⟩
  set y := aeval T g₂
  by_cases hy : y = 0
  · rw [hy, inv_zero]
    exact subset_closure (Subring.zero_mem _)
  obtain ⟨c, j, hc, hcj⟩ := hT.exists_dominant (aeval_mem_laurentSubring T g₂) hy
  have hTj : T ^ j ≠ 0 := zpow_ne_zero j hT.ne_zero
  have hinv : (c • T ^ j)⁻¹ = c⁻¹ • T ^ (-j) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_inv, zpow_neg, map_inv₀]
  refine inv_mem_closure_of_norm_sub_lt (aeval_mem_laurentSubring T g₂)
    (smul_zpow_mem_laurentSubring T c j) ?_ ?_
  · rw [hinv]
    exact smul_zpow_mem_laurentSubring T c⁻¹ (-j)
  · rwa [norm_eq_of_norm_sub_lt_norm hcj]

/-- **Annulus fields are approximated by monomials**: every `x ≠ 0` admits `c ∈ k` and `j ∈ ℤ`
with `‖x - c Tʲ‖ < ‖x‖`. In particular `|K^×| = |k^×| ‖T‖^ℤ`. -/
theorem exists_norm_sub_lt [IsAlgClosed k] [IsUltrametricDist K] {x : K} (hx : x ≠ 0) :
    ∃ c : k, ∃ j : ℤ, ‖x - c • T ^ j‖ < ‖x‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨y, hyL, hxy⟩ := hT.dense_laurent.exists_dist_lt x hxpos
  rw [dist_eq_norm] at hxy
  have hyx : ‖y‖ = ‖x‖ := norm_eq_of_norm_sub_lt_norm hxy
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hyx
    exact hxpos.ne hyx
  obtain ⟨c, j, -, hcj⟩ := hT.exists_dominant hyL hy
  refine ⟨c, j, ?_⟩
  calc ‖x - c • T ^ j‖ = ‖(x - y) + (y - c • T ^ j)‖ := by ring_nf
    _ ≤ max ‖x - y‖ ‖y - c • T ^ j‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ‖x‖ := max_lt hxy (hcj.trans_eq hyx)

/-- The residue field of an annulus field is that of `k`. -/
theorem exists_norm_sub_lt_one [IsAlgClosed k] [IsUltrametricDist K] {x : K} (hx : ‖x‖ ≤ 1) :
    ∃ c : k, ‖c‖ ≤ 1 ∧ ‖x - algebraMap k K c‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact ⟨0, by simpa using hlt⟩
  obtain ⟨c, j, hcj⟩ := hT.exists_norm_sub_lt hx0
  have hcn : ‖c • T ^ j‖ = ‖x‖ := norm_eq_of_norm_sub_lt_norm hcj
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, norm_zero] at hcn
    exact hx0 (norm_eq_zero.mp hcn.symm)
  have hj : j = 0 := by
    by_contra hj
    apply hT.norm_smul_zpow_ne (c' := (1 : k)) hc hj
    rw [hcn, heq, zpow_zero, one_smul, norm_one]
  subst hj
  refine ⟨c, ?_, ?_⟩
  · rw [zpow_zero, norm_smul, norm_one, mul_one] at hcn
    rw [hcn, heq]
  · rw [zpow_zero, Algebra.smul_def, mul_one] at hcj
    rwa [heq] at hcj

/-- **Orthogonality to `K ^ p`** (characteristic `p`): every element `v` of the `k`-span of the
`T^e` with `p ∤ e` satisfies `‖v‖ ≤ ‖v + γ ^ p‖` for all `γ ∈ K`. -/
theorem norm_le_norm_add_pow_char [IsAlgClosed k] [IsUltrametricDist K] {p : ℕ}
    [Fact p.Prime] [CharP k p] {v : K}
    (hv : v ∈ Submodule.span k ((fun i : ℤ => T ^ i) '' {e | ¬ (p : ℤ) ∣ e})) (γ : K) :
    ‖v‖ ≤ ‖v + γ ^ p‖ := by
  classical
  have hp := (Fact.out : p.Prime)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  -- approximate `γ` by a Laurent polynomial
  set δ := min ‖v‖ 1 with hδ
  have hδpos : 0 < δ := lt_min hvpos one_pos
  obtain ⟨γ', hγ'L, hγγ'⟩ := hT.dense_laurent.exists_dist_lt γ hδpos
  rw [dist_eq_norm] at hγγ'
  have hpow : ‖γ ^ p - γ' ^ p‖ < ‖v‖ := by
    rw [← sub_pow_char, norm_pow]
    calc ‖γ - γ'‖ ^ p < δ ^ p := pow_lt_pow_left₀ hγγ' (norm_nonneg _) hp.ne_zero
      _ ≤ δ := pow_le_of_le_one hδpos.le (min_le_right _ _) hp.ne_zero
      _ ≤ ‖v‖ := min_le_left _ _
  -- `γ' ^ p` lies in the span of the `T^e` with `p ∣ e`
  have hγ'p : γ' ^ p ∈ Submodule.span k ((fun i : ℤ => T ^ i) '' {e | (p : ℤ) ∣ e}) := by
    obtain ⟨h, rfl⟩ := mem_laurentSubring_iff.mp hγ'L
    rw [laurent_apply, sum_pow_char]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [_root_.smul_pow, ← zpow_natCast (T ^ i) p, ← zpow_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i * p, ⟨i, by ring⟩, rfl⟩)
  obtain ⟨l, hl, hlv⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp hv
  obtain ⟨l', hl', hl'v⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp hγ'p
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero] at hlv
    exact hv0 hlv.symm
  have hlv' : laurent k T l = v := hlv
  have hl'v' : laurent k T l' = γ' ^ p := hl'v
  -- the Gauss formula for `v + γ' ^ p`
  have hsum : laurent k T (l + l') = v + γ' ^ p := by
    rw [map_add, hlv', hl'v']
  have hle : ‖v‖ ≤ ‖v + γ' ^ p‖ := by
    rw [← hsum]
    conv_lhs => rw [← hlv', hT.norm_laurent l hl0]
    refine Finset.sup'_le _ _ fun e he => ?_
    have he' : e ∉ l'.support := by
      intro he'
      have h1 := (Finsupp.mem_supported k l).mp hl he
      have h2 := (Finsupp.mem_supported k l').mp hl' he'
      exact h1 h2
    have := hT.norm_coeff_mul_le (l + l') e
    rwa [Finsupp.add_apply, Finsupp.notMem_support_iff.mp he', add_zero] at this
  -- conclude by the ultrametric inequality
  by_contra hlt
  rw [not_le] at hlt
  have : ‖v + γ' ^ p‖ < ‖v‖ := by
    calc ‖v + γ' ^ p‖ = ‖(v + γ ^ p) - (γ ^ p - γ' ^ p)‖ := by ring_nf
      _ ≤ max ‖v + γ ^ p‖ ‖γ ^ p - γ' ^ p‖ := norm_sub_le_max_norm _ _
      _ < ‖v‖ := max_lt hlt hpow
  exact lt_irrefl _ (this.trans_le hle)

end IsAnnulusGenerator

/-! ### Value group and residue field in the vocabulary of `Analytic/Basic.lean` -/

section AnalyticBridge

open IsLocalRing Analytic

variable [IsAlgClosed k] [IsUltrametricDist k] [IsUltrametricDist K] {T : K}

/-- An annulus field has value group `|K^×| = |k^×| · ‖T‖^ℤ` (Temkin's `E_{K/k} = 1`). -/
theorem IsAnnulusGenerator.valueGroup_eq (hT : IsAnnulusGenerator k T) :
    valueGroup K = valueGroup k ⊔ Subgroup.zpowers (normUnits K (Units.mk0 T hT.ne_zero)) := by
  apply le_antisymm
  · intro γ hγ
    obtain ⟨x, hx⟩ := mem_valueGroup_iff.mp hγ
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by rw [← hx, nnnorm_zero])
    obtain ⟨c, j, hcj⟩ := hT.exists_norm_sub_lt hx0
    have hn : ‖x‖ = ‖c‖ * ‖T‖ ^ j := by
      rw [← norm_eq_of_norm_sub_lt_norm hcj, norm_smul, norm_zpow]
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero, zero_mul, norm_eq_zero] at hn
      exact hx0 hn
    rw [Subgroup.mem_sup]
    refine ⟨normUnits k (Units.mk0 c hc0), norm_mem_valueGroup _,
      normUnits K (Units.mk0 T hT.ne_zero) ^ j, Subgroup.zpow_mem_zpowers _ _, ?_⟩
    ext
    rw [← hx]
    simp [Units.val_zpow_eq_zpow_val, hn]
  · exact sup_le valueGroup_le_valueGroup
      ((Subgroup.zpowers_le).mpr (norm_mem_valueGroup _))

/-- An annulus field has the residue field of `k` (Temkin's `F_{K/k} = 0`): the residue field
extension `k̃ → K̃` is bijective. -/
theorem IsAnnulusGenerator.bijective_algebraMap_residueField (hT : IsAnnulusGenerator k T) :
    Function.Bijective
      (algebraMap (ResidueField (unitBall k)) (ResidueField (unitBall K))) := by
  refine ⟨(algebraMap (ResidueField (unitBall k)) (ResidueField (unitBall K))).injective, ?_⟩
  intro w
  obtain ⟨x, rfl⟩ := residue_surjective w
  obtain ⟨c, hc1, hc⟩ := hT.exists_norm_sub_lt_one (norm_coe_unitBall_le_one x)
  refine ⟨residue (unitBall k) ⟨c, mem_unitBall.mpr hc1⟩, ?_⟩
  rw [algebraMap_residue, residue_eq_residue_iff, coe_algebraMap_unitBall, norm_sub_rev]
  exact hc

end AnalyticBridge

end DeJongAlterations.StableModification.Valuation
