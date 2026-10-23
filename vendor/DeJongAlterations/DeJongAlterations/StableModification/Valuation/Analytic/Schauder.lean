/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Gauss
import DeJongAlterations.StableModification.Valuation.FunctionField.FrobeniusBasis

/-!
# Orthonormal Schauder bases and the type 2 basis of Temkin's Proposition 6.2.5

Let `K` be a non-archimedean field and `E` a non-archimedean normed `K`-space. A family
`(vᵢ)` in `E` is *orthonormal* if `‖vᵢ‖ = 1` and `‖∑ aᵢ vᵢ‖ = maxᵢ ‖aᵢ‖` for finitely supported
coefficients, and an *orthonormal Schauder basis* if moreover its span is dense. For complete `K`
and `E` this is Temkin's notion (*Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), `semi-stable.tex`, lines 3732–3735): every `x` has a unique expansion `x = ∑ cᵢ vᵢ`, and
`‖x‖ = maxᵢ ‖cᵢ‖` (`IsOrthonormalSchauderBasis.existsUnique_hasSum`,
`IsOrthonormalSchauderBasis.exists_hasSum`).

The main result is the type 2 case of Temkin's Proposition 6.2.5 (lines 3754–3815),
`IsGaussGenerator.exists_frobeniusFamily_isOrthonormalSchauderBasis`: let `k` be algebraically
closed of characteristic `p`, `z` a Gauss generator of `K` over `k`, and `L` a complete extension
of `K` with `[L : K] = [L̃ : K̃]` and `L̃/K̃` separable. Then there is `U ⊆ L` such that
`{1} ⊔ U ⊔ U^p ⊔ U^{p²} ⊔ ⋯` is an orthonormal Schauder basis of `L` over `k` and every element of
`span_k U` is orthogonal to `L^p`.

The proof lifts the Frobenius basis of the function field `L̃/k̃` (Temkin's Lemma 6.2.6,
`FunctionField.exists_frobeniusBasis_of_isAlgClosed`) to a coefficient field `L₀ ⊆ L` containing
a coefficient field `k₀` of `k` and `z` (`Analytic/CoefficientField.lean`). In place of Temkin's
discretely valued `k₀`, Bosch–Güntzer–Remmert 2.7.3/2, 2.7.5/2 and `L₀ ⊗̂_{k₀} k ≅ L`, the lifted
basis spans `L₀` over `k₀` by linear algebra (`IsCoefficientField.mem_span_of_span_residue`) and
the `k`-span of `L₀` is dense (`dense_adjoin_of_isCoefficientField`).

## Main definitions

* `IsOrthonormalFamily K v`, `IsOrthonormalSchauderBasis K v`.

## Main results

* `IsOrthonormalFamily.norm_le_of_hasSum`, `IsOrthonormalFamily.eq_of_hasSum`,
  `IsOrthonormalSchauderBasis.exists_hasSum`, `IsOrthonormalSchauderBasis.existsUnique_hasSum`:
  expansions in orthonormal Schauder bases.
* `isOrthonormalFamily_of_linearIndependent_residue`: lifts of `k̃`-independent residues are
  orthonormal.
* `IsCoefficientField.mem_span_of_span_residue`: lifts in a coefficient field of a spanning family
  of residues span the coefficient field.
* `norm_le_norm_add_pow_of_residue`: orthogonality to `L^p` from residues.
* `IsGaussGenerator.exists_frobeniusFamily_isOrthonormalSchauderBasis`: **Temkin,
  Proposition 6.2.5, type 2**.

## References

Blueprint `sm-val-onedim-type2.tex`: `def:sm-an-orthonormal-schauder`,
`lem:sm-an-schauder-expansion`, `lem:sm-an-lifted-basis`, `lem:sm-an-schauder-type2`.
-/

noncomputable section

open IsLocalRing Polynomial Module Filter Topology
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.Analytic

section Defs

variable (K : Type*) {E ι : Type*} [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]

/-- An **orthonormal family** in a normed `K`-space: `‖vᵢ‖ = 1` for all `i`, and
`‖aᵢ‖ ≤ ‖∑ⱼ aⱼ vⱼ‖` for all finitely supported coefficients `a` and all `i`. In a non-archimedean
space this says `‖∑ aⱼ vⱼ‖ = maxⱼ ‖aⱼ‖`. -/
structure IsOrthonormalFamily (v : ι → E) : Prop where
  /-- Every member has norm one. -/
  norm_eq_one : ∀ i, ‖v i‖ = 1
  /-- Each coefficient is bounded by the norm of the linear combination. -/
  norm_le : ∀ (a : ι →₀ K) (i : ι), ‖a i‖ ≤ ‖Finsupp.linearCombination K v a‖

/-- An **orthonormal Schauder basis**: an orthonormal family whose span is dense. For complete `K`
and `E` every element then has a unique expansion `∑ cᵢ vᵢ` with `‖x‖ = maxᵢ ‖cᵢ‖`
(`IsOrthonormalSchauderBasis.existsUnique_hasSum`, `IsOrthonormalSchauderBasis.exists_hasSum`),
which is Temkin's definition (`semi-stable.tex`, lines 3732–3735). -/
structure IsOrthonormalSchauderBasis (v : ι → E) : Prop extends IsOrthonormalFamily K v where
  /-- The span is dense. -/
  dense_span : Dense (Submodule.span K (Set.range v) : Set E)

end Defs

/-! ### Expansions -/

namespace IsOrthonormalFamily

variable {K E ι : Type*} [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  [IsUltrametricDist E] {v : ι → E} (hv : IsOrthonormalFamily K v)
include hv

/-- `‖∑ᵢ∈s cᵢ vᵢ‖ ≤ r` if all `‖cᵢ‖ ≤ r`. -/
theorem norm_sum_smul_le (s : Finset ι) (c : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i ∈ s, ‖c i‖ ≤ r) : ‖∑ i ∈ s, c i • v i‖ ≤ r :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i hi ↦ by
    rw [norm_smul, hv.norm_eq_one, mul_one]
    exact h i hi

/-- `‖∑ aᵢ vᵢ‖ ≤ r` if all `‖aᵢ‖ ≤ r`. -/
theorem norm_linearCombination_le (a : ι →₀ K) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, ‖a i‖ ≤ r) :
    ‖Finsupp.linearCombination K v a‖ ≤ r := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact hv.norm_sum_smul_le _ _ hr fun i _ ↦ h i

/-- The norm of a nonzero finite combination is the norm of one of its coefficients. -/
theorem exists_norm_linearCombination_eq (a : ι →₀ K) (ha : a ≠ 0) :
    ∃ i, ‖Finsupp.linearCombination K v a‖ = ‖a i‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image a.support (fun i ↦ ‖a i‖)
    (Finsupp.support_nonempty_iff.mpr ha)
  refine ⟨i, le_antisymm (hv.norm_linearCombination_le a (norm_nonneg _) fun j ↦ ?_)
    (hv.norm_le a i)⟩
  by_cases hj : j ∈ a.support
  · exact hi j hj
  · rw [Finsupp.notMem_support_iff.mp hj, norm_zero]
    exact norm_nonneg _

omit [IsUltrametricDist E] in
/-- Orthonormality for finite sums over a `Finset`. -/
theorem norm_le_sum (s : Finset ι) (c : ι → K) {i : ι} (hi : i ∈ s) :
    ‖c i‖ ≤ ‖∑ j ∈ s, c j • v j‖ := by
  classical
  have hf : ∀ j, (if j ∈ s then c j else 0) ≠ 0 → j ∈ s := fun j hj ↦ by
    by_contra h
    simp [h] at hj
  have := hv.norm_le (Finsupp.onFinset s _ hf) i
  rw [Finsupp.linearCombination_onFinset, Finsupp.onFinset_apply, if_pos hi] at this
  convert this using 2
  exact Finset.sum_congr rfl fun j hj ↦ by rw [if_pos hj]

omit [IsUltrametricDist E] in
/-- **Expansions, (1)**: if `x = ∑ cᵢ vᵢ` then `‖cᵢ‖ ≤ ‖x‖` for all `i`. -/
theorem norm_le_of_hasSum {c : ι → K} {x : E} (h : HasSum (fun i ↦ c i • v i) x) (i : ι) :
    ‖c i‖ ≤ ‖x‖ := by
  have ht : Tendsto (fun s : Finset ι ↦ ∑ j ∈ s, c j • v j) atTop (𝓝 x) := h
  refine ge_of_tendsto ht.norm ?_
  filter_upwards [eventually_ge_atTop {i}] with s hs
  exact hv.norm_le_sum s c (hs (Finset.mem_singleton_self i))

omit [IsUltrametricDist E] in
/-- **Expansions, (1)**: expansions in an orthonormal family are unique. -/
theorem eq_of_hasSum {c c' : ι → K} {x : E} (h : HasSum (fun i ↦ c i • v i) x)
    (h' : HasSum (fun i ↦ c' i • v i) x) : c = c' := by
  funext i
  have hsub : HasSum (fun i ↦ (c - c') i • v i) 0 := by
    simpa [sub_smul] using h.sub h'
  have := hv.norm_le_of_hasSum hsub i
  rw [norm_zero, Pi.sub_apply] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

end IsOrthonormalFamily

namespace IsOrthonormalSchauderBasis

variable {K E ι : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] {v : ι → E}
  (hv : IsOrthonormalSchauderBasis K v)
include hv

/-- **Expansions, (2)**: over a complete `K`, every `x` has an expansion `x = ∑ cᵢ vᵢ` in an
orthonormal Schauder basis, and `‖x‖ = ‖cᵢ‖` for some `i` if `x ≠ 0`. -/
theorem exists_hasSum (x : E) :
    ∃ c : ι → K, HasSum (fun i ↦ c i • v i) x ∧ (x ≠ 0 → ∃ i, ‖c i‖ = ‖x‖) := by
  classical
  have hv' := hv.toIsOrthonormalFamily
  have happrox : ∀ n : ℕ, ∃ a : ι →₀ K,
      ‖x - Finsupp.linearCombination K v a‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hy, hxy⟩ := hv.dense_span.exists_dist_lt x (by positivity : (0 : ℝ) < 1 / (n + 1))
    obtain ⟨a, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
    exact ⟨a, by rwa [dist_eq_norm, ← Finsupp.linearCombination_apply] at hxy⟩
  choose a ha using happrox
  set d : ℕ → E := fun n ↦ Finsupp.linearCombination K v (a n) with hd
  have hmono : ∀ n m : ℕ, n ≤ m → 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := fun n m hnm ↦ by
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hcauchy : ∀ n m : ℕ, n ≤ m → ∀ i, ‖a n i - a m i‖ < 1 / ((n : ℝ) + 1) := by
    intro n m hnm i
    have h1 := hv'.norm_le (a n - a m) i
    rw [map_sub, Finsupp.sub_apply] at h1
    refine h1.trans_lt ?_
    have : d n - d m = (x - d m) - (x - d n) := by abel
    calc ‖d n - d m‖ = ‖(x - d m) - (x - d n)‖ := by rw [this]
      _ ≤ max ‖x - d m‖ ‖x - d n‖ := norm_sub_le_max _ _
      _ < 1 / ((n : ℝ) + 1) := max_lt ((ha m).trans_le (hmono n m hnm)) (ha n)
  have hlim : ∀ i, ∃ c, Tendsto (fun n ↦ a n i) atTop (𝓝 c) := by
    intro i
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact (hcauchy N n hn i).trans hN
  choose c hc using hlim
  have hbound : ∀ n i, ‖a n i - c i‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n i
    have ht : Tendsto (fun m ↦ ‖a n i - a m i‖) atTop (𝓝 ‖a n i - c i‖) :=
      ((hc i).const_sub (a n i)).norm
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hcauchy n m hm i).le
  refine ⟨c, ?_, ?_⟩
  · change Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, c i • v i) atTop (𝓝 x)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨(a n).support, fun s hs ↦ ?_⟩
    rw [dist_eq_norm]
    have hdn : d n = ∑ i ∈ s, a n i • v i := by
      change Finsupp.linearCombination K v (a n) = _
      rw [Finsupp.linearCombination_apply]
      exact Finsupp.sum_of_support_subset _ hs _ fun i _ ↦ zero_smul K (v i)
    have heq : ∑ i ∈ s, c i • v i - x = (d n - x) - ∑ i ∈ s, (a n i - c i) • v i := by
      rw [hdn]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [heq]
    refine (norm_sub_le_max _ _).trans_lt (lt_of_le_of_lt (max_le ?_ ?_) hn)
    · rw [norm_sub_rev]
      exact (ha n).le
    · exact hv'.norm_sum_smul_le s _ (by positivity) fun i _ ↦ hbound n i
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hx)
    have hdn : ‖d n‖ = ‖x‖ := norm_eq_of_norm_sub_lt ((ha n).trans hn)
    have han : a n ≠ 0 := by
      intro h0
      have : d n = 0 := by rw [hd]; simp [h0]
      rw [this, norm_zero] at hdn
      exact hx (norm_eq_zero.mp hdn.symm)
    obtain ⟨i, hi⟩ := hv'.exists_norm_linearCombination_eq (a n) han
    refine ⟨i, ?_⟩
    have hi' : ‖a n i‖ = ‖x‖ := hi.symm.trans hdn
    have h1 : ‖a n i - c i‖ < ‖a n i‖ := by
      rw [hi']
      exact (hbound n i).trans_lt hn
    rw [norm_eq_of_norm_sub_lt h1, hi']

/-- **Expansions in an orthonormal Schauder basis** (complete `K`): every `x` has a unique
expansion `x = ∑ cᵢ vᵢ`. -/
theorem existsUnique_hasSum (x : E) : ∃! c : ι → K, HasSum (fun i ↦ c i • v i) x := by
  obtain ⟨c, hc, -⟩ := hv.exists_hasSum x
  exact ⟨c, hc, fun c' hc' ↦ hv.toIsOrthonormalFamily.eq_of_hasSum hc' hc⟩

end IsOrthonormalSchauderBasis

/-! ### Lifted residue bases -/

section Lift

variable {k F ι : Type*} [NormedField k] [IsUltrametricDist k] [NormedField F]
  [IsUltrametricDist F] [NormedAlgebra k F]

/-- **Lifted residue bases, (1)**: lifts of `k̃`-linearly independent residues form an orthonormal
family over `k`. -/
theorem isOrthonormalFamily_of_linearIndependent_residue (b : ι → unitBall F)
    (hb : LinearIndependent (ResidueField (unitBall k)) fun i ↦ residue (unitBall F) (b i)) :
    IsOrthonormalFamily k fun i ↦ (b i : F) where
  norm_eq_one i := norm_eq_one_of_residue_ne_zero (hb.ne_zero i)
  norm_le a i := by
    classical
    by_cases hi : i ∈ a.support
    swap
    · rw [Finsupp.notMem_support_iff.mp hi, norm_zero]
      exact norm_nonneg _
    have : Nonempty a.support := ⟨⟨i, hi⟩⟩
    obtain ⟨i₀, h1, h2⟩ := exists_norm_sum_smul_eq (K := k) (fun j : a.support ↦ b j)
      (hb.comp _ Subtype.val_injective) (fun j ↦ a j)
    have hsum : Finsupp.linearCombination k (fun i ↦ (b i : F)) a =
        ∑ j : a.support, a j • (b j : F) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum,
        ← Finset.sum_coe_sort a.support (fun j ↦ a j • (b j : F))]
    rw [hsum, h1]
    exact h2 ⟨i, hi⟩

/-- **Lifted residue bases, (2)**: let `k₀` be a coefficient field of `k` and `F₀ ⊇ k₀` a
coefficient field of `F`. If `bᵢ ∈ F₀` and the residues `b̃ᵢ` span `F̃` over `k̃`, then `F₀` lies
in the `k`-span of the `bᵢ`. -/
theorem IsCoefficientField.mem_span_of_span_residue {k₀ : Subfield k}
    (hk₀ : IsCoefficientField k₀) {F₀ : Subfield F} (hF₀ : IsCoefficientField F₀)
    (hk₀F₀ : k₀.map (algebraMap k F) ≤ F₀) (b : ι → unitBall F) (hbF₀ : ∀ i, (b i : F) ∈ F₀)
    (hspan : Submodule.span (ResidueField (unitBall k))
      (Set.range fun i ↦ residue (unitBall F) (b i)) = ⊤)
    {x : F} (hx : x ∈ F₀) : x ∈ Submodule.span k (Set.range fun i ↦ (b i : F)) := by
  set X : unitBall F := ⟨x, mem_unitBall.mpr (hF₀.norm_le_one x hx)⟩
  have hX : residue (unitBall F) X ∈ Submodule.span (ResidueField (unitBall k))
      (Set.range fun i ↦ residue (unitBall F) (b i)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨γ, hγ⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hX
  set c : ι → k := fun i ↦ (hk₀.residueEquiv.symm (γ i) : k)
  have hc : ∀ i, ‖c i‖ ≤ 1 := fun i ↦ hk₀.norm_le_one _ (hk₀.residueEquiv.symm (γ i)).2
  have hcres : ∀ i, residue (unitBall k) ⟨c i, mem_unitBall.mpr (hc i)⟩ = γ i := fun i ↦
    hk₀.residue_residueEquiv_symm (γ i)
  set y : F := ∑ i ∈ γ.support, c i • (b i : F)
  have hy : y ∈ Submodule.span k (Set.range fun i ↦ (b i : F)) :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hyF₀ : y ∈ F₀ := F₀.sum_mem fun i _ ↦ by
    rw [Algebra.smul_def]
    exact F₀.mul_mem (hk₀F₀ ⟨c i, (hk₀.residueEquiv.symm (γ i)).2, rfl⟩) (hbF₀ i)
  set Y : unitBall F := ∑ i ∈ γ.support,
    algebraMap (unitBall k) (unitBall F) ⟨c i, mem_unitBall.mpr (hc i)⟩ * b i
  have hYcoe : (Y : F) = y := by
    simp only [Y, y, Algebra.smul_def]
    push_cast
    rfl
  have hresY : residue (unitBall F) Y = residue (unitBall F) X := by
    rw [← hγ, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, ← algebraMap_residue, hcres, Algebra.smul_def]
  have hlt : ‖x - y‖ < 1 := by
    have := residue_eq_residue_iff.mp hresY.symm
    rwa [hYcoe] at this
  have h0 : x - y = 0 :=
    eq_zero_of_mem_of_norm_lt_one hF₀.norm_le_one (F₀.sub_mem hx hyF₀) hlt
  rw [sub_eq_zero.mp h0]
  exact hy

/-- **Orthogonality to `L^p` from residues.** Let `k` be algebraically closed and `F` of
characteristic `p`. Let `bᵢ ∈ F°` have `k̃`-linearly independent residues whose span meets `F̃^p`
only in `0`. Then every `u ∈ span_k (bᵢ)` is orthogonal to `F^p`: `‖u‖ ≤ ‖u + c^p‖`. -/
theorem norm_le_norm_add_pow_of_residue [IsAlgClosed k] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (b : ι → unitBall F)
    (hb : LinearIndependent (ResidueField (unitBall k)) fun i ↦ residue (unitBall F) (b i))
    (hdisj : ∀ f ∈ Submodule.span (ResidueField (unitBall k))
      (Set.range fun i ↦ residue (unitBall F) (b i)), ∀ g, g ^ p = f → f = 0)
    {u : F} (hu : u ∈ Submodule.span k (Set.range fun i ↦ (b i : F))) (c : F) :
    ‖u‖ ≤ ‖u + c ^ p‖ := by
  classical
  have hv := isOrthonormalFamily_of_linearIndependent_residue b hb
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
  rw [← Finsupp.linearCombination_apply]
  rcases eq_or_ne l 0 with rfl | hl
  · simp
  obtain ⟨j, hj⟩ := hv.exists_norm_linearCombination_eq l hl
  have hmax : ∀ i, ‖l i‖ ≤ ‖l j‖ := fun i ↦ hj ▸ hv.norm_le l i
  have hlj : l j ≠ 0 := by
    intro h0
    apply hl
    ext i
    have := hmax i
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hljpos : 0 < ‖l j‖ := norm_pos_iff.mpr hlj
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (l j)⁻¹ hp.out.pos
  set u := Finsupp.linearCombination k (fun i ↦ (b i : F)) l
  by_contra hlt
  rw [not_le] at hlt
  -- rescale
  have hμn : ‖μ ^ p‖ = ‖l j‖⁻¹ := by rw [hμ, norm_inv]
  set u' := Finsupp.linearCombination k (fun i ↦ (b i : F)) ((μ ^ p) • l)
  have hu' : u' = algebraMap k F (μ ^ p) * u := by
    simp only [u', u, map_smul, Algebra.smul_def]
  have hu'n : ‖u'‖ = 1 := by
    rw [hu', norm_mul, norm_algebraMap', hμn, hj]
    exact inv_mul_cancel₀ hljpos.ne'
  set w := algebraMap k F μ * c
  have hw : u' + w ^ p = algebraMap k F (μ ^ p) * (u + c ^ p) := by
    rw [hu', mul_pow, ← map_pow, mul_add]
  have hlt' : ‖u' + w ^ p‖ < 1 := by
    rw [hw, norm_mul, norm_algebraMap', hμn]
    calc ‖l j‖⁻¹ * ‖u + c ^ p‖ < ‖l j‖⁻¹ * ‖u‖ :=
          mul_lt_mul_of_pos_left hlt (inv_pos.mpr hljpos)
      _ = 1 := by rw [hj]; exact inv_mul_cancel₀ hljpos.ne'
  have hneg : (-w) ^ p = -w ^ p := by
    rw [neg_pow, neg_one_pow_char F p, neg_one_mul]
  have hwp : ‖(-w) ^ p‖ = 1 := by
    have : ‖u' - (-w) ^ p‖ < ‖u'‖ := by rwa [hneg, sub_neg_eq_add, hu'n]
    rw [norm_eq_of_norm_sub_lt this, hu'n]
  have hw1 : ‖-w‖ ≤ 1 := by
    rw [norm_pow] at hwp
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp hwp).le
  have hcoef : ∀ i, ‖((μ ^ p) • l) i‖ ≤ 1 := fun i ↦ by
    rw [Finsupp.smul_apply, smul_eq_mul, norm_mul, hμn]
    calc ‖l j‖⁻¹ * ‖l i‖ ≤ ‖l j‖⁻¹ * ‖l j‖ :=
          mul_le_mul_of_nonneg_left (hmax i) (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := inv_mul_cancel₀ hljpos.ne'
  set U' : unitBall F := ∑ i ∈ ((μ ^ p) • l).support,
    algebraMap (unitBall k) (unitBall F) ⟨((μ ^ p) • l) i, mem_unitBall.mpr (hcoef i)⟩ * b i
  have hU' : (U' : F) = u' := by
    simp only [U', u', Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def]
    push_cast
    rfl
  set W : unitBall F := ⟨-w, mem_unitBall.mpr hw1⟩
  have hres0 : residue (unitBall F) (U' - W ^ p) = 0 := by
    rw [residue_eq_zero_iff_norm_lt_one]
    change ‖(U' : F) - (-w) ^ p‖ < 1
    rwa [hU', hneg, sub_neg_eq_add]
  have hres : residue (unitBall F) U' = (residue (unitBall F) W) ^ p := by
    rw [map_sub, map_pow, sub_eq_zero] at hres0
    exact hres0
  have hspan : residue (unitBall F) U' ∈ Submodule.span (ResidueField (unitBall k))
      (Set.range fun i ↦ residue (unitBall F) (b i)) := by
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_mul, ← algebraMap_residue, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h0 := hdisj _ hspan _ hres.symm
  have := residue_eq_zero_iff_norm_lt_one.mp h0
  rw [hU', hu'n] at this
  exact lt_irrefl _ this

end Lift

/-! ### Temkin's Proposition 6.2.5, type 2 -/

section TypeTwo

variable {k K L : Type*} [NormedField k] [IsUltrametricDist k] [IsAlgClosed k] [NormedField K]
  [IsUltrametricDist K] [NormedAlgebra k K] [NormedField L] [IsUltrametricDist L]
  [CompleteSpace L] [NormedAlgebra k L] [NormedAlgebra K L] [IsScalarTower k K L]

/-- **Temkin, Proposition 6.2.5, type 2.** Let `k` be algebraically closed of characteristic `p`,
`z` a Gauss generator of `K` over `k`, and `L/K` a finite extension with `L` complete,
`[L : K] ≤ [L̃ : K̃]` (so `[L : K] = [L̃ : K̃]`) and `L̃/K̃` separable. Then there is `U ⊆ L` such
that
`B = {1} ⊔ U ⊔ U^p ⊔ U^{p²} ⊔ ⋯` is an orthonormal Schauder basis of `L` over `k` and every
element of `span_k U` is orthogonal to `L^p`. -/
theorem IsGaussGenerator.exists_frobeniusFamily_isOrthonormalSchauderBasis (p : ℕ)
    [hp : Fact p.Prime] [CharP k p] {z : K} (hz : IsGaussGenerator k z) [FiniteDimensional K L]
    (hf : finrank K L ≤ inertiaDegree K L)
    [Algebra.IsSeparable (ResidueField (unitBall K)) (ResidueField (unitBall L))] :
    ∃ U : Set L, IsOrthonormalSchauderBasis k (FunctionField.frobeniusFamily p U) ∧
      ∀ u ∈ Submodule.span k U, ∀ c : L, ‖u‖ ≤ ‖u + c ^ p‖ := by
  classical
  -- coefficient fields
  obtain ⟨k₀, hk₀, -⟩ := exists_isCoefficientField (F := k) p
  have : IsAlgClosed (ResidueField (unitBall k)) := isAlgClosed_residueField_of_charP (F := k) p
  have hK₀ := hz.isCoefficientField_adjoin hk₀
  obtain ⟨L₀, hK₀L₀, hL₀⟩ := hK₀.exists_isCoefficientField_map_le (L := L)
  have hk₀L₀ : k₀.map (algebraMap k L) ≤ L₀ := by
    rintro _ ⟨c, hc, rfl⟩
    refine hK₀L₀ ⟨algebraMap k K c, ?_, (IsScalarTower.algebraMap_apply k K L c).symm⟩
    exact (k₀⟮z⟯).algebraMap_mem (⟨c, hc⟩ : k₀)
  have hzL₀ : algebraMap K L z ∈ L₀ :=
    hK₀L₀ ⟨z, IntermediateField.mem_adjoin_simple_self k₀ z, rfl⟩
  -- characteristic `p`
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have : CharP (ResidueField (unitBall L)) p := by
    refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
    have h : (p : unitBall L) = 0 := Subtype.ext (by simp)
    rw [← map_natCast (residue (unitBall L)), h, map_zero]
  -- `L̃` is a function field of one variable over `k̃`
  set zt : ResidueField (unitBall L) :=
    residue (unitBall L)
      ⟨algebraMap K L z, mem_unitBall.mpr (hz.toIsGaussElement.map L).norm_le_one⟩
  have htr : Transcendental (ResidueField (unitBall k)) zt :=
    (hz.toIsGaussElement.map L).transcendental_residue
  set E := (ResidueField (unitBall k))⟮zt⟯
  have hrange : ∀ y : ResidueField (unitBall K),
      algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L)) y ∈ E := by
    intro y
    have hy : y ∈ (ResidueField (unitBall k))⟮residue (unitBall K)
        ⟨z, mem_unitBall.mpr hz.norm_le_one⟩⟯ := by
      rw [hz.adjoin_residue_eq_top hk₀]
      exact IntermediateField.mem_top
    set f := IsScalarTower.toAlgHom (ResidueField (unitBall k)) (ResidueField (unitBall K))
      (ResidueField (unitBall L))
    have hmap : f y ∈ IntermediateField.map f ((ResidueField (unitBall k))⟮residue (unitBall K)
        ⟨z, mem_unitBall.mpr hz.norm_le_one⟩⟯) := ⟨y, hy, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
    convert hmap using 3 <;> rfl
  let _ : Algebra (ResidueField (unitBall K)) E :=
    (RingHom.codRestrict (algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L))) E
      hrange).toAlgebra
  have : IsScalarTower (ResidueField (unitBall K)) E (ResidueField (unitBall L)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite E (ResidueField (unitBall L)) :=
    Module.Finite.of_restrictScalars_finite (ResidueField (unitBall K)) E
      (ResidueField (unitBall L))
  have hFF : FunctionField.IsFunctionFieldOneVar (ResidueField (unitBall k))
      (ResidueField (unitBall L)) :=
    FunctionField.IsFunctionFieldOneVar.of_finiteDimensional_adjoin htr
  -- the Frobenius basis of `L̃`
  obtain ⟨Ut, -, hli, hspan, hdisj⟩ :=
    FunctionField.exists_frobeniusBasis_of_isAlgClosed (E := ResidueField (unitBall k)) p hFF
  -- lifting to `L₀`
  set ψ : ResidueField (unitBall L) →+* L := L₀.subtype.comp hL₀.residueEquiv.symm.toRingHom
  have hψL₀ : ∀ y, ψ y ∈ L₀ := fun y ↦ (hL₀.residueEquiv.symm y).2
  have hψn : ∀ y, ‖ψ y‖ ≤ 1 := fun y ↦ hL₀.norm_le_one _ (hψL₀ y)
  have hψres : ∀ y, residue (unitBall L) ⟨ψ y, mem_unitBall.mpr (hψn y)⟩ = y := fun y ↦
    hL₀.residue_residueEquiv_symm y
  have hψinj : Function.Injective ψ := ψ.injective
  set U : Set L := ψ '' Ut
  set e₀ : Ut ≃ U := Equiv.Set.image ψ Ut hψinj
  set e : Option (ℕ × Ut) ≃ Option (ℕ × U) :=
    Equiv.optionCongr (Equiv.prodCongr (Equiv.refl ℕ) e₀)
  have hBe : ∀ ι, FunctionField.frobeniusFamily p U ι =
      ψ (FunctionField.frobeniusFamily p Ut (e.symm ι)) := by
    intro ι
    obtain ⟨ι, rfl⟩ := e.surjective ι
    rw [Equiv.symm_apply_apply]
    rcases ι with _ | ⟨j, ut⟩
    · change (1 : L) = ψ 1
      rw [map_one]
    · change ((e₀ ut : U) : L) ^ p ^ j = ψ ((ut : ResidueField (unitBall L)) ^ p ^ j)
      rw [map_pow]
      rfl
  have hBn : ∀ ι, ‖FunctionField.frobeniusFamily p U ι‖ ≤ 1 := fun ι ↦ by
    rw [hBe]
    exact hψn _
  set b : Option (ℕ × U) → unitBall L :=
    fun ι ↦ ⟨FunctionField.frobeniusFamily p U ι, mem_unitBall.mpr (hBn ι)⟩
  have hbres : ∀ ι, residue (unitBall L) (b ι) = FunctionField.frobeniusFamily p Ut (e.symm ι) := by
    intro ι
    have : b ι = ⟨ψ (FunctionField.frobeniusFamily p Ut (e.symm ι)),
        mem_unitBall.mpr (hψn _)⟩ := Subtype.ext (hBe ι)
    rw [this, hψres]
  have hbli : LinearIndependent (ResidueField (unitBall k)) fun ι ↦ residue (unitBall L) (b ι) := by
    simp_rw [hbres]
    exact hli.comp _ e.symm.injective
  have hbspan : Submodule.span (ResidueField (unitBall k))
      (Set.range fun ι ↦ residue (unitBall L) (b ι)) = ⊤ := by
    simp_rw [hbres]
    rw [show (fun ι ↦ FunctionField.frobeniusFamily p Ut (e.symm ι)) =
      FunctionField.frobeniusFamily p Ut ∘ e.symm from rfl, e.symm.surjective.range_comp, hspan]
  have horth : IsOrthonormalFamily k (FunctionField.frobeniusFamily p U) :=
    isOrthonormalFamily_of_linearIndependent_residue b hbli
  -- density
  have hsub : (Algebra.adjoin k (L₀ : Set L) : Set L) ⊆
      Submodule.span k (Set.range (FunctionField.frobeniusFamily p U)) := by
    intro x hx
    have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin k (L₀ : Set L)) := hx
    have hcl : Submonoid.closure (L₀ : Set L) = L₀.toSubmonoid := Submonoid.closure_eq _
    rw [Algebra.adjoin_eq_span, hcl] at hx'
    refine (Submodule.span_le.mpr fun y hy ↦ ?_) hx'
    exact IsCoefficientField.mem_span_of_span_residue hk₀ hL₀ hk₀L₀ b
      (fun ι ↦ by change FunctionField.frobeniusFamily p U ι ∈ L₀; rw [hBe]; exact hψL₀ _)
      hbspan hy
  have hdense := (dense_adjoin_of_isCoefficientField hk₀ hz hf hL₀ hk₀L₀ hzL₀).mono hsub
  refine ⟨U, ⟨horth, hdense⟩, ?_⟩
  -- orthogonality of `span_k U` to `L^p`
  have hUn : ∀ u : U, ‖(u : L)‖ ≤ 1 := fun u ↦ by
    obtain ⟨_, ⟨y, -, rfl⟩⟩ := u
    exact hψn y
  set bU : U → unitBall L := fun u ↦ ⟨u, mem_unitBall.mpr (hUn u)⟩
  have hbUres : ∀ u, residue (unitBall L) (bU u) = (e₀.symm u : ResidueField (unitBall L)) := by
    intro u
    obtain ⟨ut, rfl⟩ := e₀.surjective u
    rw [Equiv.symm_apply_apply]
    have : bU (e₀ ut) = ⟨ψ ut, mem_unitBall.mpr (hψn _)⟩ := Subtype.ext rfl
    rw [this, hψres]
  have hbUli : LinearIndependent (ResidueField (unitBall k))
      fun u ↦ residue (unitBall L) (bU u) := by
    have hinj : Function.Injective fun u : U ↦ (some (0, e₀.symm u) : Option (ℕ × Ut)) := by
      intro u v huv
      simpa using huv
    have hfun : (fun u ↦ residue (unitBall L) (bU u)) =
        FunctionField.frobeniusFamily p Ut ∘
          fun u : U ↦ (some (0, e₀.symm u) : Option (ℕ × Ut)) := by
      funext u
      rw [hbUres]
      change _ = ((e₀.symm u : Ut) : ResidueField (unitBall L)) ^ p ^ 0
      rw [pow_zero, pow_one]
    rw [hfun]
    exact hli.comp _ hinj
  have hbUrange : Set.range (fun u ↦ residue (unitBall L) (bU u)) = Ut := by
    ext y
    simp only [Set.mem_range, hbUres]
    constructor
    · rintro ⟨u, rfl⟩
      exact (e₀.symm u).2
    · intro hy
      exact ⟨e₀ ⟨y, hy⟩, by simp⟩
  intro u hu c
  have hu' : u ∈ Submodule.span k (Set.range fun v ↦ (bU v : L)) := by
    rwa [show (Set.range fun v ↦ (bU v : L)) = U from Subtype.range_coe]
  refine norm_le_norm_add_pow_of_residue bU hbUli ?_ hu' c
  rw [hbUrange]
  exact hdisj

end TypeTwo

end DeJongAlterations.StableModification.Valuation.Analytic
