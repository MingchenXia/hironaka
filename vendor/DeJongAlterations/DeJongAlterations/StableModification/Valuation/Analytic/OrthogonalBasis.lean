/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Orthogonal and `r`-orthogonal families in non-archimedean normed spaces

Let `K` be a non-archimedean normed field and `E` a non-archimedean normed `K`-space. A finite
family `v` in `E` is `r`-orthogonal if `‖∑ aⱼ vⱼ‖ ≥ r ‖aᵢ vᵢ‖` for all coefficients and all `i`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, 2.6.1; Temkin, *Stable modification of
relative curves*, proof of Lemma 6.3.3, `semi-stable.tex` lines 4019–4025). For `r = 1` this is
orthogonality in the sense of Temkin §2.1 (line 2005): `‖∑ aⱼ vⱼ‖ = maxⱼ ‖aⱼ vⱼ‖`.

## Main results

* `IsROrthogonal.linearIndependent`: an `r`-orthogonal family of nonzero vectors with `r > 0` is
  linearly independent.
* `exists_basis_isROrthogonal` (BGR 2.6.1/3): if `K` is complete and nontrivially normed, every
  finite-dimensional non-archimedean normed `K`-space has an `r`-orthogonal basis for each `r < 1`.
* `IsROrthogonal.exists_forall_norm_sub_smul_le`: if `E` has an orthogonal basis, then for all
  `x, u ∈ E` the distance from `x` to the line `K u` is attained.

The existence proof is the classical induction on the dimension: a finite-dimensional subspace
`V` is closed, so a vector `x ∉ V` has positive distance `d` to `V`, and for `r < 1` some `v ∈ V`
with `‖x - v‖ < d / r` makes `x - v` `r`-orthogonal to `V`.
-/

noncomputable section

open Module

namespace DeJongAlterations.StableModification.Valuation.Analytic

section Defs

variable (K : Type*) {E ι : Type*} [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  [Fintype ι]

/-- A finite family `v` in a normed `K`-space is `r`-orthogonal if `r ‖aᵢ vᵢ‖ ≤ ‖∑ⱼ aⱼ vⱼ‖` for all
coefficients `a` and all indices `i` (BGR 2.6.1). A `1`-orthogonal family is called orthogonal. -/
def IsROrthogonal (r : ℝ) (v : ι → E) : Prop :=
  ∀ (a : ι → K) (i : ι), r * ‖a i • v i‖ ≤ ‖∑ j, a j • v j‖

variable {K}

theorem IsROrthogonal.mono {r s : ℝ} {v : ι → E} (h : IsROrthogonal K r v) (hsr : s ≤ r) :
    IsROrthogonal K s v := fun a i ↦ (mul_le_mul_of_nonneg_right hsr (norm_nonneg _)).trans (h a i)

theorem isROrthogonal_of_nonpos {r : ℝ} (hr : r ≤ 0) (v : ι → E) : IsROrthogonal K r v :=
  fun _ _ ↦ (mul_nonpos_of_nonpos_of_nonneg hr (norm_nonneg _)).trans (norm_nonneg _)

/-- `r`-orthogonality does not depend on the indexing. -/
theorem IsROrthogonal.comp_equiv {ι' : Type*} [Fintype ι'] {r : ℝ} {v : ι → E}
    (h : IsROrthogonal K r v) (e : ι' ≃ ι) : IsROrthogonal K r (v ∘ e) := by
  intro a i
  have := h (a ∘ e.symm) (e i)
  rw [← e.sum_comp] at this
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this

/-- A subfamily of an `r`-orthogonal family is `r`-orthogonal. -/
theorem IsROrthogonal.comp_injective {ι' : Type*} [Fintype ι'] {r : ℝ} {v : ι → E}
    (h : IsROrthogonal K r v) {e : ι' → ι} (he : Function.Injective e) :
    IsROrthogonal K r (v ∘ e) := by
  classical
  intro a i
  set A : ι → K := Function.extend e a 0
  have hA : ∀ j, A (e j) = a j := fun j ↦ he.extend_apply a 0 j
  have hsum : ∑ j, a j • (v ∘ e) j = ∑ k, A k • v k := by
    refine Fintype.sum_of_injective e he _ _ (fun k hk ↦ ?_) (fun j ↦ by simp [hA])
    have : A k = 0 := by
      simp only [A]
      rw [Function.extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply]
    rw [this, zero_smul]
  have := h A (e i)
  rwa [hA, ← hsum] at this

/-- An `r`-orthogonal family of nonzero vectors with `r > 0` is linearly independent. -/
theorem IsROrthogonal.linearIndependent {r : ℝ} {v : ι → E} (h : IsROrthogonal K r v)
    (hr : 0 < r) (hv : ∀ i, ‖v i‖ ≠ 0) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have := h a i
  rw [ha, norm_zero, norm_smul] at this
  have h0 : ‖a i‖ * ‖v i‖ ≤ 0 := by nlinarith [norm_nonneg (a i), norm_nonneg (v i)]
  have : ‖a i‖ * ‖v i‖ = 0 := le_antisymm h0 (by positivity)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact norm_eq_zero.mp h1
  · exact absurd h1 (hv i)

/-- For an orthogonal family in a non-archimedean space, `‖∑ⱼ aⱼ vⱼ‖ = maxⱼ ‖aⱼ vⱼ‖`. -/
theorem IsROrthogonal.norm_sum_eq_sup [IsUltrametricDist E] [Nonempty ι] {v : ι → E}
    (h : IsROrthogonal K 1 v) (a : ι → K) :
    ‖∑ j, a j • v j‖ = Finset.univ.sup' Finset.univ_nonempty (fun j ↦ ‖a j • v j‖) := by
  refine le_antisymm ?_ ?_
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ?_ fun j _ ↦ ?_
    · obtain ⟨j⟩ := ‹Nonempty ι›
      exact (norm_nonneg _).trans (Finset.le_sup' (fun j ↦ ‖a j • v j‖) (Finset.mem_univ j))
    · exact Finset.le_sup' (fun j ↦ ‖a j • v j‖) (Finset.mem_univ j)
  · exact Finset.sup'_le _ _ fun j _ ↦ by simpa using h a j

end Defs

/-! ### Existence of `r`-orthogonal bases -/

section Existence

variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K] [NormedAddCommGroup E]
  [NormedSpace K E] [IsUltrametricDist E]

/-- Let `V` be a finite-dimensional subspace and `x ∉ V`. For `0 < r < 1` there is `v ∈ V` such that
`x - v` is `r`-orthogonal to `V`: `r · max ‖x - v‖ ‖w‖ ≤ ‖(x - v) + w‖` for all `w ∈ V`. -/
theorem exists_isROrthogonal_complement (V : Submodule K E) [FiniteDimensional K V] {x : E}
    (hx : x ∉ V) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ v ∈ V, ∀ w ∈ V, r * max ‖x - v‖ ‖w‖ ≤ ‖(x - v) + w‖ := by
  have hV : IsClosed (V : Set E) := V.closed_of_finiteDimensional
  have hne : (V : Set E).Nonempty := ⟨0, V.zero_mem⟩
  set d := Metric.infDist x (V : Set E) with hd
  have hdpos : 0 < d := by
    rw [hd, ← Metric.infDist_pos_iff_notMem_closure hne, hV.closure_eq] at *
    exact hx
  have hlt : d < d / r := by
    rw [lt_div_iff₀ hr0]
    nlinarith
  obtain ⟨v, hvV, hv⟩ := (Metric.infDist_lt_iff hne).mp hlt
  rw [dist_eq_norm] at hv
  refine ⟨v, hvV, fun w hw ↦ ?_⟩
  -- `‖(x - v) + w‖ ≥ d` because `v - w ∈ V`
  have hdle : d ≤ ‖(x - v) + w‖ := by
    have : (x - v) + w = x - (v - w) := by abel
    rw [this, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (V.sub_mem hvV hw)
  have h1 : r * ‖x - v‖ < ‖(x - v) + w‖ := by
    calc r * ‖x - v‖ < r * (d / r) := mul_lt_mul_of_pos_left hv hr0
      _ = d := by field_simp
      _ ≤ _ := hdle
  rcases le_or_gt ‖w‖ ‖x - v‖ with hw' | hw'
  · rw [max_eq_left hw']
    exact h1.le
  · rw [max_eq_right hw'.le]
    -- ultrametric: `‖w‖ ≤ max ‖(x - v) + w‖ ‖x - v‖` and `‖x - v‖ < ‖w‖`
    have h2 : ‖w‖ ≤ max ‖(x - v) + w‖ ‖x - v‖ := by
      have := norm_sub_le_max ((x - v) + w) (x - v)
      rwa [add_sub_cancel_left] at this
    have h3 : ‖w‖ ≤ ‖(x - v) + w‖ := by
      rcases le_max_iff.mp h2 with h | h
      · exact h
      · exact absurd h (not_le.mpr hw')
    calc r * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hr1.le (norm_nonneg _)
      _ = ‖w‖ := one_mul _
      _ ≤ _ := h3

/-- Inductive step: an `r`-orthogonal independent family of length `n < dim E` extends to an
`r²`-orthogonal independent family of length `n + 1`. -/
theorem exists_snoc_isROrthogonal [FiniteDimensional K E] {n : ℕ} {b : Fin n → E}
    (hb : LinearIndependent K b) (hn : n < finrank K E) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hbo : IsROrthogonal K r b) :
    ∃ x : E, LinearIndependent K (Fin.snoc b x : Fin (n + 1) → E) ∧
      IsROrthogonal K (r * r) (Fin.snoc b x : Fin (n + 1) → E) := by
  set V := Submodule.span K (Set.range b)
  have hVlt : V ≠ ⊤ := by
    intro hV
    have : finrank K V = n := by
      rw [finrank_span_eq_card hb, Fintype.card_fin]
    rw [hV, finrank_top] at this
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ∉ V := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hVlt (eq_top_iff.mpr fun y _ ↦ h y)
  obtain ⟨v, hvV, hv⟩ := exists_isROrthogonal_complement V hx₀ hr0 hr1
  have hxV : x₀ - v ∉ V := fun h ↦ hx₀ (by simpa using V.add_mem h hvV)
  refine ⟨x₀ - v, linearIndependent_finSnoc.mpr ⟨hb, hxV⟩, fun a i ↦ ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  set w := ∑ j : Fin n, a (Fin.castSucc j) • b j with hw
  have hwV : w ∈ V :=
    Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- the key estimate `r · max ‖c (x₀ - v)‖ ‖w‖ ≤ ‖w + c (x₀ - v)‖`
  have key : r * max ‖a (Fin.last n) • (x₀ - v)‖ ‖w‖ ≤ ‖w + a (Fin.last n) • (x₀ - v)‖ := by
    set c := a (Fin.last n)
    rcases eq_or_ne c 0 with hc | hc
    · simp only [hc, zero_smul, norm_zero, add_zero]
      rw [max_eq_right (norm_nonneg w)]
      exact (mul_le_of_le_one_left (norm_nonneg w) hr1.le)
    · have hw' : c⁻¹ • w ∈ V := V.smul_mem _ hwV
      have := hv _ hw'
      have heq : w + c • (x₀ - v) = c • ((x₀ - v) + c⁻¹ • w) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
      rw [heq, norm_smul, norm_smul]
      have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
      calc r * max (‖c‖ * ‖x₀ - v‖) ‖w‖
          = ‖c‖ * (r * max ‖x₀ - v‖ (‖c‖⁻¹ * ‖w‖)) := by
            have hm : ‖c‖ * max ‖x₀ - v‖ (‖c‖⁻¹ * ‖w‖) = max (‖c‖ * ‖x₀ - v‖) ‖w‖ := by
              rw [mul_max_of_nonneg _ _ hcpos.le, mul_inv_cancel_left₀ hcpos.ne']
            rw [← hm]
            ring
        _ ≤ ‖c‖ * ‖(x₀ - v) + c⁻¹ • w‖ := by
            apply mul_le_mul_of_nonneg_left _ hcpos.le
            rwa [norm_smul, norm_inv] at this
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.snoc_last]
    calc r * r * ‖a (Fin.last n) • (x₀ - v)‖ ≤ r * ‖a (Fin.last n) • (x₀ - v)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hr0.le hr1.le) (norm_nonneg _)
      _ ≤ r * max ‖a (Fin.last n) • (x₀ - v)‖ ‖w‖ :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hr0.le
      _ ≤ _ := key
  · simp only [Fin.snoc_castSucc]
    calc r * r * ‖a (Fin.castSucc j) • b j‖ ≤ r * ‖w‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hbo (fun j ↦ a (Fin.castSucc j)) j) hr0.le
      _ ≤ r * max ‖a (Fin.last n) • (x₀ - v)‖ ‖w‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hr0.le
      _ ≤ _ := key

/-- Every family length `n ≤ dim E` of `r`-orthogonal independent vectors exists, for `0 < r < 1`. -/
theorem exists_linearIndependent_isROrthogonal [FiniteDimensional K E] :
    ∀ n ≤ finrank K E, ∀ r : ℝ, 0 < r → r < 1 →
      ∃ b : Fin n → E, LinearIndependent K b ∧ IsROrthogonal K r b := by
  intro n
  induction n with
  | zero =>
    intro _ r _ _
    refine ⟨Fin.elim0, linearIndependent_empty_type, fun a i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro hn r hr0 hr1
    set s := Real.sqrt r
    have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
    have hs1 : s < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt hr0.le hr1
    obtain ⟨b, hb, hbo⟩ := ih (by omega) s hs0 hs1
    obtain ⟨x, hx, hxo⟩ := exists_snoc_isROrthogonal hb (by omega) hs0 hs1 hbo
    refine ⟨_, hx, ?_⟩
    have : s * s = r := Real.mul_self_sqrt hr0.le
    rwa [this] at hxo

/-- **BGR 2.6.1/3.** Let `K` be a complete nontrivially normed non-archimedean field and `E` a
finite-dimensional non-archimedean normed `K`-space. For every `r < 1`, `E` has an `r`-orthogonal
basis. -/
theorem exists_basis_isROrthogonal [FiniteDimensional K E] {r : ℝ} (hr : r < 1) :
    ∃ b : Basis (Fin (finrank K E)) K E, IsROrthogonal K r b := by
  rcases le_or_gt r 0 with hr0 | hr0
  · exact ⟨Module.finBasis K E, isROrthogonal_of_nonpos hr0 _⟩
  obtain ⟨b, hb, hbo⟩ := exists_linearIndependent_isROrthogonal (finrank K E) le_rfl r hr0 hr
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' b hb (by simp), ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact hbo

end Existence

/-! ### Distances to lines are attained in the presence of an orthogonal basis -/

section Distance

variable {K E ι : Type*} [NormedField K] [NormedAddCommGroup E] [NormedSpace K E]
  [IsUltrametricDist E] [Fintype ι]

/-- If `E` has an orthogonal basis, then for all `x, u ∈ E` the distance from `x` to the line
`K u` is attained: there is `c ∈ K` with `‖x - c u‖ ≤ ‖x - c' u‖` for all `c' ∈ K`. -/
theorem IsROrthogonal.exists_forall_norm_sub_smul_le (b : Basis ι K E)
    (hb : IsROrthogonal K 1 b) (x u : E) :
    ∃ c : K, ∀ c' : K, ‖x - c • u‖ ≤ ‖x - c' • u‖ := by
  classical
  set ξ := b.repr x
  set β := b.repr u
  -- expansion of `x - c • u` in the basis
  have hexp : ∀ c : K, x - c • u = ∑ i, (ξ i - c * β i) • b i := by
    intro c
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr u]
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, ξ, β]
  have hterm : ∀ c i, ‖(ξ i - c * β i) • b i‖ ≤ ‖x - c • u‖ := fun c i ↦ by
    simpa [hexp c] using hb (fun i ↦ ξ i - c * β i) i
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun c' ↦ by rw [hexp, hexp]; simp⟩
  -- choose `j` maximizing `‖β j • b j‖`
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖β i • b i‖)
    Finset.univ_nonempty
  rcases eq_or_ne (β j) 0 with hβj | hβj
  · -- then `u = 0`
    have hu : ∀ i, β i • b i = 0 := fun i ↦ by
      have := hj i (Finset.mem_univ i)
      rw [hβj, zero_smul, norm_zero] at this
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    have hu0 : u = 0 := by
      rw [← b.sum_repr u]
      exact Finset.sum_eq_zero fun i _ ↦ hu i
    exact ⟨0, fun c' ↦ by simp [hu0]⟩
  refine ⟨ξ j / β j, fun c' ↦ ?_⟩
  set c := ξ j / β j
  rw [hexp c]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ ↦ ?_
  -- `(ξ i - c β i) b i = (ξ i - c' β i) b i + (c' - c) β i b i`
  have hsplit : (ξ i - c * β i) • b i = (ξ i - c' * β i) • b i + (c' - c) • (β i • b i) := by
    rw [smul_smul, ← add_smul]
    ring_nf
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hterm c' i) ?_)
  -- `‖(c' - c) β i b i‖ ≤ ‖(c' - c) β j b j‖ = ‖(ξ j - c' β j) b j‖`
  have hj' : (c' - c) • (β j • b j) = -((ξ j - c' * β j) • b j) := by
    rw [smul_smul, ← neg_smul]
    congr 1
    simp only [c]
    field_simp
    ring
  calc ‖(c' - c) • (β i • b i)‖ = ‖c' - c‖ * ‖β i • b i‖ := norm_smul _ _
    _ ≤ ‖c' - c‖ * ‖β j • b j‖ :=
        mul_le_mul_of_nonneg_left (hj i (Finset.mem_univ i)) (norm_nonneg _)
    _ = ‖(c' - c) • (β j • b j)‖ := (norm_smul _ _).symm
    _ = ‖(ξ j - c' * β j) • b j‖ := by rw [hj', norm_neg]
    _ ≤ ‖x - c' • u‖ := hterm c' j

end Distance

end DeJongAlterations.StableModification.Valuation.Analytic
