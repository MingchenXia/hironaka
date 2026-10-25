/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.OneDim
import DeJongAlterations.StableModification.Valuation.Analytic.OrthogonalBasis
import DeJongAlterations.StableModification.Valuation.Analytic.Krasner
import DeJongAlterations.StableModification.Valuation.FunctionField.Places
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Continuity of generators: Temkin's Lemmas 6.3.2, 6.3.3 and Corollary 6.3.4

Let `k` be an algebraically closed non-archimedean field. This file proves the approximation
results of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §6.3
(`semi-stable.tex`, lines 4003–4040), for analytic `k`-fields:

* `exists_algHom_closureAdjoin` (**Temkin, Lemma 6.3.2**): if `‖z - z'‖ < ε r(z)` with `ε < 1`,
  `r(z) = inf_{a ∈ k} ‖z - a‖`, there is a `k`-embedding `φ : \overline{k(z)} → L` with
  `φ z = z'`, `‖φ x - x‖ ≤ ε ‖x‖`, and image `\overline{k(z')}`.
* `finiteDimensional_of_norm_sub_le`, `finrank_le_of_norm_sub_le` (**Temkin, Lemma 6.3.3**): if
  `φ : K → L` moves every element by at most `ε ‖x‖`, `ε < 1`, and `L/K` is finite, then `L` is
  finite over `φ(K)` of degree at most `[L : K]`.
* `IsUnramified.of_norm_sub_lt`: unramifiedness over `\overline{k(z)}` is an open condition on
  `z`.
* `finiteDimensional_closureAdjoin` (**Temkin, Corollary 6.3.4**): a one-dimensional analytic
  `k`-field is finite over `\overline{k(x)}` for every `x ∉ k`.

## References

Blueprint chapter `sm-val-onedim.tex`: `lem:sm-an-eps-close-poly`, `lem:sm-an-eps-close`,
`lem:sm-an-equal-degree`, `lem:sm-an-eps-close-unramified`, `cor:sm-an-finite`.
-/

noncomputable section

open IsLocalRing Polynomial Module Topology Filter
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### Relative approximation of products, quotients and polynomials -/

section Approx

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

/-- If `x'` and `y'` are relatively `ε`-close to `x` and `y`, so is `x' y'` to `x y`. -/
theorem norm_mul_sub_mul_lt {x x' y y' : L} {ε : ℝ} (hε : ε ≤ 1) (hx : ‖x - x'‖ < ε * ‖x‖)
    (hy : ‖y - y'‖ < ε * ‖y‖) : ‖x * y - x' * y'‖ < ε * ‖x * y‖ := by
  have hy0 : 0 < ‖y‖ := by
    by_contra h
    have : ‖y‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [this, mul_zero] at hy
    exact (norm_nonneg _).not_gt hy
  have hx0 : 0 < ‖x‖ := by
    by_contra h
    have : ‖x‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [this, mul_zero] at hx
    exact (norm_nonneg _).not_gt hx
  have hyy' : ‖y'‖ = ‖y‖ := norm_eq_of_norm_sub_lt (hy.trans_le (by nlinarith))
  have heq : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [heq, norm_mul x y]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    calc ‖x‖ * ‖y - y'‖ < ‖x‖ * (ε * ‖y‖) := mul_lt_mul_of_pos_left hy hx0
      _ = ε * (‖x‖ * ‖y‖) := by ring
  · rw [norm_mul, hyy']
    calc ‖x - x'‖ * ‖y‖ < ε * ‖x‖ * ‖y‖ := mul_lt_mul_of_pos_right hx hy0
      _ = ε * (‖x‖ * ‖y‖) := by ring

/-- If `x'` and `y'` are relatively `ε`-close to `x` and `y`, so is `x' / y'` to `x / y`. -/
theorem norm_div_sub_div_lt {x x' y y' : L} {ε : ℝ} (hε : ε ≤ 1) (hx : ‖x - x'‖ < ε * ‖x‖)
    (hy : ‖y - y'‖ < ε * ‖y‖) : ‖x / y - x' / y'‖ < ε * ‖x / y‖ := by
  have hy0 : 0 < ‖y‖ := by
    by_contra h
    have : ‖y‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [this, mul_zero] at hy
    exact (norm_nonneg _).not_gt hy
  have hyy' : ‖y'‖ = ‖y‖ := norm_eq_of_norm_sub_lt (hy.trans_le (by nlinarith))
  have hy'0 : y' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hyy'
    exact hy0.ne' hyy'.symm
  have hy00 : y ≠ 0 := norm_pos_iff.mp hy0
  -- `y'⁻¹` is relatively close to `y⁻¹`
  have hinv : ‖y⁻¹ - y'⁻¹‖ < ε * ‖y⁻¹‖ := by
    have heq : y⁻¹ - y'⁻¹ = (y' - y) / (y * y') := by field_simp
    rw [heq, norm_div, norm_mul, hyy', norm_sub_rev, norm_inv]
    rw [div_lt_iff₀ (by positivity)]
    calc ‖y - y'‖ < ε * ‖y‖ := hy
      _ = ε * ‖y‖⁻¹ * (‖y‖ * ‖y‖) := by field_simp
  have := norm_mul_sub_mul_lt hε hx hinv
  simpa [div_eq_mul_inv] using this

variable {k : Type*} [NormedField k] [IsAlgClosed k] [NormedAlgebra k L]

/-- **Polynomials** (Temkin, proof of Lemma 6.3.2): if `‖z - z'‖ < ε r(z)`, then
`‖g(z) - g(z')‖ < ε ‖g(z)‖` for every nonzero `g ∈ k[X]`. -/
theorem norm_aeval_sub_aeval_lt {z z' : L} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (h : ‖z - z'‖ < ε * radius k z) {g : k[X]} (hg : g ≠ 0) :
    ‖aeval z g - aeval z' g‖ < ε * ‖aeval z g‖ := by
  induction g using induction_on_X_sub_C_mul with
  | hC c =>
    have hc : c ≠ 0 := fun h0 ↦ hg (by rw [h0, map_zero])
    rw [aeval_C, aeval_C, sub_self, norm_zero, norm_algebraMap']
    exact mul_pos hε0 (norm_pos_iff.mpr hc)
  | hmul a g ih =>
    have hg0 : g ≠ 0 := fun h0 ↦ hg (by rw [h0, mul_zero])
    rw [map_mul, map_mul]
    refine norm_mul_sub_mul_lt hε ?_ (ih hg0)
    simp only [map_sub, aeval_X, aeval_C]
    calc ‖z - algebraMap k L a - (z' - algebraMap k L a)‖ = ‖z - z'‖ := by ring_nf
      _ < ε * radius k z := h
      _ ≤ ε * ‖z - algebraMap k L a‖ := mul_le_mul_of_nonneg_left (radius_le z a) hε0.le

end Approx

/-! ### Temkin, Lemma 6.3.2 -/

section AdjoinEquiv

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- The isomorphism `k(z) → k(z')`, `z ↦ z'`, of simple transcendental extensions. -/
def adjoinEquivOfTranscendental {z z' : L} (hz : Transcendental k z) (hz' : Transcendental k z') :
    k⟮z⟯ ≃ₐ[k] k⟮z'⟯ :=
  (RatFunc.algEquivOfTranscendental z hz).symm.trans (RatFunc.algEquivOfTranscendental z' hz')

theorem adjoinEquivOfTranscendental_gen {z z' : L} (hz : Transcendental k z)
    (hz' : Transcendental k z') :
    (adjoinEquivOfTranscendental hz hz' (IntermediateField.AdjoinSimple.gen k z) : L) = z' := by
  simp [adjoinEquivOfTranscendental]

end AdjoinEquiv

section EpsClose

variable {k L : Type*} [NontriviallyNormedField k] [IsAlgClosed k] [NormedField L]
  [IsUltrametricDist L] [NormedAlgebra k L]

omit [IsAlgClosed k] [IsUltrametricDist L] in
theorem notMem_range_of_radius_pos {z : L} (h : 0 < radius k z) :
    z ∉ Set.range (algebraMap k L) := by
  rintro ⟨c, rfl⟩
  have := radius_le (algebraMap k L c) c
  rw [sub_self, norm_zero] at this
  linarith

omit [IsUltrametricDist L] in
/-- An element outside the algebraically closed field `k` is transcendental over it. -/
theorem transcendental_of_notMem_range {z : L} (h : z ∉ Set.range (algebraMap k L)) :
    Transcendental k z := fun halg ↦ by
  obtain ⟨c, hc⟩ := mem_range_of_isAlgebraic_of_isAlgClosed halg
  exact h ⟨c, hc⟩

omit [IsAlgClosed k] [IsUltrametricDist L] in
theorem notMem_range_of_norm_sub_lt {z z' : L} {ε : ℝ} (hε : ε ≤ 1)
    (h : ‖z - z'‖ < ε * radius k z) : z' ∉ Set.range (algebraMap k L) := by
  rintro ⟨c, rfl⟩
  have h1 := radius_le z c
  have h2 : 0 ≤ radius k z := radius_nonneg z
  nlinarith


/-- The isomorphism `k(z) → k(z')` moves every element by less than `ε` times its norm. -/
theorem norm_adjoinEquivOfTranscendental_sub_le {z z' : L} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (h : ‖z - z'‖ < ε * radius k z) (hz : Transcendental k z) (hz' : Transcendental k z')
    (x : k⟮z⟯) : ‖(adjoinEquivOfTranscendental hz hz' x : L) - x‖ ≤ ε * ‖(x : L)‖ := by
  set u := (RatFunc.algEquivOfTranscendental z hz).symm x with hu
  have hx : x = RatFunc.algEquivOfTranscendental z hz u := by simp [hu]
  have hψ : (adjoinEquivOfTranscendental hz hz' x : L) =
      aeval z' u.num / aeval z' u.denom := by
    rw [adjoinEquivOfTranscendental, AlgEquiv.trans_apply, ← hu,
      RatFunc.algEquivOfTranscendental_apply]
  have hx' : (x : L) = aeval z u.num / aeval z u.denom := by
    rw [hx, RatFunc.algEquivOfTranscendental_apply]
  rcases eq_or_ne u 0 with hu0 | hu0
  · have : x = 0 := by rw [hx, hu0, map_zero]
    simp [this]
  rw [hψ, hx', norm_sub_rev]
  exact (norm_div_sub_div_lt hε (norm_aeval_sub_aeval_lt hε0 hε h (RatFunc.num_ne_zero hu0))
    (norm_aeval_sub_aeval_lt hε0 hε h u.denom_ne_zero)).le

end EpsClose

section EpsCloseExtend

variable {k L : Type*} [NontriviallyNormedField k] [IsAlgClosed k] [NormedField L]
  [IsUltrametricDist L] [NormedAlgebra k L] [CompleteSpace L]

/-- **Temkin, Lemma 6.3.2** (`epsclose`, lines 4003–4016): if `0 < ε < 1` and
`‖z - z'‖ < ε r(z)`, there is a `k`-embedding `φ : \overline{k(z)} → L` with `φ z = z'`,
`‖φ x - x‖ ≤ ε ‖x‖` and `‖φ x‖ = ‖x‖` for all `x`, whose image is `\overline{k(z')}`. -/
theorem exists_algHom_closureAdjoin {z z' : L} {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1)
    (h : ‖z - z'‖ < ε * radius k z) :
    ∃ φ : closureAdjoin k z →ₐ[k] L, φ ⟨z, mem_closureAdjoin_self z⟩ = z' ∧
      (∀ x, ‖φ x - x‖ ≤ ε * ‖(x : L)‖) ∧ (∀ x, ‖φ x‖ = ‖(x : L)‖) ∧
      φ.fieldRange = closureAdjoin k z' := by
  have hr : 0 < radius k z := pos_of_mul_pos_right ((norm_nonneg (z - z')).trans_lt h) hε0.le
  have hz : Transcendental k z := transcendental_of_notMem_range (notMem_range_of_radius_pos hr)
  have hz' : Transcendental k z' :=
    transcendental_of_notMem_range (notMem_range_of_norm_sub_lt hε.le h)
  let ψ : k⟮z⟯ →ₐ[k] L := (k⟮z'⟯.val).comp (adjoinEquivOfTranscendental hz hz').toAlgHom
  have hψ : ∀ x : k⟮z⟯, ‖ψ x - x‖ ≤ ε * ‖(x : L)‖ :=
    norm_adjoinEquivOfTranscendental_sub_le hε0 hε.le h hz hz'
  -- an element moved by at most `ε ‖x‖`, `ε < 1`, keeps its norm
  have hkeep : ∀ {a b : L}, ‖b - a‖ ≤ ε * ‖a‖ → ‖b‖ = ‖a‖ := by
    intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · rw [norm_zero, mul_zero, sub_zero] at hab
      rw [norm_zero]
      exact le_antisymm hab (norm_nonneg _)
    · have : ‖a - b‖ < ‖a‖ := by
        rw [norm_sub_rev]
        exact hab.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr ha) hε)
      exact norm_eq_of_norm_sub_lt this
  have hψn : ∀ x : k⟮z⟯, ‖ψ x‖ = ‖(x : L)‖ := fun x ↦ hkeep (hψ x)
  let i : k⟮z⟯ →ₐ[k] closureAdjoin k z := IntermediateField.inclusion (adjoin_le_closureAdjoin z)
  have hi : Isometry i := AddMonoidHomClass.isometry_of_norm i fun _ ↦ rfl
  have hψi : Isometry ψ := AddMonoidHomClass.isometry_of_norm ψ hψn
  have hdr : DenseRange i := by
    rw [DenseRange, Subtype.dense_iff]
    have himage : ((↑) : closureAdjoin k z → L) '' Set.range i = (k⟮z⟯ : Set L) := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact x.2
      · intro hy
        exact ⟨i ⟨y, hy⟩, ⟨_, rfl⟩, rfl⟩
    exact himage ▸ subset_rfl
  have hue := hi.isUniformInducing
  have huc := hψi.uniformContinuous
  let φr : closureAdjoin k z →+* L :=
    IsDenseInducing.extendRingHom (i := i.toRingHom) (f := ψ.toRingHom) hue hdr huc
  have hφi : ∀ a, φr (i a) = ψ a := fun a ↦
    IsDenseInducing.extend_eq (hue.isDenseInducing hdr) huc.continuous a
  have hφc : Continuous φr := (uniformContinuous_uniformly_extend hue hdr huc).continuous
  let φ : closureAdjoin k z →ₐ[k] L :=
    { φr with
      commutes' := fun c ↦ by
        have : algebraMap k (closureAdjoin k z) c = i (algebraMap k k⟮z⟯ c) := (i.commutes c).symm
        change φr (algebraMap k (closureAdjoin k z) c) = algebraMap k L c
        rw [this, hφi, ψ.commutes] }
  have hφφr : ∀ x, φ x = φr x := fun _ ↦ rfl
  have hest : ∀ x, ‖φ x - x‖ ≤ ε * ‖(x : L)‖ := by
    intro x
    refine hdr.induction_on x ?_ fun a ↦ ?_
    · exact isClosed_le ((hφc.sub continuous_subtype_val).norm)
        (continuous_const.mul continuous_subtype_val.norm)
    · rw [hφφr, hφi]
      exact hψ a
  have hnorm : ∀ x, ‖φ x‖ = ‖(x : L)‖ := fun x ↦ hkeep (hest x)
  have hiso : Isometry φ := AddMonoidHomClass.isometry_of_norm φ hnorm
  have hφz : φ ⟨z, mem_closureAdjoin_self z⟩ = z' := by
    have : (⟨z, mem_closureAdjoin_self z⟩ : closureAdjoin k z) =
        i (IntermediateField.AdjoinSimple.gen k z) := rfl
    rw [this]
    change φr (i _) = z'
    rw [hφi]
    exact adjoinEquivOfTranscendental_gen hz hz'
  refine ⟨φ, hφz, hest, hnorm, ?_⟩
  · apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := hy
      change φ x ∈ closure (k⟮z'⟯ : Set L)
      refine hdr.induction_on x ?_ fun a ↦ ?_
      · exact isClosed_closure.preimage hφc
      · change φr (i a) ∈ _
        rw [hφi]
        exact subset_closure (adjoinEquivOfTranscendental hz hz' a).2
    · refine closureAdjoin_le ?_ ⟨⟨z, mem_closureAdjoin_self z⟩, hφz⟩
      rw [AlgHom.coe_fieldRange]
      exact hiso.isUniformInducing.isComplete_range.isClosed

end EpsCloseExtend

/-! ### Temkin, Lemma 6.3.3 -/

section EqualDegree

variable {k L : Type*} [NontriviallyNormedField k] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra k L]

/-- **Temkin, Lemma 6.3.3** (`fin`, lines 4018–4029), approximation form: let `K, E ⊆ L` be
complete intermediate fields, `0 < ε < 1`, and suppose every `a ∈ K` admits `a' ∈ E` with
`‖a' - a‖ ≤ ε ‖a‖`. If `L/K` is finite, then `L/E` is finite and `[L : E] ≤ [L : K]`. -/
theorem finrank_le_of_forall_exists_norm_sub_le {K E : IntermediateField k L} [CompleteSpace K]
    [CompleteSpace E] [FiniteDimensional K L] {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1)
    (h : ∀ a ∈ K, ∃ a' ∈ E, ‖a' - a‖ ≤ ε * ‖a‖) :
    FiniteDimensional E L ∧ finrank E L ≤ finrank K L := by
  classical
  set ρ := (ε + 1) / 2 with hρ
  have hερ : ε < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := hε0.trans hερ
  obtain ⟨b, hb⟩ := exists_basis_isROrthogonal (K := K) (E := L) hρ1
  set V : Submodule E L := Submodule.span E (Set.range b) with hV
  have hVfin : FiniteDimensional E V := FiniteDimensional.span_of_finite E (Set.finite_range b)
  have hVcl : IsClosed (V : Set L) := V.closed_of_finiteDimensional
  set c := ε / ρ with hc
  have hc0 : 0 < c := div_pos hε0 hρ0
  have hc1 : c < 1 := (div_lt_one hρ0).mpr hερ
  -- approximation of every element by an element of `V`
  have happrox : ∀ x : L, ∃ x' ∈ V, ‖x - x'‖ ≤ c * ‖x‖ := by
    intro x
    set a := b.repr x
    choose a' ha'E ha' using fun i ↦ h (a i : L) (a i).2
    refine ⟨∑ i, (⟨a' i, ha'E i⟩ : E) • b i, Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    have hx : x = ∑ i, a i • b i := (b.sum_repr x).symm
    have hdiff : x - ∑ i, (⟨a' i, ha'E i⟩ : E) • b i = ∑ i, ((a i : L) - a' i) * b i := by
      conv_lhs => rw [hx]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.smul_def, Algebra.smul_def, sub_mul]
      rfl
    rw [hdiff]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ ↦ ?_
    have hbi := hb a i
    rw [← hx] at hbi
    rw [norm_mul, norm_sub_rev]
    calc ‖a' i - a i‖ * ‖b i‖ ≤ ε * ‖(a i : L)‖ * ‖b i‖ :=
          mul_le_mul_of_nonneg_right (ha' i) (norm_nonneg _)
      _ = ε * ‖a i • b i‖ := by rw [norm_smul, mul_assoc]; rfl
      _ = c * (ρ * ‖a i • b i‖) := by rw [hc]; field_simp
      _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_left hbi hc0.le
  -- every element lies in `V`
  have hne : (V : Set L).Nonempty := ⟨0, V.zero_mem⟩
  have hall : ∀ x : L, x ∈ V := by
    intro x
    have hd : Metric.infDist x (V : Set L) ≤ c * Metric.infDist x (V : Set L) := by
      have : Metric.infDist x (V : Set L) / c ≤ Metric.infDist x (V : Set L) := by
        rw [Metric.le_infDist hne]
        intro v hv
        obtain ⟨y', hy'V, hy'⟩ := happrox (x - v)
        have hmem : v + y' ∈ V := V.add_mem hv hy'V
        have := Metric.infDist_le_dist_of_mem (x := x) hmem
        rw [dist_eq_norm, show x - (v + y') = (x - v) - y' by ring] at this
        rw [div_le_iff₀ hc0, dist_eq_norm]
        nlinarith [norm_nonneg (x - v)]
      rwa [div_le_iff₀ hc0, mul_comm] at this
    have h0 : Metric.infDist x (V : Set L) = 0 := by
      have hnn := Metric.infDist_nonneg (x := x) (s := (V : Set L))
      nlinarith
    have hcl := (Metric.mem_closure_iff_infDist_zero hne).mpr h0
    rwa [hVcl.closure_eq] at hcl
  have htop : V = ⊤ := eq_top_iff.mpr fun x _ ↦ hall x
  have hfin : FiniteDimensional E L := by
    have : FiniteDimensional E (⊤ : Submodule E L) := htop ▸ hVfin
    exact Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfin, ?_⟩
  calc finrank E L = finrank E (⊤ : Submodule E L) :=
        (LinearEquiv.finrank_eq Submodule.topEquiv).symm
    _ = finrank E V := by rw [htop]
    _ ≤ Fintype.card (Fin (finrank K L)) := finrank_range_le_card (R := E) b
    _ = finrank K L := Fintype.card_fin _

end EqualDegree

/-! ### Residue fields of approximating subfields -/

section ResidueRange

/-- Two field extensions of `B` with the same image have the same degree. -/
theorem finrank_eq_of_fieldRange_eq {A A' B : Type*} [Field A] [Field A'] [Field B] [Algebra A B]
    [Algebra A' B] (h : (algebraMap A B).fieldRange = (algebraMap A' B).fieldRange) :
    finrank A B = finrank A' B := by
  refine Algebra.finrank_eq_of_equiv_equiv
    (((algebraMap A B).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr h)).trans
      (algebraMap A' B).rangeRestrictFieldEquiv.symm) (RingEquiv.refl B) ?_
  ext a
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.trans_apply, RingEquiv.refl_apply]
  set y := (RingEquiv.subfieldCongr h) ((algebraMap A B).rangeRestrictFieldEquiv a)
  have hy : (y : B) = algebraMap A B a := rfl
  rw [← hy, ← RingHom.rangeRestrictFieldEquiv_apply_symm_apply (algebraMap A' B) y]

/-- Separability transfers between two field extensions of `B` with the same image. -/
theorem isSeparable_of_fieldRange_eq {A A' B : Type*} [Field A] [Field A'] [Field B] [Algebra A B]
    [Algebra A' B] (h : (algebraMap A B).fieldRange = (algebraMap A' B).fieldRange)
    [Algebra.IsSeparable A B] : Algebra.IsSeparable A' B := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (((algebraMap A B).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr h)).trans
      (algebraMap A' B).rangeRestrictFieldEquiv.symm) (RingEquiv.refl B) ?_
  ext a
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.trans_apply, RingEquiv.refl_apply]
  set y := (RingEquiv.subfieldCongr h) ((algebraMap A B).rangeRestrictFieldEquiv a)
  have hy : (y : B) = algebraMap A B a := rfl
  rw [← hy, ← RingHom.rangeRestrictFieldEquiv_apply_symm_apply (algebraMap A' B) y]

variable {k L : Type*} [NormedField k] [NormedField L] [IsUltrametricDist L] [NormedAlgebra k L]

/-- If every `a ∈ K°` is congruent modulo `L°°` to an element of `E`, the image of `K̃` in `L̃` is
contained in that of `Ẽ`. -/
theorem fieldRange_algebraMap_residueField_le {K E : IntermediateField k L}
    (h : ∀ a ∈ K, ‖a‖ ≤ 1 → ∃ a' ∈ E, ‖a' - a‖ < 1) :
    (algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L))).fieldRange ≤
      (algebraMap (ResidueField (unitBall E)) (ResidueField (unitBall L))).fieldRange := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨a, rfl⟩ := residue_surjective w
  obtain ⟨a', ha'E, ha'⟩ := h ((a : K) : L) (a : K).2 (norm_coe_unitBall_le_one a)
  have ha'1 : ‖a'‖ ≤ 1 := by
    have h2 := IsUltrametricDist.norm_add_le_max ((a : K) : L) (a' - ((a : K) : L))
    rw [add_sub_cancel] at h2
    exact h2.trans (max_le (norm_coe_unitBall_le_one a) ha'.le)
  refine ⟨residue (unitBall E) ⟨⟨a', ha'E⟩, mem_unitBall.mpr ha'1⟩, ?_⟩
  rw [algebraMap_residue, algebraMap_residue, residue_eq_residue_iff]
  simpa using ha'

end ResidueRange

/-! ### Unramifiedness is an open condition -/

section OpenCondition

variable {k L : Type*} [NontriviallyNormedField k] [IsAlgClosed k] [NormedField L]
  [IsUltrametricDist L] [NormedAlgebra k L] [CompleteSpace L]

/-- Under the hypotheses of Lemma 6.3.2, `\overline{k(z)}` and `\overline{k(z')}` approximate each
other to within `ε`. -/
theorem approx_closureAdjoin {z z' : L} {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1)
    (h : ‖z - z'‖ < ε * radius k z) :
    (∀ a ∈ closureAdjoin k z, ∃ a' ∈ closureAdjoin k z', ‖a' - a‖ ≤ ε * ‖a‖) ∧
      (∀ a ∈ closureAdjoin k z', ∃ a' ∈ closureAdjoin k z, ‖a' - a‖ ≤ ε * ‖a‖) := by
  obtain ⟨φ, -, hest, hnorm, hrange⟩ := exists_algHom_closureAdjoin hε0 hε h
  constructor
  · intro a ha
    exact ⟨φ ⟨a, ha⟩, hrange ▸ ⟨⟨a, ha⟩, rfl⟩, hest ⟨a, ha⟩⟩
  · intro b hb
    rw [← hrange] at hb
    obtain ⟨a, rfl⟩ := hb
    refine ⟨a, a.2, ?_⟩
    change ‖(a : L) - φ a‖ ≤ ε * ‖φ a‖
    rw [norm_sub_rev, hnorm]
    exact hest a

/-- **Temkin, Lemmas 6.3.2 and 6.3.3**: if `‖z - z'‖ < ε r(z)` with `0 < ε < 1` and `L` is finite
over `\overline{k(z)}`, then `L` is finite over `\overline{k(z')}`, of the same degree. -/
theorem finiteDimensional_closureAdjoin_of_norm_sub_lt {z z' : L} {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε < 1) (h : ‖z - z'‖ < ε * radius k z) [FiniteDimensional (closureAdjoin k z) L] :
    FiniteDimensional (closureAdjoin k z') L ∧
      finrank (closureAdjoin k z') L = finrank (closureAdjoin k z) L := by
  obtain ⟨h1, h2⟩ := approx_closureAdjoin hε0 hε h
  obtain ⟨hfin, hle⟩ := finrank_le_of_forall_exists_norm_sub_le hε0 hε h1
  obtain ⟨-, hle'⟩ := finrank_le_of_forall_exists_norm_sub_le hε0 hε h2
  exact ⟨hfin, le_antisymm hle hle'⟩

/-- **Unramifiedness is an open condition** (Temkin, proof of Theorem 2.1.10(ii),
lines 4146–4151): if `L/\overline{k(z)}` is finite and unramified and `‖z - z'‖ < ε r(z)` with
`0 < ε < 1`, then `L/\overline{k(z')}` is finite and unramified. -/
theorem IsUnramified.of_norm_sub_lt {z z' : L} {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1)
    (h : ‖z - z'‖ < ε * radius k z) (hu : IsUnramified (closureAdjoin k z) L) :
    IsUnramified (closureAdjoin k z') L := by
  have := hu.finiteDimensional
  have hsep := hu.isSeparable
  obtain ⟨hfin, hdeg⟩ := finiteDimensional_closureAdjoin_of_norm_sub_lt hε0 hε h
  obtain ⟨h1, h2⟩ := approx_closureAdjoin hε0 hε h
  have hlt : ∀ {K E : IntermediateField k L},
      (∀ a ∈ K, ∃ a' ∈ E, ‖a' - a‖ ≤ ε * ‖a‖) → ∀ a ∈ K, ‖a‖ ≤ 1 → ∃ a' ∈ E, ‖a' - a‖ < 1 := by
    intro K E hKE a ha ha1
    obtain ⟨a', ha'E, ha'⟩ := hKE a ha
    exact ⟨a', ha'E, ha'.trans_lt ((mul_le_of_le_one_right hε0.le ha1).trans_lt hε)⟩
  have hr := le_antisymm (fieldRange_algebraMap_residueField_le (hlt h1))
    (fieldRange_algebraMap_residueField_le (hlt h2))
  refine ⟨hfin, ?_, isSeparable_of_fieldRange_eq hr⟩
  rw [inertiaDegree_def, ← finrank_eq_of_fieldRange_eq hr, ← inertiaDegree_def, hu.inertiaDegree_eq,
    hdeg]

end OpenCondition

/-! ### Temkin, Corollary 6.3.4 -/

section Exchange

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- **Exchange**: if `x` is transcendental over `k` and algebraic over `k(y)`, then `y` is
algebraic over `k(x)`. -/
theorem isAlgebraic_adjoin_of_isAlgebraic_adjoin {x y : L} (hx : Transcendental k x)
    (hxy : IsAlgebraic (IntermediateField.adjoin k {y}) x) :
    IsAlgebraic (IntermediateField.adjoin k {x}) y := by
  by_contra hy
  have hy' : Transcendental (Algebra.adjoin k (Set.range fun _ : Unit ↦ x)) y := by
    rw [Set.range_const, ← IntermediateField.transcendental_adjoin_iff]
    exact hy
  have hind : AlgebraicIndependent k (fun _ : Unit ↦ x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have h2 := (hind.option_iff_transcendental y).mpr hy'
  let σ : Option Unit → Option Unit := fun o ↦ o.elim (some ()) fun _ ↦ none
  have hσ : Function.Injective σ := by
    intro a b hab
    rcases a with _ | ⟨⟨⟩⟩ <;> rcases b with _ | ⟨⟨⟩⟩ <;> simp_all [σ]
  have h3 : AlgebraicIndependent k (fun o : Option Unit ↦ o.elim x fun _ ↦ y) := by
    have := h2.comp σ hσ
    convert this using 1
    ext o
    rcases o with _ | ⟨⟨⟩⟩ <;> rfl
  have hyind : AlgebraicIndependent k (fun _ : Unit ↦ y) :=
    h3.comp (fun _ ↦ some ()) fun _ _ _ ↦ rfl
  have h4 := (hyind.option_iff_transcendental x).mp h3
  rw [Set.range_const, ← IntermediateField.transcendental_adjoin_iff] at h4
  exact h4 hxy

/-- Finiteness over a smaller subfield implies finiteness over a larger one (the two subfields
may be intermediate fields over different base fields). -/
theorem finiteDimensional_of_forall_mem {F F' : Type*} [Field F] [Field F'] [Algebra F L]
    [Algebra F' L] {A : IntermediateField F L} {B : IntermediateField F' L}
    (h : ∀ x ∈ A, x ∈ B) [FiniteDimensional A L] : FiniteDimensional B L := by
  let f : A →+* B :=
    { toFun := fun a ↦ ⟨a, h a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let : Algebra A B := f.toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Module.Finite.of_restrictScalars_finite A B L

/-- Finiteness over a smaller intermediate field implies finiteness over a larger one. -/
theorem finiteDimensional_of_le {A B : IntermediateField k L} (h : A ≤ B) [FiniteDimensional A L] :
    FiniteDimensional B L :=
  finiteDimensional_of_forall_mem fun _ hx ↦ h hx

end Exchange

section Finite

variable {k L : Type*} [NontriviallyNormedField k] [CompleteSpace k]
  [IsAlgClosed k] [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra k L]

/-- **Temkin, Corollary 6.3.4** (`fincor`, lines 4031–4040): a one-dimensional analytic `k`-field
`L` is finite over `\overline{k(x)}` for every `x ∉ k`. -/
theorem finiteDimensional_closureAdjoin (hL : IsOneDimensional k L) {x : L}
    (hx : x ∉ Set.range (algebraMap k L)) : FiniteDimensional (closureAdjoin k x) L := by
  obtain ⟨y, hy, hfin⟩ := hL
  set K₀ := closureAdjoin k y with hK₀
  set q := ringExpChar L
  have : ExpChar L q := ringExpChar.expChar L
  -- the separable closure `L₁` of `K₀` in `L`, and `x₁ = x ^ q ^ n ∈ L₁`
  set L₁ := separableClosure K₀ L with hL₁
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem L₁ q x
  set x₁ := x ^ q ^ n with hx₁
  have hx₁L₁ : x₁ ∈ L₁ := by
    obtain ⟨w, hw⟩ := hn
    rw [← hw]
    exact w.2
  have hx₁k : x₁ ∉ Set.range (algebraMap k L) := by
    rintro ⟨c, hc⟩
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (expChar_pos L q) n)
    apply hx
    refine ⟨d, ?_⟩
    have : (x - algebraMap k L d) ^ q ^ n = 0 := by
      rw [sub_pow_expChar_pow, ← map_pow, hd, hc, sub_self]
    exact (sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (expChar_pos L q).ne') |>.mp this)).symm
  have hle : closureAdjoin k x₁ ≤ closureAdjoin k x :=
    closureAdjoin_le_closureAdjoin (adjoin_le_closureAdjoin x
      (pow_mem (IntermediateField.mem_adjoin_simple_self k x) _))
  suffices hsuff : FiniteDimensional (closureAdjoin k x₁) L from finiteDimensional_of_le hle
  -- Krasner density: `L₁ = K₀(α)` with `α` integral over `k(y)`
  let : Algebra (IntermediateField.adjoin k {y}) K₀ :=
    (IntermediateField.inclusion (adjoin_le_closureAdjoin y)).toAlgebra
  have hdense : DenseRange (algebraMap (IntermediateField.adjoin k {y}) K₀) := by
    rw [DenseRange, Subtype.dense_iff]
    have himage : ((↑) : K₀ → L) '' Set.range (algebraMap (IntermediateField.adjoin k {y}) K₀) =
        (IntermediateField.adjoin k {y} : Set L) := by
      ext w
      constructor
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        exact v.2
      · intro hw
        exact ⟨_, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
    exact himage ▸ subset_rfl
  obtain ⟨α, g, hgm, -, hmin, hαtop⟩ := exists_adjoin_eq_top_of_denseRange hdense L₁
  have hαint : IsIntegral (IntermediateField.adjoin k {y}) (α : L) := by
    have h0 : aeval α (minpoly K₀ α) = 0 := minpoly.aeval _ _
    rw [hmin] at h0
    have h1 : aeval (α : L) (g.map (algebraMap (IntermediateField.adjoin k {y}) K₀)) = 0 := by
      have := congrArg (algebraMap L₁ L) h0
      rwa [map_zero, ← aeval_algebraMap_apply] at this
    rw [aeval_def, eval₂_map] at h1
    exact ⟨g, hgm, h1⟩
  -- `l = k(y)(α)` is dense in `L₁`
  set l := IntermediateField.adjoin (IntermediateField.adjoin k {y}) {(α : L)} with hl
  have hlalg : ∀ w ∈ l, IsAlgebraic (IntermediateField.adjoin k {y}) w := by
    intro w hw
    have : FiniteDimensional (IntermediateField.adjoin k {y}) l :=
      IntermediateField.adjoin.finiteDimensional hαint
    have := Algebra.IsAlgebraic.isAlgebraic (R := IntermediateField.adjoin k {y})
      (⟨w, hw⟩ : l)
    exact this.algHom (l.val)
  have hL₁cl : (L₁ : Set L) ⊆ closure (l : Set L) := by
    set C : IntermediateField K₀ L := Subfield.toIntermediateField
      (l.toSubfield.topologicalClosure) fun c ↦ by
        change (c : L) ∈ closure (l : Set L)
        have hc : (c : L) ∈ closure (IntermediateField.adjoin k {y} : Set L) := c.2
        refine closure_mono ?_ hc
        intro w hw
        exact IntermediateField.algebraMap_mem l ⟨w, hw⟩
    have hαC : (α : L) ∈ C := subset_closure (IntermediateField.mem_adjoin_simple_self _ _)
    have hL₁C : L₁ ≤ C := by
      have : IntermediateField.adjoin K₀ {(α : L)} ≤ C :=
        IntermediateField.adjoin_simple_le_iff.mpr hαC
      have heq : IntermediateField.adjoin K₀ {(α : L)} = L₁ := by
        have := IntermediateField.adjoin_map K₀ {α} L₁.val
        rw [Set.image_singleton, hαtop, ← AlgHom.fieldRange_eq_map,
          IntermediateField.fieldRange_val] at this
        exact this.symm
      rwa [heq] at this
    exact hL₁C
  -- choose `x' ∈ l` close to `x₁`
  have hr : 0 < radius k x₁ := by
    by_contra hr0
    have h0 : radius k x₁ = 0 := le_antisymm (not_lt.mp hr0) (radius_nonneg x₁)
    have hcl : IsClosed (Set.range (algebraMap k L)) :=
      (algebraMap_isometry k L).isUniformInducing.isComplete_range.isClosed
    apply hx₁k
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨a, ha⟩ := exists_norm_sub_lt_of_radius_lt (k := k) (z := x₁) (t := ε) (by rwa [h0])
    exact ⟨algebraMap k L a, ⟨a, rfl⟩, by rwa [dist_eq_norm]⟩
  obtain ⟨x', hx'l, hx'⟩ := Metric.mem_closure_iff.mp (hL₁cl hx₁L₁) (1 / 2 * radius k x₁)
    (by positivity)
  rw [dist_eq_norm] at hx'
  have hx'k : x' ∉ Set.range (algebraMap k L) := notMem_range_of_norm_sub_lt (by norm_num) hx'
  -- `y` is algebraic over `k(x')`, hence integral over `K' = \overline{k(x')}`
  set K' := closureAdjoin k x' with hK'
  have hyalg : IsAlgebraic (IntermediateField.adjoin k {x'}) y :=
    isAlgebraic_adjoin_of_isAlgebraic_adjoin (transcendental_of_notMem_range hx'k)
      (hlalg x' hx'l)
  let : Algebra (IntermediateField.adjoin k {x'}) K' :=
    (IntermediateField.inclusion (adjoin_le_closureAdjoin x')).toAlgebra
  have : IsScalarTower (IntermediateField.adjoin k {x'}) K' L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hyint : IsIntegral K' y :=
    (hyalg.extendScalars (algebraMap (IntermediateField.adjoin k {x'}) K').injective).isIntegral
  -- `L` is finite over `K'(y) ⊇ K₀`, hence over `K'`
  set M := IntermediateField.adjoin K' {y} with hM
  have hMfin : FiniteDimensional K' M := IntermediateField.adjoin.finiteDimensional hyint
  have hMcl : IsClosed (M : Set L) := isClosed_adjoin_simple hyint
  have hMcl' : IsClosed ((M.restrictScalars k : IntermediateField k L) : Set L) := by
    rw [IntermediateField.coe_restrictScalars]
    exact hMcl
  have hyM : y ∈ M.restrictScalars k := by
    rw [IntermediateField.mem_restrictScalars]
    exact IntermediateField.mem_adjoin_simple_self _ _
  have hK₀M : K₀ ≤ M.restrictScalars k := closureAdjoin_le hMcl' hyM
  have : FiniteDimensional M L :=
    finiteDimensional_of_forall_mem (A := K₀) fun a ha ↦ by
      have := hK₀M ha
      rwa [IntermediateField.mem_restrictScalars] at this
  have : FiniteDimensional K' L := Module.Finite.trans M L
  -- compare `K'` with `\overline{k(x₁)}` (Lemmas 6.3.2, 6.3.3)
  obtain ⟨-, h2⟩ := approx_closureAdjoin (k := k) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hx'
  exact (finrank_le_of_forall_exists_norm_sub_le (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) h2).1

end Finite

end DeJongAlterations.StableModification.Valuation.Analytic
