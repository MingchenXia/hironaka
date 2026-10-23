/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Henselian

/-!
# Hensel's lemma and the spectral norm for complete non-archimedean fields

Temkin, *Stable modification of relative curves*, §2.1 (`semi-stable.tex`, lines 1895–1896):
"Any analytic field is henselian in the sense that its ring of integers is henselian". This file
proves it for every complete non-archimedean normed field `K`, with the root bound of Hensel's
lemma, and records the consequences of the uniqueness of the spectral norm for algebraic extensions
of a complete nontrivially normed field: automorphisms are isometries and the unit ball of an
algebraic extension is the integral closure of the unit ball.

## Main results

* `mem_span_singleton_pow_iff`: for `0 ≠ b ∈ K°`, the ideal `(b)ⁿ` is the closed ball of radius
  `‖b‖ⁿ` in `K°`.
* `isAdicComplete_span_singleton`: if `K` is complete and `0 < ‖b‖ < 1`, then `K°` is `(b)`-adically
  complete.
* `exists_isRoot_norm_sub_le` (**Hensel's lemma**): if `F ∈ K°[X]` is monic, `‖F(a)‖ < 1` and
  `F'(a)` is a unit, then `F` has a root `x ∈ K°` with `‖x - a‖ ≤ ‖F(a)‖`.
* `henselianLocalRing_unitBall`: `K°` is a henselian local ring.
* `norm_le_one_of_isIntegral`: elements integral over `K°` have norm at most one, in every
  non-archimedean normed `K`-algebra.
* `isIntegral_unitBall_iff_norm_le_one`: for an algebraic normed extension `L` of a complete
  nontrivially normed `K`, `x ∈ L` is integral over `K°` iff `‖x‖ ≤ 1`; so `L°` is the integral
  closure of `K°` in `L` (`mem_integralClosure_iff_mem_unitBall`).
* `norm_algEquiv_apply`: `K`-automorphisms of such an `L` are isometries.

The Hensel part adapts EnvelopeProperty, `Algebra/NormValuationPrincipalAdic.lean` and
`Algebra/NormValuationHenselian.lean`.
-/

noncomputable section

open IsLocalRing Polynomial
open scoped NNReal

namespace DeJongAlterations.StableModification.Valuation.Analytic

section Hensel

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- For `0 ≠ b ∈ K°`, the ideal `(b)ⁿ` of `K°` is the closed ball of radius `‖b‖ⁿ`. -/
theorem mem_span_singleton_pow_iff {b : unitBall K} (hb : b ≠ 0) (n : ℕ) (a : unitBall K) :
    a ∈ Ideal.span {b} ^ n ↔ ‖(a : K)‖ ≤ ‖(b : K)‖ ^ n := by
  have hbK : (b : K) ≠ 0 := fun h ↦ hb (Subtype.ext h)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    change ‖(c : K) * (b : K) ^ n‖ ≤ ‖(b : K)‖ ^ n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (norm_coe_unitBall_le_one c)
  · intro ha
    have hpos : 0 < ‖(b : K)‖ ^ n := pow_pos (norm_pos_iff.mpr hbK) _
    refine ⟨⟨(a : K) / (b : K) ^ n, mem_unitBall.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, norm_pow]
      exact (div_le_one hpos).mpr ha
    · change (a : K) / (b : K) ^ n * (b : K) ^ n = a
      exact div_mul_cancel₀ _ (pow_ne_zero _ hbK)

/-- The unit ball is closed. -/
theorem isClosed_unitBall : IsClosed (unitBall K : Set K) := by
  have : (unitBall K : Set K) = {x | ‖x‖ ≤ 1} := by ext x; exact mem_unitBall
  rw [this]
  exact isClosed_le continuous_norm continuous_const

instance completeSpace_unitBall [CompleteSpace K] : CompleteSpace (unitBall K) :=
  isClosed_unitBall.completeSpace_coe

/-- For `0 < ‖b‖ < 1`, the metric topology of `K°` is the `(b)`-adic topology. -/
theorem isAdic_span_singleton {b : unitBall K} (hb : b ≠ 0) (hsmall : ‖(b : K)‖ < 1) :
    IsAdic (Ideal.span {b}) := by
  have hbK : (b : K) ≠ 0 := fun h ↦ hb (Subtype.ext h)
  have hn : 0 < ‖(b : K)‖ := norm_pos_iff.mpr hbK
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [Metric.isOpen_iff]
    intro a ha
    refine ⟨‖(b : K)‖ ^ n, pow_pos hn _, fun c hc ↦ ?_⟩
    rw [SetLike.mem_coe, mem_span_singleton_pow_iff hb] at ha ⊢
    rw [Metric.mem_ball, dist_eq_norm] at hc
    change ‖(c : K) - (a : K)‖ < ‖(b : K)‖ ^ n at hc
    calc ‖(c : K)‖ = ‖((c : K) - (a : K)) + (a : K)‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(c : K) - (a : K)‖ ‖(a : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖(b : K)‖ ^ n := max_le hc.le ha
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hnε⟩ := exists_pow_lt_of_lt_one hε hsmall
    refine ⟨n, fun a ha ↦ hball ?_⟩
    rw [SetLike.mem_coe, mem_span_singleton_pow_iff hb] at ha
    rw [Metric.mem_ball, dist_zero_right]
    exact ha.trans_lt hnε

/-- If `K` is complete and `0 < ‖b‖ < 1`, then `K°` is `(b)`-adically complete. -/
theorem isAdicComplete_span_singleton [CompleteSpace K] {b : unitBall K} (hb : b ≠ 0)
    (hsmall : ‖(b : K)‖ < 1) : IsAdicComplete (Ideal.span {b}) (unitBall K) :=
  (isAdic_span_singleton hb hsmall).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

/-- **Hensel's lemma** with the root bound. Let `K` be a complete non-archimedean normed field and
`F ∈ K°[X]` monic. If `‖F(a)‖ < 1` and `F'(a)` is a unit of `K°`, then `F` has a root `x ∈ K°` with
`‖x - a‖ ≤ ‖F(a)‖`. -/
theorem exists_isRoot_norm_sub_le [CompleteSpace K] (F : (unitBall K)[X]) (hF : F.Monic)
    (a : unitBall K) (hsmall : ‖((F.eval a : unitBall K) : K)‖ < 1)
    (hderiv : IsUnit (F.derivative.eval a)) :
    ∃ x : unitBall K, F.IsRoot x ∧ ‖((x - a : unitBall K) : K)‖ ≤ ‖((F.eval a : unitBall K) : K)‖ := by
  by_cases hz : F.eval a = 0
  · refine ⟨a, hz, ?_⟩
    rw [sub_self]
    simp
  set b := F.eval a with hb_def
  have : IsAdicComplete (Ideal.span {b}) (unitBall K) := isAdicComplete_span_singleton hz hsmall
  have hb : F.eval a ∈ Ideal.span {b} := Ideal.mem_span_singleton_self b
  have hd : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) (F.derivative.eval a)) := hderiv.map _
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian F hF a hb hd
  refine ⟨x, hx, ?_⟩
  have := (mem_span_singleton_pow_iff hz 1 (x - a)).mp (by simpa only [pow_one] using hxa)
  simpa only [pow_one] using this

/-- The unit ball of a complete non-archimedean normed field is a henselian local ring
(Temkin, l. 1895–1896). -/
instance henselianLocalRing_unitBall [CompleteSpace K] : HenselianLocalRing (unitBall K) where
  is_henselian F hF a hsmall hderiv := by
    have hs : ‖((F.eval a : unitBall K) : K)‖ < 1 := mem_maximalIdeal_unitBall_iff.mp hsmall
    obtain ⟨x, hx, hxa⟩ := exists_isRoot_norm_sub_le F hF a hs hderiv
    exact ⟨x, hx, mem_maximalIdeal_unitBall_iff.mpr (hxa.trans_lt hs)⟩

/-- A simple root of the reduction of a monic polynomial over `K°` lifts to a root in `K°`. -/
theorem exists_isRoot_residue_eq [CompleteSpace K] (F : (unitBall K)[X]) (hF : F.Monic)
    (β : ResidueField (unitBall K)) (hβ : aeval β F = 0) (hβ' : aeval β F.derivative ≠ 0) :
    ∃ x : unitBall K, F.IsRoot x ∧ residue (unitBall K) x = β := by
  have h := ((HenselianLocalRing.TFAE (unitBall K)).out 0 1).mp
    (inferInstance : HenselianLocalRing (unitBall K))
  exact h F hF β hβ hβ'

end Hensel

/-! ### Integrality and the spectral norm -/

section Integral

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

/-- In a non-archimedean normed algebra, an element integral over the unit ball of the base has
norm at most one. -/
theorem norm_le_one_of_isIntegral {x : L} (hx : IsIntegral (unitBall K) x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hpm, hp⟩ := hx
  by_contra hlt
  rw [not_le] at hlt
  have hx0 : (0 : ℝ) < ‖x‖ := one_pos.trans hlt
  set n := p.natDegree
  have hn : 0 < n := by
    by_contra h0
    rw [not_lt, Nat.le_zero] at h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hpm h0, eval₂_one] at hp
    exact one_ne_zero hp
  -- `x ^ n = - ∑_{i < n} p_i x ^ i`
  have hsum : x ^ n = -∑ i ∈ Finset.range n, algebraMap (unitBall K) L (p.coeff i) * x ^ i := by
    have := hp
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at this
    exact eq_neg_of_add_eq_zero_right this
  have hle : ‖x ^ n‖ ≤ ‖x‖ ^ (n - 1) := by
    rw [hsum, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hc : ‖algebraMap (unitBall K) L (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply (unitBall K) K L, norm_algebraMap', ]
      exact norm_coe_unitBall_le_one _
    calc ‖algebraMap (unitBall K) L (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ‖x‖ ^ i := one_mul _
      _ ≤ ‖x‖ ^ (n - 1) := pow_le_pow_right₀ hlt.le (by omega)
  rw [norm_pow] at hle
  have : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
  exact absurd hle (not_le.mpr this)

end Integral

section Spectral

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

/-- `K`-automorphisms of an algebraic normed extension of a complete field are isometries
(uniqueness of the spectral norm). -/
theorem norm_algEquiv_apply (σ : L ≃ₐ[K] L) (x : L) : ‖σ x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K,
    spectralNorm_eq_of_equiv σ x]

/-- Two embeddings into an algebraic normed extension of a complete field induce the same norm. -/
theorem norm_algHom_apply {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (σ : L →ₐ[K] M) (x : L) : ‖σ x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K, spectralNorm,
    spectralNorm, minpoly.algHom_eq σ σ.injective]

variable [IsUltrametricDist L]

/-- In an algebraic normed extension `L` of a complete nontrivially normed field `K`, an element is
integral over `K°` iff its norm is at most one. -/
theorem isIntegral_unitBall_iff_norm_le_one {x : L} :
    IsIntegral (unitBall K) x ↔ ‖x‖ ≤ 1 := by
  refine ⟨norm_le_one_of_isIntegral, fun hx ↦ ?_⟩
  have halg : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hmon := minpoly.monic halg
  rw [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm, spectralValue_le_one_iff hmon] at hx
  -- the minimal polynomial has coefficients in `K°`, so it lifts to a monic polynomial over `K°`
  have hlifts : minpoly K x ∈ Polynomial.lifts (algebraMap (unitBall K) K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n ↦ ⟨⟨_, mem_unitBall.mpr (hx n)⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmon
  refine ⟨q, hqm, ?_⟩
  rw [← aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]

/-- The unit ball of an algebraic normed extension of a complete nontrivially normed field is the
integral closure of the unit ball of the base. -/
theorem mem_integralClosure_iff_mem_unitBall {x : L} :
    x ∈ integralClosure (unitBall K) L ↔ x ∈ unitBall L := by
  rw [mem_integralClosure_iff, isIntegral_unitBall_iff_norm_le_one, mem_unitBall]

end Spectral

end DeJongAlterations.StableModification.Valuation.Analytic
