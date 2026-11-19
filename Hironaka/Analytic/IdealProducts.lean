import Hironaka.Analytic.IdealPresentation

set_option autoImplicit false

/-!
# The weight of a product of ideals

Source: Copy-4, `sec:qpsh` and `lem:ideal-comparison`
(`transcendental-nakamaye-copy4-20260911`).

`lem:ideal-comparison` reads an inclusion of ideals
`𝔅 · 𝔅̄_m^p ⊆ 𝓘(Mu) ⊆ 𝔅̄_M` as an inequality between the divisors that
principalize them.  Half of that translation is the monotonicity proved in
`Pending/IdealWeightComparison`; the other half is the identity

  `ψ_{𝔞𝔟} = ψ_𝔞 + ψ_𝔟 + O(1)`,

which lets the weight of a product be split.  This module proves it, in the same
`HasAnalyticSingularitiesOfType` language, with one constant on a compact
manifold.

The mechanism is `mulFamily`: the `N·P` pairwise products of two generating
families.  Its squared norm is exactly the product of the two squared norms, so
its weight is exactly the sum of the two weights — no error term at all at the
level of *families*.  All of the `O(1)` comes from comparing the chosen
generators of `𝔞𝔟` with those products, which is `DominatedAt` in both
directions.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealWeightProducts

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison

/-! ### The family of pairwise products -/

section Family

variable {X : Type*} {N P : ℕ}

/-- The `N·P` pairwise products of two finite families, indexed through
`finProdFinEquiv`. -/
def mulFamily (g : Fin N → X → ℂ) (h : Fin P → X → ℂ) : Fin (N * P) → X → ℂ :=
  fun k y => g (finProdFinEquiv.symm k).1 y * h (finProdFinEquiv.symm k).2 y

theorem mulFamily_apply (g : Fin N → X → ℂ) (h : Fin P → X → ℂ)
    (i : Fin N) (j : Fin P) (y : X) :
    mulFamily g h (finProdFinEquiv (i, j)) y = g i y * h j y := by
  simp [mulFamily]

/-- The squared norm of the product family is the product of the squared
norms. -/
theorem generatorNormSq_mulFamily (g : Fin N → X → ℂ) (h : Fin P → X → ℂ) (y : X) :
    generatorNormSq (mulFamily g h) y = generatorNormSq g y * generatorNormSq h y := by
  have hre : ∑ k, ‖mulFamily g h k y‖ ^ 2
      = ∑ q : Fin N × Fin P, ‖g q.1 y‖ ^ 2 * ‖h q.2 y‖ ^ 2 := by
    refine (Fintype.sum_equiv finProdFinEquiv
      (fun q : Fin N × Fin P => ‖g q.1 y‖ ^ 2 * ‖h q.2 y‖ ^ 2)
      (fun k => ‖mulFamily g h k y‖ ^ 2) ?_).symm
    intro q
    rw [mulFamily_apply, norm_mul, mul_pow]
  calc generatorNormSq (mulFamily g h) y = ∑ k, ‖mulFamily g h k y‖ ^ 2 := rfl
    _ = ∑ q : Fin N × Fin P, ‖g q.1 y‖ ^ 2 * ‖h q.2 y‖ ^ 2 := hre
    _ = ∑ i, ∑ j, ‖g i y‖ ^ 2 * ‖h j y‖ ^ 2 := Fintype.sum_prod_type _
    _ = generatorNormSq g y * generatorNormSq h y := by
      rw [generatorNormSq, generatorNormSq, Finset.sum_mul_sum]

/-- **The weight of the product family is the sum of the weights**, exactly — the
logarithm turns the previous identity into an addition, and the convention
`log 0 = ⊥` makes it correct at common zeros too. -/
theorem generatorLog_mulFamily (g : Fin N → X → ℂ) (h : Fin P → X → ℂ) (y : X) :
    generatorLog (mulFamily g h) y = generatorLog g y + generatorLog h y := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  have h1 : (∑ k, ‖mulFamily g h k y‖ ^ 2)
      = (∑ i, ‖g i y‖ ^ 2) * ∑ j, ‖h j y‖ ^ 2 := by
    simpa only [generatorNormSq] using generatorNormSq_mulFamily g h y
  rw [h1, ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ENNReal.log_mul_add]

end Family

/-! ### The weight of a product ideal -/

section Ideal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Unfolding the product ideal. -/
theorem mem_mul_iff {𝔞 𝔟 : GermIdeal n M} {x : M} {v : M → ℂ} :
    (𝔞.mul 𝔟).mem x v ↔
      IsInSpanAt (n := n) (fun s => ∃ a b, 𝔞.mem x a ∧ 𝔟.mem x b ∧ s = a * b) x v :=
  Iff.rfl

/-- A product of dominated germs is dominated by the product family. -/
theorem dominatedAt_mul {N P : ℕ} {g : Fin N → M → ℂ} {h : Fin P → M → ℂ} {x : M}
    {a b : M → ℂ} (ha : DominatedAt g x a) (hb : DominatedAt h x b) :
    DominatedAt (mulFamily g h) x (a * b) := by
  obtain ⟨B, hB, hBy⟩ := ha
  obtain ⟨B', hB', hB'y⟩ := hb
  refine ⟨B * B', mul_pos hB hB', ?_⟩
  filter_upwards [hBy, hB'y] with y hy hy'
  have hg0 : (0 : ℝ) ≤ B * generatorNormSq g y :=
    mul_nonneg hB.le (generatorNormSq_nonneg g y)
  rw [generatorNormSq_mulFamily]
  calc ‖(a * b) y‖ ^ 2 = ‖a y‖ ^ 2 * ‖b y‖ ^ 2 := by
        simp only [Pi.mul_apply, norm_mul, mul_pow]
    _ ≤ (B * generatorNormSq g y) * (B' * generatorNormSq h y) :=
        mul_le_mul hy hy' (sq_nonneg _) hg0
    _ = B * B' * (generatorNormSq g y * generatorNormSq h y) := by ring

/-- **`ψ_{𝔞𝔟} = ψ_𝔞 + ψ_𝔟 + O(1)`**, at a point (Copy-4, `sec:qpsh`).  Both
directions are genuine: one says every generator of `𝔞𝔟` is a holomorphic
combination of pairwise products, the other that every pairwise product is a
section of `𝔞𝔟`. -/
theorem sameSingularityTypeAt_mul {φ φ' φ'' : M → EReal} {c : ℚ}
    {𝔞 𝔟 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hφ'' : HasAnalyticSingularitiesOfType (n := n) φ'' c (𝔞.mul 𝔟))
    (x : M) : SameSingularityTypeAt φ'' (fun y => φ y + φ' y) x := by
  obtain ⟨hc, hcoh, hpres⟩ := hφ
  obtain ⟨-, hcoh', hpres'⟩ := hφ'
  obtain ⟨-, -, hpres''⟩ := hφ''
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres x
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff, R', C₀', hR'b, hφ'eq⟩ := hpres' x
  obtain ⟨U'', hU'', hxU'', Q, k, hkdiff, hkiff, R'', C₀'', hR''b, hφ''eq⟩ := hpres'' x
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- every generator of `𝔞𝔟` is a holomorphic combination of pairwise products
  have hdom1 : ∀ l, DominatedAt (mulFamily g h) x (k l) := by
    intro l
    obtain ⟨-, K, s, α, hs, hα, hsum⟩ :=
      mem_mul_iff.mp (mem_of_isPresentation hU'' hxU'' hkdiff hkiff l)
    refine DominatedAt.sum (fun t => (hα t).continuousAt) (fun t => ?_) hsum
    obtain ⟨a, b, hamem, hbmem, hst⟩ := hs t
    rw [hst]
    exact dominatedAt_mul (dominatedAt_of_isInSpanAt ((hgiff x hxU a).mp hamem))
      (dominatedAt_of_isInSpanAt ((hhiff x hxU' b).mp hbmem))
  -- conversely each pairwise product is a section of `𝔞𝔟`
  have hdom2' : ∀ (i : Fin N) (j : Fin P),
      DominatedAt k x (fun y => g i y * h j y) := by
    intro i j
    have hga : 𝔞.mem x (g i) := mem_of_isPresentation hU hxU hgdiff hgiff i
    have hhb : 𝔟.mem x (h j) := mem_of_isPresentation hU' hxU' hhdiff hhiff j
    have hgh : HolomorphicAt n (fun y => g i y * h j y) x :=
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hga).mul
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh' hhb)
    exact dominatedAt_of_isInSpanAt ((hkiff x hxU'' _).mp
      (mem_mul_iff.mpr (isInSpanAt_of_eq_mul ⟨g i, h j, hga, hhb, rfl⟩ hgh
        (holomorphicAt_const 1) (Filter.Eventually.of_forall fun _ => (one_mul _).symm))))
  have hdom2 : ∀ t, DominatedAt k x (mulFamily g h t) := fun t =>
    hdom2' (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  have hlog1 : MoreSingularAt (generatorLog k) (generatorLog (mulFamily g h)) x :=
    moreSingularAt_generatorLog_of_forall_dominatedAt hdom1
  have hlog2 : MoreSingularAt (generatorLog (mulFamily g h)) (generatorLog k) x :=
    moreSingularAt_generatorLog_of_forall_dominatedAt hdom2
  -- the sum is presented by the product family, with the summed remainder
  have hsum : ∀ᶠ y in 𝓝 x, φ y + φ' y
      = ((c : ℝ) : EReal) * generatorLog (mulFamily g h) y
        + ((R y + R' y : ℝ) : EReal) := by
    filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU'] with y hy hy'
    rw [hφeq y hy, hφ'eq y hy', generatorLog_mulFamily,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le)
        (EReal.coe_ne_top _), EReal.coe_add]
    exact add_add_add_comm _ _ _ _
  have hRsum : ∀ᶠ y in 𝓝 x, R y + R' y ≤ C₀ + C₀' := by
    filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU'] with y hy hy'
    have h1 := (abs_le.mp (hRb y hy)).2
    have h2 := (abs_le.mp (hR'b y hy')).2
    linarith
  have hRsum' : ∀ᶠ y in 𝓝 x, -(C₀ + C₀') ≤ R y + R' y := by
    filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU'] with y hy hy'
    have h1 := (abs_le.mp (hRb y hy)).1
    have h2 := (abs_le.mp (hR'b y hy')).1
    linarith
  have h''eq : ∀ᶠ y in 𝓝 x, φ'' y
      = ((c : ℝ) : EReal) * generatorLog k y + (R'' y : EReal) :=
    Filter.eventually_of_mem (hU''.mem_nhds hxU'') fun y hy => hφ''eq y hy
  have h''le : ∀ᶠ y in 𝓝 x, R'' y ≤ C₀'' :=
    Filter.eventually_of_mem (hU''.mem_nhds hxU'') fun y hy => (abs_le.mp (hR''b y hy)).2
  have h''ge : ∀ᶠ y in 𝓝 x, -C₀'' ≤ R'' y :=
    Filter.eventually_of_mem (hU''.mem_nhds hxU'') fun y hy => (abs_le.mp (hR''b y hy)).1
  exact ⟨moreSingularAt_of_moreSingularAt_generatorLog hcR h''eq hsum h''le hRsum' hlog1,
    moreSingularAt_of_moreSingularAt_generatorLog hcR hsum h''eq hRsum h''ge hlog2⟩

/-- **`ψ_{𝔞𝔟} = ψ_𝔞 + ψ_𝔟 + O(1)` on a compact manifold**, with one constant.
This is the step by which `lem:ideal-comparison` turns the inclusion
`𝔅 𝔅̄_m^p ⊆ 𝔅̄_M` into the divisor inequality `G_B + p G_m ≥ G_M`. -/
theorem sameSingularityTypeOn_univ_mul [CompactSpace M] {φ φ' φ'' : M → EReal}
    {c : ℚ} {𝔞 𝔟 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hφ'' : HasAnalyticSingularitiesOfType (n := n) φ'' c (𝔞.mul 𝔟)) :
    SameSingularityTypeOn φ'' (fun y => φ y + φ' y) univ :=
  ⟨moreSingularOn_univ_of_forall_moreSingularAt
      fun x => (sameSingularityTypeAt_mul hφ hφ' hφ'' x).1,
   moreSingularOn_univ_of_forall_moreSingularAt
      fun x => (sameSingularityTypeAt_mul hφ hφ' hφ'' x).2⟩

end Ideal

end

end Hironaka.IdealWeightProducts
