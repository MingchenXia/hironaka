import Hironaka.Blowup.ExceptionalMetricProof
import Hironaka.Analytic.BlanchardWeight
import Hironaka.Analytic.MeteredDivisorWeightBounds
import Hironaka.Analytic.GlobalAnalyticSingularities

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Every effective divisor on a compact complex manifold carries a smooth metric

Source: Copy-4, `prop:principalization` Step 4, `eq:def-DLY`
(`transcendental-nakamaye-copy4-20260911`).

`lem:relative-principalization` produces the divisors `H^fix_m`, `P^mov`, `P^F` and
`G̃_M` as honest divisors — in Lean, `Hironaka.HolomorphicIdealSheaves.EffectiveDivisor`,
i.e. an invertible ideal sheaf `𝒪(-D)` and nothing else.  `eq:def-DLY` forms the
rational combination `D = (1/M) G̃_M + ((C-1)/M) P^mov + (C/M) P^F + τ E_rel`
*with its metric*, and every later step (`ψ_D`, `Θ_D`, `[D] ≥ 0`) reads that metric.
The `MeteredDivisorScaling`/`MeteredDivisorOperations` calculus therefore has no
subject until each `EffectiveDivisor` is upgraded to a
`MeteredEffectiveQDivisor`; only `E_rel` arrives metered, from
`lem:exceptional-metric`.

This module supplies the missing upgrade, which is the classical statement that
`𝒪(D)` admits a smooth Hermitian metric.  The construction is the standard one:
cover `M` by open sets `S_j` carrying a local generator `g_j` of `𝒪(-D)`, take a
chart-smooth partition of unity `χ_a` subordinate to the cover, and set

  `U = ∑_a χ_a |g_{idx a}|²`,   `ψ_D = log U`.

Near a point `x` the sum factors as `U = |g_{j₀}|² · ∑_a χ_a |u_a|²` with
`u_a = g_{idx a}/g_{j₀}` a nonvanishing holomorphic unit, because two local
generators of one invertible ideal differ by a unit (`exists_unit_of_generators`,
the only non-formal ingredient here: the two mutual divisibility relations give
`u v g = g`, and `g` vanishes identically on no nonempty open set, so `u v = 1`
on a whole neighbourhood, not merely off the zero set).  That is exactly a
`FactorizedWeightForm.WeightFactorization`, so
`ExceptionalMetricProof.ofWeightFactorization` turns it into a metered divisor
whose curvature is the glued `ddᶜ log U`.

Contents:

* `exists_unit_of_generators` — two local generators of an invertible ideal
  differ by a nonvanishing holomorphic factor on a neighbourhood;
* `IsDivisorMetric D E` — `ψ_E = log |g|² + (smooth)` for a local generator `g`
  of `𝒪(-D)`;
* `exists_divisorMetric` — every effective divisor on a compact complex manifold
  admits such an `E`, with `E.support = D.support`;
* `hasAnalyticSingularitiesOfType_of_isDivisorMetric` — `ψ_D` has analytic
  singularities of type `(1, 𝒪(-D))`, i.e. the `sec:qpsh` identity
  `ψ_𝔞 = ψ_D + O(1)` for `𝔞 = 𝒪(-D)`.  This is the direction converse to
  `Hironaka.MeteredDivisorGlobalIdeal.exists_hasAnalyticSingularitiesOfType`, and
  together they identify the two encodings.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DivisorMetric

open Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities
  Hironaka.NumericalRestrictedVolumeScaffold
  ChartPartition FactorizedWeightForm ExceptionalMetricProof

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Two local generators of an invertible ideal differ by a unit.**
If `g₁` generates `𝔟` on the open set `U₁` and vanishes identically on no
nonempty open subset of `U₁`, and `g₂` generates `𝔟` on `U₂`, then on a
neighbourhood `V` of any common point there is a nonvanishing holomorphic `u`
with `g₂ = u · g₁`. -/
theorem exists_unit_of_generators {𝔟 : GermIdeal n M} {g₁ g₂ : M → ℂ} {U₁ U₂ : Set M}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hg₁d : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g₁ U₁)
    (hg₂d : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g₂ U₂)
    (hg₁nz : ∀ W : Set M, IsOpen W → W ⊆ U₁ → W.Nonempty → ∃ y ∈ W, g₁ y ≠ 0)
    (hgen₁ : ∀ y ∈ U₁, ∀ f, 𝔟.mem y f ↔ IsInSpanAt (n := n) (· = g₁) y f)
    (hgen₂ : ∀ y ∈ U₂, ∀ f, 𝔟.mem y f ↔ IsInSpanAt (n := n) (· = g₂) y f)
    {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    ∃ (V : Set M) (u : M → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ U₁ ∩ U₂ ∧
      (∀ y ∈ V, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u y) ∧
      (∀ y ∈ V, u y ≠ 0) ∧ ∀ y ∈ V, g₂ y = u y * g₁ y := by
  classical
  have hhol₁ : HolomorphicAt n g₁ x := by
    filter_upwards [hU₁.mem_nhds hx₁] with y hy
    exact (hg₁d y hy).mdifferentiableAt (hU₁.mem_nhds hy)
  have hhol₂ : HolomorphicAt n g₂ x := by
    filter_upwards [hU₂.mem_nhds hx₂] with y hy
    exact (hg₂d y hy).mdifferentiableAt (hU₂.mem_nhds hy)
  -- `g₂` lies in `𝔟` at `x`, hence is a multiple of `g₁`
  have hmem₂ : 𝔟.mem x g₂ :=
    (hgen₂ x hx₂ g₂).mpr
      (isInSpanAt_of_eq_mul rfl hhol₂ (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp))
  have hmem₁ : 𝔟.mem x g₁ :=
    (hgen₁ x hx₁ g₁).mpr
      (isInSpanAt_of_eq_mul rfl hhol₁ (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp))
  obtain ⟨-, u, hu, hueq⟩ := isInSpanAt_eq_iff.mp ((hgen₁ x hx₁ g₂).mp hmem₂)
  obtain ⟨-, v, hv, hveq⟩ := isInSpanAt_eq_iff.mp ((hgen₂ x hx₂ g₁).mp hmem₁)
  -- on a small neighbourhood both relations hold and `u`, `v` are holomorphic
  have hkey : ∀ᶠ y in 𝓝 x, (g₂ y = u y * g₁ y) ∧ (g₁ y = v y * g₂ y) ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u y ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) v y ∧ y ∈ U₁ ∧ y ∈ U₂ := by
    filter_upwards [hueq, hveq, hu, hv, hU₁.mem_nhds hx₁, hU₂.mem_nhds hx₂]
      with y h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hkey
  refine ⟨V, u, hV, hxV, fun y hy => ⟨(hVsub hy).2.2.2.2.1, (hVsub hy).2.2.2.2.2⟩,
    fun y hy => (hVsub hy).2.2.1, ?_, fun y hy => (hVsub hy).1⟩
  -- `u v = 1` on `V`: it holds where `g₁ ≠ 0`, a dense subset of `V`
  have hone : ∀ z ∈ V, g₁ z ≠ 0 → u z * v z = 1 := by
    intro z hz hz0
    have h1 : g₂ z = u z * g₁ z := (hVsub hz).1
    have h2 : g₁ z = v z * g₂ z := (hVsub hz).2.1
    have h3 : g₁ z = v z * (u z * g₁ z) := h2.trans (by rw [h1])
    have h4 : (1 - u z * v z) * g₁ z = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hz0
  intro y hy hu0
  have hcont : ContinuousAt (fun z => u z * v z) y :=
    ((hVsub hy).2.2.1.continuousAt).mul ((hVsub hy).2.2.2.1.continuousAt)
  have hne : (fun z => u z * v z) y ≠ 1 := by simp [hu0]
  obtain ⟨W, hWsub, hW, hyW⟩ := mem_nhds_iff.mp
    ((hcont.eventually_ne hne).and (hV.mem_nhds hy))
  obtain ⟨z, hzW, hz0⟩ := hg₁nz W hW
    (fun z hz => (hVsub (hWsub hz).2).2.2.2.2.1) ⟨y, hyW⟩
  exact (hWsub hzW).1 (hone z (hWsub hzW).2 hz0)


section Partition

variable (n M) in
/-- A finite cover of `M` by open sets carrying a local generator of `𝒪(-D)`, together with a
subordinate chart-smooth partition of unity.  On a compact manifold such data exist
(`exists_divisorPartition`). -/
structure DivisorPartition (D : EffectiveDivisor n M) where
  card : ℕ
  dom : Fin card → Set M
  isOpen_dom : ∀ a, IsOpen (dom a)
  gen : Fin card → M → ℂ
  gen_mdifferentiableOn : ∀ a,
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (gen a) (dom a)
  gen_nowhereZero : ∀ a, ∀ W : Set M, IsOpen W → W ⊆ dom a → W.Nonempty →
    ∃ y ∈ W, gen a y ≠ 0
  gen_spec : ∀ a, ∀ y ∈ dom a, ∀ f,
    D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = gen a) y f
  part : Fin card → M → ℝ
  part_chartSmooth : ∀ a, ChartSmooth (n := n) (part a)
  part_nonneg : ∀ a y, 0 ≤ part a y
  part_tsupport : ∀ a, tsupport (part a) ⊆ dom a
  part_sum : ∀ y, ∑ a, part a y = 1

theorem exists_divisorPartition [CompactSpace M] (D : EffectiveDivisor n M) :
    Nonempty (DivisorPartition n M D) := by
  classical
  choose S hS hmem g hgd hgnz hgspec using D.isInvertible
  obtain ⟨m, χ, idx, hχsm, hχnn, hχsupp, -, hχsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) (fun x : M => ⟨S x, hS x⟩)
      fun x => ⟨x, hmem x⟩
  exact ⟨⟨m, fun a => S (idx a), fun a => hS _, fun a => g (idx a), fun a => hgd _,
    fun a => hgnz _, fun a => hgspec _, χ, hχsm, hχnn, hχsupp, hχsum⟩⟩

namespace DivisorPartition

variable {D : EffectiveDivisor n M} (P : DivisorPartition n M D)

/-- `|g_a|²`, extended by zero off the domain of the `a`-th generator. -/
def genNormSq (a : Fin P.card) : M → ℝ :=
  (P.dom a).indicator fun y => Complex.normSq (P.gen a y)

theorem genNormSq_nonneg (a : Fin P.card) (y : M) : 0 ≤ P.genNormSq a y :=
  Set.indicator_nonneg (fun _ _ => Complex.normSq_nonneg _) y

/-- **The divisor weight** `U = ∑ₐ χₐ |g_a|²`. -/
def weight (y : M) : ℝ := ∑ a, P.part a y * P.genNormSq a y

theorem weight_nonneg (y : M) : 0 ≤ P.weight y :=
  Finset.sum_nonneg fun a _ => mul_nonneg (P.part_nonneg a y) (P.genNormSq_nonneg a y)

theorem part_eq_zero_of_notMem_tsupport {a : Fin P.card} {y : M}
    (hy : y ∉ tsupport (P.part a)) : P.part a y = 0 :=
  image_eq_zero_of_notMem_tsupport hy

/-- **The local factorization** `U = |g_{a₀}|² · U'` with `U'` smooth and positive, where
`g_{a₀}` is one of the local generators. -/
theorem exists_localFactor (x : M) :
    ∃ (V : Set M) (a₀ : Fin P.card) (U' : M → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ P.dom a₀ ∧
      (∀ e : ComplexChart n M, ContDiffOn ℝ ∞ (fun z => U' (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
      (∀ y ∈ V, 0 < U' y) ∧
      ∀ y ∈ V, P.weight y = Complex.normSq (P.gen a₀ y) * U' y := by
  classical
  -- a partition function positive at `x`
  obtain ⟨a₀, -, ha₀⟩ : ∃ a₀ ∈ Finset.univ, 0 < P.part a₀ x := by
    by_contra hcon
    push Not at hcon
    have : ∑ a, P.part a x ≤ 0 :=
      Finset.sum_nonpos fun a ha => hcon a ha
    rw [P.part_sum x] at this
    linarith
  have hx₀ : x ∈ P.dom a₀ := P.part_tsupport a₀ (subset_tsupport _ ha₀.ne')
  -- a unit relating each nearby generator to `g_{a₀}`
  have key : ∀ a : Fin P.card, ∃ (Va : Set M) (ua : M → ℂ), IsOpen Va ∧ x ∈ Va ∧
      Va ⊆ P.dom a₀ ∧
      (∀ y ∈ Va, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ua y) ∧
      (∀ y ∈ Va, P.part a y * Complex.normSq (ua y * P.gen a₀ y) =
        P.part a y * P.genNormSq a y) ∧
      (∀ y ∈ Va, 0 < P.part a y → ua y ≠ 0) := by
    intro a
    by_cases hxa : x ∈ tsupport (P.part a)
    · obtain ⟨V, u, hV, hxV, hVsub, hud, hun, hueq⟩ :=
        exists_unit_of_generators (𝔟 := D.ideal) (P.isOpen_dom a₀) (P.isOpen_dom a)
          (P.gen_mdifferentiableOn a₀) (P.gen_mdifferentiableOn a)
          (P.gen_nowhereZero a₀) (P.gen_spec a₀) (P.gen_spec a) hx₀ (P.part_tsupport a hxa)
      refine ⟨V, u, hV, hxV, fun y hy => (hVsub hy).1, hud, fun y hy => ?_,
        fun y hy _ => hun y hy⟩
      rw [← hueq y hy, genNormSq, Set.indicator_of_mem (hVsub hy).2]
    · refine ⟨(tsupport (P.part a))ᶜ ∩ P.dom a₀, 0,
        (isClosed_tsupport _).isOpen_compl.inter (P.isOpen_dom a₀), ⟨hxa, hx₀⟩,
        fun y hy => hy.2, fun y _ => mdifferentiableAt_const, fun y hy => ?_,
        fun y hy hpos => absurd (P.part_eq_zero_of_notMem_tsupport hy.1) hpos.ne'⟩
      rw [P.part_eq_zero_of_notMem_tsupport hy.1, zero_mul, zero_mul]
  choose V u hVopen hxV hVdom hud hfac hunz using key
  refine ⟨⋂ a, V a, a₀, fun y => ∑ a, P.part a y * Complex.normSq (u a y),
    isOpen_iInter_of_finite hVopen, mem_iInter.2 hxV,
    (iInter_subset _ a₀).trans (hVdom a₀), ?_, ?_, ?_⟩
  · -- smoothness
    intro e z hz
    have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' ⋂ a, V a) :=
      e.val.isOpen_inter_preimage_symm (isOpen_iInter_of_finite hVopen)
    refine ContDiffAt.contDiffWithinAt (ContDiffAt.sum fun a _ => ?_)
    refine ContDiffAt.mul ((P.part_chartSmooth a e).contDiffAt
      (e.val.open_target.mem_nhds hz.1)) ?_
    refine BlanchardWeight.BlanchardData.contDiffAt_normSq_comp ?_
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    exact differentiableAt_comp_chart_symm e hz'.1 (hud a _ (mem_iInter.mp hz'.2 a))
  · -- positivity
    intro y hy
    have hyV : ∀ a, y ∈ V a := fun a => mem_iInter.mp hy a
    obtain ⟨a, -, ha⟩ : ∃ a ∈ Finset.univ, 0 < P.part a y := by
      by_contra hcon
      push Not at hcon
      have : ∑ a, P.part a y ≤ 0 := Finset.sum_nonpos fun a ha => hcon a ha
      rw [P.part_sum y] at this
      linarith
    refine Finset.sum_pos' (fun b _ => mul_nonneg (P.part_nonneg b y) (Complex.normSq_nonneg _))
      ⟨a, Finset.mem_univ a, mul_pos ha (Complex.normSq_pos.mpr (hunz a y (hyV a) ha))⟩
  · -- the factorization
    intro y hy
    have hyV : ∀ a, y ∈ V a := fun a => mem_iInter.mp hy a
    rw [Finset.mul_sum, weight]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hfac a y (hyV a), Complex.normSq_mul]
    ring

/-- The zero locus of `𝒪(-D)` is read off any local generator. -/
theorem mem_support_iff {a : Fin P.card} {y : M} (hy : y ∈ P.dom a) :
    y ∈ D.support ↔ P.gen a y = 0 := by
  constructor
  · intro hmem
    refine hmem (P.gen a) ((P.gen_spec a y hy _).mpr ?_)
    refine isInSpanAt_of_eq_mul rfl ?_ (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)
    filter_upwards [(P.isOpen_dom a).mem_nhds hy] with z hz
    exact (P.gen_mdifferentiableOn a z hz).mdifferentiableAt ((P.isOpen_dom a).mem_nhds hz)
  · intro h0 f hf
    obtain ⟨-, c, -, hceq⟩ := isInSpanAt_eq_iff.mp ((P.gen_spec a y hy f).mp hf)
    rw [hceq.self_of_nhds]
    show c y * P.gen a y = 0
    rw [h0, mul_zero]

theorem weight_eq_zero_iff {y : M} : P.weight y = 0 ↔ y ∈ D.support := by
  obtain ⟨V, a₀, U', -, hyV, hVdom, -, hpos, hfac⟩ := P.exists_localFactor y
  rw [hfac y hyV, mul_eq_zero, P.mem_support_iff (hVdom hyV)]
  constructor
  · rintro (h | h)
    · exact Complex.normSq_eq_zero.mp h
    · exact absurd h (hpos y hyV).ne'
  · exact fun h => Or.inl (by rw [h]; simp)

theorem weight_nowhereZero (W : Set M) (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ y ∈ W, P.weight y ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, a₀, U', hV, hxV, hVdom, -, hpos, hfac⟩ := P.exists_localFactor x
  obtain ⟨y, hy, hy0⟩ := P.gen_nowhereZero a₀ (W ∩ V) (hW.inter hV)
    (fun z hz => hVdom hz.2) ⟨x, hx, hxV⟩
  refine ⟨y, hy.1, ?_⟩
  rw [hfac y hy.2]
  exact (mul_pos (Complex.normSq_pos.mpr hy0) (hpos y hy.2)).ne'

end DivisorPartition

end Partition

section Metric

/-- **`E` metrizes the effective divisor `D`**: near every point `ψ_E = log |g|² + h` with
`g` a local generator of `𝒪(-D)` and `h` chart-smooth.  This is the property that makes
`ψ_E` the weight `ψ_D` of the manuscript's `sec:qpsh` calculus. -/
def IsDivisorMetric (D : EffectiveDivisor n M) (E : MeteredEffectiveQDivisor n M) : Prop :=
  ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ g : M → ℂ,
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g V ∧
    (∀ y ∈ V, ∀ f, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
    ∃ h : M → ℝ,
      (∀ e : ComplexChart n M, ContDiffOn ℝ ∞ (fun z => h (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
      ∀ y ∈ V, E.weight y = generatorLog (fun _ : Fin 1 => g) y + (h y : EReal)

/-- **Every effective divisor on a compact complex manifold carries a smooth metric.**
`𝒪(D)` is equipped with the partition-of-unity metric built from local generators of
`𝒪(-D)`; the resulting metered `ℚ`-divisor has the same support and its weight is the
divisor weight `ψ_D`. -/
theorem exists_divisorMetric [CompactSpace M] (D : EffectiveDivisor n M) :
    ∃ E : MeteredEffectiveQDivisor n M, E.support = D.support ∧ IsDivisorMetric D E := by
  classical
  obtain ⟨P⟩ := exists_divisorPartition D
  choose V a₀ U' hV hxV hVdom hsm hpos hfac using P.exists_localFactor
  set F : WeightFactorization n P.weight :=
    { domain := V
      isOpen_domain := hV
      mem_domain := hxV
      gen := fun x => P.gen (a₀ x)
      smoothPart := U'
      gen_mdifferentiable := fun x y hy =>
        (P.gen_mdifferentiableOn (a₀ x) y (hVdom x hy)).mdifferentiableAt
          ((P.isOpen_dom (a₀ x)).mem_nhds (hVdom x hy))
      smooth := hsm
      pos := hpos
      factor := hfac
      nowhereZero := P.weight_nowhereZero } with hF
  refine ⟨ofWeightFactorization F 1 one_pos, ?_, ?_⟩
  · ext y
    show (((1 : ℚ) : ℝ) : EReal) * FactorizedWeightPsh.logWeight P.weight y = ⊥ ↔ _
    rw [← P.weight_eq_zero_iff]
    rcases eq_or_lt_of_le (P.weight_nonneg y) with h | h
    · have hbot : FactorizedWeightPsh.logWeight P.weight y = ⊥ := by
        simp [FactorizedWeightPsh.logWeight, ← h]
      simp [hbot, h.symm]
    · simp [FactorizedWeightPsh.logWeight_of_pos h, h.ne']
  · intro x
    refine ⟨V x, hV x, hxV x, P.gen (a₀ x),
      (P.gen_mdifferentiableOn (a₀ x)).mono (hVdom x),
      fun y hy => P.gen_spec (a₀ x) y (hVdom x hy),
      fun y => Real.log (U' x y),
      fun e => (hsm x e).log fun u hu => (hpos x _ hu.2).ne', fun y hy => ?_⟩
    show (((1 : ℚ) : ℝ) : EReal) * FactorizedWeightPsh.logWeight P.weight y = _
    have hsplit : FactorizedWeightPsh.logWeight P.weight y =
        generatorLog (fun _ : Fin 1 => P.gen (a₀ x)) y +
          (Real.log (U' x y) : EReal) := by
      rw [FactorizedWeightPsh.logWeight, hfac x y hy, generatorLog_eq_log_sum,
        ENNReal.ofReal_mul (Complex.normSq_nonneg _), ENNReal.log_mul_add,
        ENNReal.log_ofReal_of_pos (hpos x y hy)]
      simp [Complex.normSq_eq_norm_sq]
    rw [hsplit]
    simp

/-- Membership in the span of `g` is membership in the span of the one-element family
`![g]`. -/
theorem isInSpanAt_eq_iff_mem_range {g f : M → ℂ} {x : M} :
    IsInSpanAt (n := n) (· = g) x f ↔
      IsInSpanAt (n := n) (· ∈ range (fun _ : Fin 1 => g)) x f := by
  constructor
  · exact IsInSpanAt.mono fun s hs => ⟨0, hs.symm⟩
  · refine IsInSpanAt.mono fun s hs => ?_
    rcases hs with ⟨i, hi⟩
    exact hi.symm

/-- An invertible ideal is coherent: one generator is a family of generators. -/
theorem isCoherent_of_isInvertible {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsInvertible) :
    𝔟.IsCoherent := by
  intro x
  obtain ⟨U, hU, hxU, g, hgd, -, hgspec⟩ := h𝔟 x
  exact ⟨U, hU, hxU, 1, fun _ => g, fun _ => hgd,
    fun y hy f => (hgspec y hy f).trans isInSpanAt_eq_iff_mem_range⟩

/-- **`ψ_D` has analytic singularities of type `(1, 𝒪(-D))`.**  This is the
`sec:qpsh` identity `ψ_𝔞 = ψ_D + O(1)` for an invertible `𝔞 = 𝒪(-D)`: the divisor
weight supplied by a smooth metric and the ideal weight differ by a bounded
function.  The bound is obtained on a compact neighbourhood, which is where the
chart-smooth remainder of `IsDivisorMetric` becomes a genuine `O(1)`. -/
theorem hasAnalyticSingularitiesOfType_of_isDivisorMetric {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : IsDivisorMetric D E) :
    HasAnalyticSingularitiesOfType E.weight 1 D.ideal := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  refine ⟨one_pos, isCoherent_of_isInvertible D.isInvertible, fun x => ?_⟩
  obtain ⟨V, hV, hxV, g, hgd, hgspec, h, hsm, hweq⟩ := hE x
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_subset hV hxV
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := h) fun y hy =>
      (MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn hV hsm
        (hKV hy)).continuousWithinAt
  refine ⟨interior K, isOpen_interior, hxK, 1, fun _ => g,
    fun _ => hgd.mono (interior_subset.trans hKV),
    fun y hy f => (hgspec y (hKV (interior_subset hy)) f).trans isInSpanAt_eq_iff_mem_range,
    h, C, fun y hy => hC y (interior_subset hy), fun y hy => ?_⟩
  rw [hweq y (hKV (interior_subset hy))]
  norm_num

end Metric


end

end Hironaka.DivisorMetric
