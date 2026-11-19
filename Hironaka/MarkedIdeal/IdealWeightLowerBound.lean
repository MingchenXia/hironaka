import Hironaka.Analytic.IdealPresentation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# An ideal weight is bounded below off the zero locus

Source: Copy-4, Step 5 of `prop:principalization`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1936-1942`),
where `eq:QM-lower` is obtained from `eq:IV-H`,
`ψ_{𝓘_V}∘π = ψ_H + ψ_{𝓘_W} + O(1)`, by discarding `ψ_{𝓘_W}` with the words
"where `ψ_{𝓘_W}` is bounded on `Λ`".

`Λ` there is a compact subset of `U \ W`, so it is disjoint from `Z(𝓘_W) = W`,
and the assertion is the *lower* bound (the upper one is
`IdealWeightComparison.exists_le_of_hasAnalyticSingularitiesOfType`, which needs
no disjointness).  It is proved here: near a point off the zero locus not all
generators of a local presentation vanish, so `∑|gᵢ|²` is bounded below by a
positive constant on a neighbourhood, and `ψ = c log ∑|gᵢ|² + R` with `R`
bounded; compactness then gives one constant.

`Pending/MeteredDivisorWeightBounds.exists_bound_of_isCompact_disjoint_support`
is the same statement for a *divisor* weight.  It is not usable here: `𝓘_W` is
the ideal of a submanifold of codimension `> 1` and is not the ideal of a
divisor.

With this, `hIWb` of
`CollarWeightComparison.moreSingularOn_ambientLowerBound` is discharged.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology

namespace Hironaka.IdealWeightLowerBound

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison

noncomputable section

/-! ### The elementary lower bound on `ψ_g` -/

variable {X : Type*}

/-- `ψ_g ≥ log A` wherever `∑|gᵢ|² ≥ A > 0`.  This is the mirror of
`IdealWeightComparison.generatorLog_le_of_generatorNormSq_le`. -/
theorem le_generatorLog_of_le_generatorNormSq {N : ℕ} {f : Fin N → X → ℂ} {y : X}
    {A : ℝ} (hA : 0 < A) (hfy : A ≤ generatorNormSq f y) :
    ((Real.log A : ℝ) : EReal) ≤ generatorLog f y := by
  rw [generatorLog_eq_log_sum]
  calc ((Real.log A : ℝ) : EReal) = ENNReal.log (ENNReal.ofReal A) :=
        (ENNReal.log_ofReal_of_pos hA).symm
    _ ≤ ENNReal.log (ENNReal.ofReal (∑ i, ‖f i y‖ ^ 2)) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal
          (by simpa only [generatorNormSq] using hfy))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Off the zero locus the generators do not all vanish -/

/-- **At a point off `Z(𝔞)` some generator of a local presentation is nonzero.**
If they all vanished at `x`, every germ of `𝔞` at `x` — being a holomorphic
combination of them — would vanish at `x`, which is what `x ∈ Z(𝔞)` means. -/
theorem generatorNormSq_pos_of_notMem_zeroLocus {𝔞 : GermIdeal n M} {U : Set M}
    {N : ℕ} {g : Fin N → M → ℂ} {x : M} (hxU : x ∈ U)
    (hgiff : ∀ y ∈ U, ∀ h, 𝔞.mem y h ↔ IsInSpanAt (n := n) (· ∈ range g) y h)
    (hx : x ∉ 𝔞.zeroLocus) : 0 < generatorNormSq g x := by
  rcases (generatorNormSq_nonneg g x).lt_or_eq with h | h
  · exact h
  · refine absurd (fun v hv => ?_) hx
    have hzero : ∀ i, g i x = 0 := by
      intro i
      have hsum : ∑ j, ‖g j x‖ ^ 2 = 0 := by
        simpa only [generatorNormSq] using h.symm
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ‖g j x‖)).mp hsum i (Finset.mem_univ i)
      simpa using hi
    obtain ⟨-, K, s, a, hs, -, hsum⟩ := (hgiff x hxU v).mp hv
    have hsx : ∀ k, s k x = 0 := by
      intro k
      obtain ⟨j, hj⟩ := hs k
      rw [← hj]
      exact hzero j
    rw [hsum.eq_of_nhds]
    simp [hsx]

/-! ### The bound on a compact set -/

/-- **A weight with analytic singularities is bounded below on a compact set
disjoint from the zero locus of its ideal.**  This is Copy-4's "`ψ_{𝓘_W}` is
bounded on `Λ`" of Step 5. -/
theorem exists_le_on_of_isCompact_disjoint_zeroLocus {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    {Λ : Set M} (hΛ : IsCompact Λ) (hdisj : Disjoint Λ 𝔞.zeroLocus) :
    ∃ K : ℝ, ∀ y ∈ Λ, (K : EReal) ≤ φ y := by
  classical
  obtain ⟨hc, -, hpres⟩ := hφ
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have key : ∀ x ∈ Λ, ∃ (V : Set M) (K : ℝ),
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, (K : EReal) ≤ φ y := by
    intro x hx
    obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres x
    have hpos := generatorNormSq_pos_of_notMem_zeroLocus hxU hgiff
      (Set.disjoint_left.mp hdisj hx)
    set A : ℝ := generatorNormSq g x / 2 with hAdef
    have hA : 0 < A := by rw [hAdef]; linarith
    have hlt : A < generatorNormSq g x := by rw [hAdef]; linarith
    have hgc : ∀ i, ContinuousAt (g i) x := fun i =>
      ((hgdiff i x hxU).mdifferentiableAt (hU.mem_nhds hxU)).continuousAt
    have hcont : ContinuousAt (fun y => ∑ i, ‖g i y‖ ^ 2) x :=
      tendsto_finsetSum _ fun i _ => ((hgc i).norm).pow 2
    have hAy : ∀ᶠ y in 𝓝 x, A ≤ generatorNormSq g y :=
      (continuousAt_const.eventually_lt hcont hlt).mono fun _ hy => hy.le
    obtain ⟨V, hVsub, hVopen, hxV⟩ :=
      mem_nhds_iff.mp (inter_mem hAy (hU.mem_nhds hxU))
    refine ⟨V, (c : ℝ) * Real.log A - C₀, hVopen, hxV, fun y hy => ?_⟩
    have hyA : A ≤ generatorNormSq g y := (hVsub hy).1
    have hyU : y ∈ U := (hVsub hy).2
    rw [hφeq y hyU]
    have h1 : (((c : ℝ) * Real.log A : ℝ) : EReal)
        ≤ ((c : ℝ) : EReal) * generatorLog g y := by
      calc (((c : ℝ) * Real.log A : ℝ) : EReal)
          = ((c : ℝ) : EReal) * ((Real.log A : ℝ) : EReal) := by rw [← EReal.coe_mul]
        _ ≤ ((c : ℝ) : EReal) * generatorLog g y :=
            monotone_eReal_const_mul hcR.le
              (le_generatorLog_of_le_generatorNormSq hA hyA)
    calc (((c : ℝ) * Real.log A - C₀ : ℝ) : EReal)
        = (((c : ℝ) * Real.log A : ℝ) : EReal) + ((-C₀ : ℝ) : EReal) := by
          rw [← EReal.coe_add, sub_eq_add_neg]
      _ ≤ ((c : ℝ) : EReal) * generatorLog g y + (R y : EReal) :=
          add_le_add h1 (EReal.coe_le_coe_iff.mpr
            (by linarith [(abs_le.mp (hRb y hyU)).1]))
  choose! V K hVopen hxV hKle using key
  obtain ⟨b, hbΛ, hbfin, hcover⟩ := hΛ.elim_finite_subcover_image
    (fun x hx => hVopen x hx) (fun x hx => mem_biUnion hx (hxV x hx))
  rcases hbfin.toFinset.eq_empty_or_nonempty with ht | ht
  · refine ⟨0, fun y hy => ?_⟩
    obtain ⟨x, hxb, -⟩ := mem_iUnion₂.mp (hcover hy)
    have hxt : x ∈ hbfin.toFinset := hbfin.mem_toFinset.mpr hxb
    rw [ht] at hxt
    simp at hxt
  · refine ⟨hbfin.toFinset.inf' ht K, fun y hy => ?_⟩
    obtain ⟨x, hxb, hyV⟩ := mem_iUnion₂.mp (hcover hy)
    have hxt : x ∈ hbfin.toFinset := hbfin.mem_toFinset.mpr hxb
    exact le_trans (EReal.coe_le_coe_iff.mpr (Finset.inf'_le K hxt))
      (hKle x (hbΛ hxb) y hyV)

end

end Hironaka.IdealWeightLowerBound
