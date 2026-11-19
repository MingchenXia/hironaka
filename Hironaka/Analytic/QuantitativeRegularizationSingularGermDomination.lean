import Hironaka.Analytic.QuantitativeRegularizationSingularOverlap
import Hironaka.Analytic.QuantitativeRegularizationGermDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 4 of Copy-4 `lem:regularization` for the singular weight `e^{-mΨ}`

Source: Copy-4, `lem:regularization`, Step 4 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationGermDomination.normSq_le_bergmanSup` is the germ-domination
half of the regularization lemma — the inequality `φ_m ≥ m⁻¹ ψ_{𝓘(mφ)} + O(1)` in the
weak form the Lean statement of `QuantitativeRegularization` asks for.  Like everything
upstream it needs a *smooth* weight `ϕ` bounded below on `D`, whereas the weight that gets
substituted is `ϕ = m Ψ` with `Ψ` plurisubharmonic, hence `-∞` on a polar set.

This module removes that restriction.  The passage is the same two-layer limit as in
`QuantitativeRegularizationSingularOverlap` — truncate, then mollify — but the shape of the
inequality is different, and so is the reason the constant survives:

* `le_mul_bergmanSup_multiplierWeight_of_smoothPsh` is the limit with a **constant** on the
  left.  Only the `≥` half of the two limits is used, so the statement follows from the two
  *equalities* `bergmanSup(e^{-cu}) = ⨅ bergmanSup(e^{-c·truncation})` and
  `bergmanSup(e^{-c·truncation}) = ⨅ bergmanSup(e^{-c·mollification})` together with
  `le_mul_iInf`.
* Its `hcomp` hypothesis carries one clause the overlap version does not need: the smooth
  approximant **dominates** `u` on `A`.  That clause is what keeps the weighted mass finite
  along the approximation, and it is available for free — mollifying the `k`-th truncation
  from above produces functions `≥ max(u, -k) ≥ u`.

The endpoint is `normSq_le_bergmanSup_multiplierWeight`: for `g` holomorphic near the
cut-off support whose weighted mass `N = ∫ |g|² e^{-mΨ}` over `tsupport θ` is finite — i.e.
for a germ of the multiplier ideal `𝓘(mΨ)` — and for every `y` near `x`,

> `|g y|² ≤ (C·N + 1) · bergmanSup B_j (e^{-mΨ}) y`,  `C = pointExtensionConst d (r/2) Mθ (2S) S`.

The constant is the *same* `pointExtensionConst` as in the smooth theory: it involves the
dimension, the cut-off and the size of `B_j`, and nothing about the weight.  `N` enters
only through the finiteness hypothesis, exactly as in the smooth case.

Why the mass stays finite along the approximation: the `j`-th mollification `f_j` of the
`k`-th truncation satisfies `f_j ≥ u` on `A`, so `e^{-m f_j} ≤ e^{-mu}` pointwise and the
approximate masses are all bounded by `N`.  Since `pointExtensionConst` does not see the
weight, one constant `C·N + 1` serves every level of both layers, which is precisely the
hypothesis `le_mul_bergmanSup_multiplierWeight_of_smoothPsh` consumes.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace Hironaka.QuantitativeRegularizationSingularGermDomination

noncomputable section

open Hironaka.MongeAmpere BergmanSupWeight
open Hironaka.QuantitativeRegularizationGermDomination
open Hironaka.QuantitativeRegularizationPointExtension
open Hironaka.QuantitativeRegularizationSingularWeight
open Hironaka.QuantitativeRegularizationTruncationLimit
open Hironaka.QuantitativeRegularizationSmoothWeightLimit
open Hironaka.QuantitativeRegularizationSingularOverlap

variable {d : ℕ}

/-! ### A constant bound passes to an infimum -/

/-- If `a ≤ C · f i` for every `i` with `C` finite, then `a ≤ C · ⨅ i, f i`. -/
theorem le_mul_iInf {C : ℝ≥0∞} (hCtop : C ≠ ⊤) {a : ℝ≥0∞} {ι : Sort*} [Nonempty ι]
    {f : ι → ℝ≥0∞} (h : ∀ i, a ≤ C * f i) : a ≤ C * ⨅ i, f i := by
  rw [ENNReal.mul_iInf fun htop => absurd htop hCtop]
  exact le_iInf h

/-! ### The two-layer limit with a constant on the left -/

variable {A Ω : Opens (ComplexModel d)} {u : ComplexModel d → EReal} {c : ℝ}

/-- **The two-layer singular-weight limit, constant-on-the-left form.**  A bound
`a ≤ C · bergmanSup D (e^{-cg})` valid for every smooth plurisubharmonic `g` that is
bounded below on `A` *and dominates `u` there* is a bound for the singular weight `e^{-cu}`.

Only the `≥` half of each of the two limits is needed, so this is a consequence of the two
equalities plus `le_mul_iInf`.  The domination clause `u ≤ g` is the one the germ-domination
consumer cannot do without: it is what bounds the approximate weighted masses by the
singular one. -/
theorem le_mul_bergmanSup_multiplierWeight_of_smoothPsh
    (hA : RelativelyCompactIn A Ω) (hu : PlurisubharmonicOn u Ω) (hc : 0 < c)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDA : D ⊆ (A : Set (ComplexModel d)))
    {y : ComplexModel d} (hy : y ∈ D)
    {a C : ℝ≥0∞} (hCtop : C ≠ ⊤)
    (hcomp : ∀ g : ComplexModel d → ℝ, IsSmoothPshOn A g →
      (∃ B : ℝ, ∀ z ∈ (A : Set (ComplexModel d)), B ≤ g z) →
      (∀ z ∈ (A : Set (ComplexModel d)), u z ≤ ((g z : ℝ) : EReal)) →
      a ≤ C * bergmanSup D (fun z => multiplierWeight c ((g z : ℝ) : EReal)) y) :
    a ≤ C * bergmanSup D (fun z => multiplierWeight c (u z)) y := by
  have hAΩ : (A : Set (ComplexModel d)) ⊆ Ω := subset_closure.trans hA.2
  rw [bergmanSup_multiplierWeight_eq_iInf_truncationWeight hu hc hDo (hDA.trans hAΩ) hy]
  refine le_mul_iInf hCtop fun k => ?_
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
    (truncationReal_isLocallyBoundedPshOn hu k) hA
  have hstep : bergmanSup D (truncationWeight c u k) y
      = ⨅ j : ℕ, bergmanSup D
          (fun z => multiplierWeight c ((f j z : ℝ) : EReal)) y :=
    bergmanSup_multiplierWeight_eq_iInf_smoothWeight hf hc.le hDo hDA hy
  rw [hstep]
  refine le_mul_iInf hCtop fun j => ?_
  -- the `k`-th truncation is bounded below by `-k`, hence so is every approximant
  have htrunc : ∀ z ∈ (A : Set (ComplexModel d)),
      ((truncationReal u k z : ℝ) : EReal) ≤ ((f j z : ℝ) : EReal) := fun z hz =>
    EReal.coe_le_coe_iff.mpr (le_of_isDecreasingApproximation hf j hz)
  refine hcomp (f j) (hf.1 j) ⟨-(k : ℝ), fun z hz => ?_⟩ fun z hz => ?_
  · refine EReal.coe_le_coe_iff.mp (le_trans ?_ (htrunc z hz))
    rw [coe_truncationReal hu k (hAΩ hz)]
    exact truncation_lower_bound u k z
  · refine le_trans ?_ (htrunc z hz)
    rw [coe_truncationReal hu k (hAΩ hz)]
    exact le_max_left _ _

/-! ### Germ domination for the singular weight -/

/-- **A germ of `𝓘(mΨ)` is dominated by the Bergman sup-weight of the singular weight**
(Copy-4, `lem:regularization`, Step 4, for `ϕ = m Ψ`).

`Ψ` is an arbitrary plurisubharmonic function on `Ω` and may be `-∞` on a polar set; `A` is
a convex open set, relatively compact in `Ω`, containing the cut-off support and the closure
of `B_j`.  The constant `pointExtensionConst d (r/2) Mθ (2S) S` is the one the smooth theory
produces and does not mention the weight; `N` enters only through its finiteness, which is
the statement that `g` is a germ of the multiplier ideal. -/
theorem normSq_le_bergmanSup_multiplierWeight (hd : 0 < d)
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    (hu : PlurisubharmonicOn u Ω) {m : ℝ} (hm : 0 < m)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {U : Set (ComplexModel d)} (hUo : IsOpen U) (hts : tsupport θ ⊆ U)
    (htsA : tsupport θ ⊆ (A : Set (ComplexModel d)))
    {g : ComplexModel d → ℂ} (hg : DifferentiableOn ℂ g U)
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcA : Bjc ⊆ (A : Set (ComplexModel d)))
    {S : ℝ} (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    (hN : (∫⁻ z in tsupport θ,
      ENNReal.ofReal (‖g z‖ ^ 2) * multiplierWeight m (u z)) ≠ ⊤)
    {y : ComplexModel d} (hyBj : y ∈ Bj) (hyx : ‖y - x‖ < r / 2) :
    ENNReal.ofReal (‖g y‖ ^ 2) ≤
      (ENNReal.ofReal (pointExtensionConst d (r / 2) Mθ (2 * S) S) *
        (∫⁻ z in tsupport θ,
          ENNReal.ofReal (‖g z‖ ^ 2) * multiplierWeight m (u z)) + 1) *
        bergmanSup Bj (fun z => multiplierWeight m (u z)) y := by
  set N : ℝ≥0∞ := ∫⁻ z in tsupport θ,
    ENNReal.ofReal (‖g z‖ ^ 2) * multiplierWeight m (u z) with hNdef
  set Cc : ℝ := pointExtensionConst d (r / 2) Mθ (2 * S) S with hCc
  have hAb : Bornology.IsBounded (A : Set (ComplexModel d)) :=
    hAΩ.1.isBounded.subset subset_closure
  have hCtop : ENNReal.ofReal Cc * N + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN, by simp⟩
  refine le_mul_bergmanSup_multiplierWeight_of_smoothPsh hAΩ hu hm hBjo
    (hBjBjc.trans hBjcA) hyBj hCtop ?_
  intro G hG hGB hGu
  obtain ⟨B, hB⟩ := hGB
  obtain ⟨hsmooth, hlevi⟩ := smul_isAdmissibleWeight hG hm.le
  -- the rescaled smooth weight is bounded below on `A`
  have hlower : ∀ z ∈ (A : Set (ComplexModel d)), -(-(m * B)) ≤ m * G z := fun z hz => by
    simpa using mul_le_mul_of_nonneg_left (hB z hz) hm.le
  -- and bounded above on the compact `Bjc`, hence on `Bj`
  obtain ⟨B₀, hB₀⟩ := hBjc.exists_bound_of_continuousOn (hG.1.continuousOn.mono hBjcA)
  have hupper : ∀ z ∈ Bj, m * G z ≤ m * B₀ := fun z hz =>
    mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hB₀ z (hBjBjc hz))) hm.le
  -- the approximate weighted mass is bounded by the singular one
  have hweight : ∀ z ∈ (A : Set (ComplexModel d)),
      multiplierWeight m ((G z : ℝ) : EReal) ≤ multiplierWeight m (u z) := fun z hz =>
    multiplierWeight_antitone hm.le (hGu z hz)
  have hNG : (∫⁻ z in tsupport θ, ENNReal.ofReal (‖g z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-(m * G z)))) ≤ N := by
    rw [hNdef]
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hθcs.measurableSet).2 (Filter.Eventually.of_forall ?_)
    intro z hz
    exact mul_le_mul' le_rfl
      (by simpa only [multiplierWeight_coe] using hweight z (htsA hz))
  have hNGtop : (∫⁻ z in tsupport θ, ENNReal.ofReal (‖g z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-(m * G z)))) ≠ ⊤ := ne_top_of_le_ne_top hN hNG
  have hkey := normSq_le_bergmanSup hd A.isOpen hAconv hAb hsmooth hlevi hlower x hr
    hθ hθcs hθ1 hθle hUo hts htsA hg hMθ hBjo hBjBjc hBjc hBjcA hupper hnormS hNGtop
    hyBj hyx
  simp only [multiplierWeight_coe]
  exact hkey.trans
    (mul_le_mul' (by
      rw [hCc]
      exact add_le_add_left (mul_le_mul' le_rfl hNG) 1) le_rfl)

end

end Hironaka.QuantitativeRegularizationSingularGermDomination
