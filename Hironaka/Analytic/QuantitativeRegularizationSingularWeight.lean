import Hironaka.Analytic.BergmanSupWeight
import Hironaka.Analytic.WeightedL2ExtensionLimit

set_option autoImplicit false

/-!
# The Bergman kernel of a singular weight as a decreasing limit of regular ones

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.  Demailly, *Analytic methods in algebraic geometry*,
Theorem 13.2 and its proof.

Every quantitative statement about `bergmanSup` that the regularization chain
currently has — `QuantitativeRegularizationBergmanOverlap.bergmanSup_le_of_pointExtension`
and everything built on it, up to `BergmanOverlapFixedCover.exists_overlapConst_finite` —
assumes the weight `e^{-ϕ}` has `ϕ` **smooth** and **bounded below**.  Copy-4 applies
those statements to `ϕ = m Ψ` with `Ψ` merely plurisubharmonic, hence `-∞` on a polar
set.  This is the most blocking gap of the whole chain, and no
bookkeeping closes it: replacing `Ψ` by `max (Ψ, -k)` makes the weight
`e^{-ϕ}` **smaller**, hence the weighted unit ball **larger** and `bergmanSup`
**larger**, so the comparison has to be closed by a limit from above, not by monotone
convergence.

This module supplies that limit.

* `bergmanBall_subset_of_weight_le` / `bergmanSup_antitone_weight` — the elementary
  half: a larger weight has a smaller unit ball, hence a smaller kernel.  This is the
  direction that makes the truncated kernels *decrease*.
* `bergmanSup_congr_of_eqOn` — only the values of a weight on `D` matter.
* `bergmanSup_iSup_weight` — **the limit itself**: for a sequence of weights increasing
  on `D` and locally bounded below there by a positive constant, the kernel of any
  weight whose restriction to `D` is their pointwise supremum is the *infimum* of the
  kernels, `bergmanSup D w∞ y = ⨅ i, bergmanSup D (w i) y`.
  The nontrivial inequality is `≥`: a family of competitors, one in each truncated
  unit ball, is locally uniformly bounded (the weights are bounded below), so Montel
  extracts a locally uniform limit, Fatou plus monotone convergence keep it inside the
  unit ball of the supremum weight (`WeightedL2ExtensionLimit`), and locally uniform
  convergence transports the point value.
* `bergmanSup_le_mul_of_iSup_weight` — the consequence the overlap estimate needs: a
  comparison `bergmanSup D₁ (w i) y ≤ C · bergmanSup D₂ (w i) y` that holds for every
  member of the approximating sequence, with a constant `C` independent of `i`, passes
  to the singular weight.  This is the exact shape of Copy-4's `eq:reg-overlap`, whose
  constant is already known to be weight-independent
  (`BergmanOverlapFixedCover.exists_overlapConst_finite`).

Nothing here assumes plurisubharmonicity, smoothness, or any relation between `D₁` and
`D₂`: the statements are about weighted Bergman kernels alone, so they apply verbatim to
the smooth truncations `ϕ_k = m · max (Ψ, -k)` and, after
`HolomorphicPullback.exists_decreasingMollifierApproximation`, to their smooth
regularizations.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology

namespace Hironaka.QuantitativeRegularizationSingularWeight

noncomputable section

open BergmanSupWeight

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-! ### Monotonicity in the weight

Only the values of the weight on `D` matter: the unit ball constrains an integral over
`D` alone.  All hypotheses below are therefore stated on `D`. -/

/-- A weight larger **on `D`** has a smaller weighted unit ball. -/
theorem bergmanBall_subset_of_weight_le {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {w w' : ComplexModel d → ℝ≥0∞} (h : ∀ z ∈ D, w z ≤ w' z) :
    bergmanBall D w' ⊆ bergmanBall D w := by
  rintro f ⟨hf, hint⟩
  refine ⟨hf, le_trans (lintegral_mono_ae ?_) hint⟩
  filter_upwards [ae_restrict_mem hD] with z hz
  gcongr
  exact h z hz

/-- **The Bergman kernel is antitone in the weight.**  This is what makes the kernels of
the truncations `max (Ψ, -k)` decrease as `k` grows. -/
theorem bergmanSup_antitone_weight {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {w w' : ComplexModel d → ℝ≥0∞} (h : ∀ z ∈ D, w z ≤ w' z) (y : ComplexModel d) :
    bergmanSup D w' y ≤ bergmanSup D w y :=
  iSup₂_le fun _ hf => le_bergmanSup (bergmanBall_subset_of_weight_le hD h hf) y

/-- Weights agreeing on `D` have the same unit ball. -/
theorem bergmanBall_congr_of_eqOn {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {w w' : ComplexModel d → ℝ≥0∞} (h : ∀ z ∈ D, w z = w' z) :
    bergmanBall D w = bergmanBall D w' :=
  Subset.antisymm (bergmanBall_subset_of_weight_le hD fun z hz => (h z hz).ge)
    (bergmanBall_subset_of_weight_le hD fun z hz => (h z hz).le)

/-- Weights agreeing on `D` have the same kernel. -/
theorem bergmanSup_congr_of_eqOn {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {w w' : ComplexModel d → ℝ≥0∞} (h : ∀ z ∈ D, w z = w' z) (y : ComplexModel d) :
    bergmanSup D w y = bergmanSup D w' y := by
  simp only [bergmanSup, bergmanBall_congr_of_eqOn hD h]

/-! ### The limit -/

/-- **A normal-family limit inside the weighted unit balls.**  Competitors `F i` in the
unit balls of an increasing sequence of weights have a subsequence converging locally
uniformly to a competitor for the supremum weight.  This is
`WeightedL2ExtensionLimit.exists_subseq_differentiableOn_extension_of_weighted_bounds`
on the constant exhaustion `U i = D`, with no interpolation data. -/
theorem exists_subseq_mem_bergmanBall_iSup
    {D : Set (ComplexModel d)} (hD : IsOpen D)
    {w : ℕ → ComplexModel d → ℝ≥0∞} (hwm : ∀ z ∈ D, Monotone fun i => w i z)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict D))
    (hlow : ∀ x ∈ D, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ w 0 y)
    {F : ℕ → ComplexModel d → ℂ} (hF : ∀ i, F i ∈ bergmanBall D (w i)) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel d → ℂ), StrictMono ψ ∧
      G ∈ bergmanBall D (fun z => ⨆ i, w i z) ∧
      TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop D := by
  have hUnion : (⋃ _ : ℕ, D) = D := iUnion_const D
  have hwm' : ∀ x ∈ (⋃ _ : ℕ, D), Monotone fun i => w i x := by
    simpa only [hUnion] using hwm
  have hwmeas' : ∀ i, AEMeasurable (w i) (volume.restrict (⋃ _ : ℕ, D)) := by
    simpa only [hUnion] using hwmeas
  have hlow' : ∀ x ∈ (⋃ _ : ℕ, D), ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ w 0 y := by
    simpa only [hUnion] using hlow
  obtain ⟨ψ, G, hψ, hG, hconv, -, hGint⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds
      (N := d) (α := Empty) (ι := Empty.elim) (g := Empty.elim)
      (U := fun _ : ℕ => D) (fun _ => hD) monotone_const (w := w)
      hwm' hwmeas' hlow'
      (F := F) (fun i => (hF i).1) (fun _ a _ => a.elim)
      (A := 1) ENNReal.one_ne_top (fun i => (hF i).2)
  rw [hUnion] at hG hconv hGint
  exact ⟨ψ, G, hψ, ⟨hG, hGint⟩, hconv⟩

/-- **The Bergman kernel of a singular weight is the decreasing limit of the regular
ones.**  For an increasing sequence of weights, locally bounded below by a positive
constant, the kernel of the pointwise supremum is the infimum of the kernels.

Applied to `w i = e^{-m·max (Ψ, -i)}` — or to any smooth decreasing regularization of
those truncations — this is the statement that closes that gap: a bound for the
kernels of the regular weights, uniform in `i`, is a bound for the kernel of `e^{-mΨ}`. -/
theorem bergmanSup_iSup_weight
    {D : Set (ComplexModel d)} (hD : IsOpen D)
    {w : ℕ → ComplexModel d → ℝ≥0∞} (hwm : ∀ z ∈ D, Monotone fun i => w i z)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict D))
    (hlow : ∀ x ∈ D, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ w 0 y)
    {winf : ComplexModel d → ℝ≥0∞} (hwinf : ∀ z ∈ D, winf z = ⨆ i, w i z)
    {y : ComplexModel d} (hy : y ∈ D) :
    bergmanSup D winf y = ⨅ i, bergmanSup D (w i) y := by
  rw [bergmanSup_congr_of_eqOn hD.measurableSet hwinf y]
  refine le_antisymm
    (le_iInf fun i => bergmanSup_antitone_weight hD.measurableSet
      (fun z _ => le_iSup (fun j => w j z) i) y) ?_
  by_contra hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between (not_le.1 hcon)
  have hpick : ∀ i, ∃ f, f ∈ bergmanBall D (w i) ∧ t < ENNReal.ofReal (‖f y‖ ^ 2) := by
    intro i
    have hti : t < bergmanSup D (w i) y := lt_of_lt_of_le ht2 (iInf_le _ i)
    simpa only [bergmanSup, lt_iSup_iff, exists_prop] using hti
  choose F hFmem hFt using hpick
  obtain ⟨ψ, G, _, hGmem, hconv⟩ :=
    exists_subseq_mem_bergmanBall_iSup hD hwm hwmeas hlow hFmem
  have hpt : Tendsto (fun i => F (ψ i) y) atTop (𝓝 (G y)) := hconv.tendsto_at hy
  have hsq : Tendsto (fun i => ENNReal.ofReal (‖F (ψ i) y‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖G y‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hpt.norm.pow 2)
  have hGt : t ≤ ENNReal.ofReal (‖G y‖ ^ 2) :=
    ge_of_tendsto hsq (Eventually.of_forall fun i => (hFt (ψ i)).le)
  exact absurd (hGt.trans (le_bergmanSup hGmem y)) (not_le.2 ht1)

/-- **A weight-uniform comparison passes to the singular weight.**  If the two Bergman
kernels of an increasing family of weights are comparable with ONE constant `C`, then so
are the kernels of the supremum weight.  Only the right-hand domain needs the hypotheses
of the limit theorem.

This is exactly how Copy-4's `eq:reg-overlap` is used: `C_B` is fixed by the cover before
the weight (`BergmanOverlapFixedCover.exists_overlapConst_finite`), so the comparison is
available for every member of an approximating sequence with the same `C`. -/
theorem bergmanSup_le_mul_of_iSup_weight
    {D₁ D₂ : Set (ComplexModel d)} (hD₁ : MeasurableSet D₁) (hD₂ : IsOpen D₂)
    {w : ℕ → ComplexModel d → ℝ≥0∞} (hwm : ∀ z ∈ D₂, Monotone fun i => w i z)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict D₂))
    (hlow : ∀ x ∈ D₂, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ w 0 y)
    {winf : ComplexModel d → ℝ≥0∞}
    (hwinf₁ : ∀ z ∈ D₁, winf z = ⨆ i, w i z) (hwinf₂ : ∀ z ∈ D₂, winf z = ⨆ i, w i z)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    {y : ComplexModel d} (hy : y ∈ D₂)
    (hcomp : ∀ i, bergmanSup D₁ (w i) y ≤ C * bergmanSup D₂ (w i) y) :
    bergmanSup D₁ winf y ≤ C * bergmanSup D₂ winf y := by
  calc bergmanSup D₁ winf y
      ≤ ⨅ i, bergmanSup D₁ (w i) y := by
        rw [bergmanSup_congr_of_eqOn hD₁ hwinf₁ y]
        exact le_iInf fun i => bergmanSup_antitone_weight hD₁
          (fun z _ => le_iSup (fun j => w j z) i) y
    _ ≤ ⨅ i, C * bergmanSup D₂ (w i) y := iInf_mono hcomp
    _ = C * ⨅ i, bergmanSup D₂ (w i) y := (ENNReal.mul_iInf_of_ne hC0 hCtop).symm
    _ = C * bergmanSup D₂ winf y := by
        rw [bergmanSup_iSup_weight hD₂ hwm hwmeas hlow hwinf₂ hy]

end

end Hironaka.QuantitativeRegularizationSingularWeight
