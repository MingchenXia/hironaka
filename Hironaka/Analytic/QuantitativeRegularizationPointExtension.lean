import Hironaka.Analytic.QuantitativeRegularizationCanonicalExtensions
import Hironaka.Analytic.QuantitativeRegularizationCanonicalLimit
import Hironaka.Analytic.HormanderL2Theorem

set_option autoImplicit false

/-!
# Value-preserving `L²` extension from a point, with a weight-independent constant

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`).

This is the analytic statement that Step 2 of Copy-4's regularization lemma actually uses, and
the only place in that proof where the constant is won *uniformly in the weight*.  Fix a bounded
convex open `D`, a point `x ∈ D`, a smooth cut-off `θ` equal to `1` on `ball x r`, and `f`
holomorphic near `tsupport θ`.  Then for every smooth psh weight `ϕ` on `D` there is a single
holomorphic `F` on a relatively compact open `K ∋ x` with

* `F x = f x`, and
* `∫_K |F|² e^{-ϕ} ≤ C · ∫_{tsupport θ} |f|² e^{-ϕ}`,

where `C = pointExtensionConst d r Mθ R S` depends only on the dimension, the cut-off data
`(r, Mθ)` and the size `(R, S)` of `K` — **not** on `ϕ`, and not on `f`.

Two hypotheses on `ϕ` are, however, genuinely restrictive and must be stated: `ϕ` is *smooth*
on `D`, and it is *bounded below* on `D` (`hBϕ`).  The upper bound `hϕupper` on `K` is not a
restriction — a continuous function is bounded above on a compact set — but `hBϕ` is: a smooth
psh function on a bounded open set need not be bounded below there.  It is removable, since it
is consumed only at points of a relatively compact `D' ⊆ D` inside
`Hironaka.PointPoleExtension`; that cleanup is recorded as an inbox issue rather than done here,
because it would change the statement of theorems other modules already use.

That independence is what makes Copy-4's overlap constant `C_B` independent of the background
form `ζ`: applied with `ϕ = m Ψ` for the *common* weight `Ψ` of two overlapping balls, it
compares the two Bergman sup-weights to within `C_B / m` with `C_B` fixed by the cover alone.

The proof runs Hörmander's estimate against the regularized pole weight
`Φ_δ = ϕ + (d+1) log(‖z-x‖² + δ²) + ‖z‖²` at the canonical radii `δ_i = 1/(i+1)`
(`Hironaka.QuantitativeRegularizationCanonicalExtensions`), extracts a locally uniform limit of
the `∂̄`-solutions on a small ball around `x` where they are holomorphic — the limit vanishes at
`x` (`Hironaka.QuantitativeRegularizationCanonicalLimit`) — and, along a further subsequence, a
locally uniform limit of the holomorphic corrections themselves on all of `K`.  The two limits
agree near `x`, which is what transfers the vanishing into the value `F x = f x`.

The weight here is smooth and bounded below; the singular weights of the regularization lemma
reach this statement through a truncation/mollification reduction in the style of
`Hironaka.OhsawaTakegoshiRegularReduction`, which is **not** carried out here.  That reduction is
not pure bookkeeping: truncating `ϕ` *enlarges* the weighted unit ball, so closing it needs a
decreasing normal-family limit of the Bergman sup-weights, not just monotone convergence.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Hironaka.QuantitativeRegularizationPointExtension

noncomputable section

open Hormander PointPole
open QuantitativeRegularizationCanonicalRadii
open QuantitativeRegularizationCanonicalWeights

variable {d : ℕ}

/-- The constant of the point extension: it involves only the dimension, the cut-off data
`(r, Mθ)` and the size `(R, S)` of the target region, never the weight. -/
def pointExtensionConst (d : ℕ) (r Mθ R S : ℝ) : ℝ :=
  2 + 4 * (Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹) * ((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2))

theorem pointExtensionConst_nonneg {r Mθ R S : ℝ} (hr : 0 < r) :
    0 ≤ pointExtensionConst d r Mθ R S := by
  have h1 : (0:ℝ) < (r ^ 2) ^ (d + 1) := by positivity
  have h2 : (0:ℝ) ≤ (R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2) := by positivity
  have h3 : (0:ℝ) ≤ Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹ := by positivity
  have : (0:ℝ) ≤ 4 * (Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹) *
      ((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2)) := by positivity
  simp only [pointExtensionConst]
  linarith

theorem pointExtensionConst_pos {r Mθ R S : ℝ} (hr : 0 < r) :
    0 < pointExtensionConst d r Mθ R S := by
  have h : (0:ℝ) ≤ 4 * (Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹) *
      ((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2)) := by positivity
  simp only [pointExtensionConst]
  linarith

/-- On a bounded region around `x` every canonical pole weight dominates a fixed positive
multiple of `e^{-ϕ}`.  The multiple depends only on the size of the region. -/
theorem le_canonicalWeight
    {ϕ : ComplexModel d → ℝ} {x z : ComplexModel d} {R S : ℝ}
    (hzx : ‖z - x‖ ≤ R) (hz : ‖z‖ ≤ S) (i : ℕ) :
    ENNReal.ofReal (((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2))⁻¹ * Real.exp (-ϕ z)) ≤
      canonicalWeight (d + 1) ϕ x i z := by
  have hRnn : (0:ℝ) ≤ R := le_trans (norm_nonneg _) hzx
  have hδ := canonicalRadius_pos i
  have hδ1 : canonicalRadius i ≤ 1 := by
    have := canonicalRadius_antitone (Nat.zero_le i)
    simpa [canonicalRadius] using this
  have hbase : ‖z - x‖ ^ 2 + canonicalRadius i ^ 2 ≤ R ^ 2 + 1 := by
    have h1 : ‖z - x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (z - x)]
    have h2 : canonicalRadius i ^ 2 ≤ 1 := by nlinarith
    linarith
  have hbasepos : (0:ℝ) < ‖z - x‖ ^ 2 + canonicalRadius i ^ 2 := by positivity
  have hpow : (‖z - x‖ ^ 2 + canonicalRadius i ^ 2) ^ (d + 1) ≤ (R ^ 2 + 1) ^ (d + 1) :=
    pow_le_pow_left₀ hbasepos.le hbase _
  have hpowpos : (0:ℝ) < (‖z - x‖ ^ 2 + canonicalRadius i ^ 2) ^ (d + 1) := by positivity
  have hA : ((R ^ 2 + 1) ^ (d + 1))⁻¹ ≤ ((‖z - x‖ ^ 2 + canonicalRadius i ^ 2) ^ (d + 1))⁻¹ := by
    gcongr
  have hB : Real.exp (-(S ^ 2)) ≤ Real.exp (-‖z‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [norm_nonneg z]
  have key : ((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2))⁻¹ * Real.exp (-ϕ z) ≤
      Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + canonicalRadius i ^ 2) ^ (d + 1))⁻¹ *
        Real.exp (-‖z‖ ^ 2) := by
    have hprod : ((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2))⁻¹ * Real.exp (-ϕ z)
        = Real.exp (-ϕ z) * ((R ^ 2 + 1) ^ (d + 1))⁻¹ * Real.exp (-(S ^ 2)) := by
      rw [mul_inv, show Real.exp (-(S ^ 2)) = (Real.exp (S ^ 2))⁻¹ from Real.exp_neg _]
      ring
    rw [hprod]
    refine mul_le_mul (mul_le_mul_of_nonneg_left hA (Real.exp_pos (-ϕ z)).le) hB
      (Real.exp_pos _).le (by positivity)
  calc ENNReal.ofReal (((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2))⁻¹ * Real.exp (-ϕ z))
      ≤ ENNReal.ofReal (Real.exp (-ϕ z) *
          ((‖z - x‖ ^ 2 + canonicalRadius i ^ 2) ^ (d + 1))⁻¹ * Real.exp (-‖z‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal key
    _ = canonicalWeight (d + 1) ϕ x i z := by
        rw [canonicalWeight, PointPole.exp_neg_poleWeight ϕ x hδ z]


/-- Montel with a fixed positive weight: a sequence of holomorphic functions with one uniform
weighted `L²` bound has a locally uniformly convergent subsequence whose limit obeys the same
bound.  This is `WeightedL2ExtensionLimit` with a constant domain, a constant weight and no
prescribed interpolation data. -/
theorem exists_subseq_locallyUniform_limit_of_weighted_bounds
    {U : Set (ComplexModel d)} (hU : IsOpen U)
    {w : ComplexModel d → ℝ≥0∞} (hwmeas : AEMeasurable w (volume.restrict U))
    (hwlow : ∀ z ∈ U, ∃ ρ > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball z ρ, ENNReal.ofReal δ ≤ w y)
    {F : ℕ → ComplexModel d → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ z in U, ENNReal.ofReal (‖F i z‖ ^ 2) * w z ≤ A) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel d → ℂ), StrictMono ψ ∧ DifferentiableOn ℂ G U ∧
      TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop U ∧
      ∫⁻ z in U, ENNReal.ofReal (‖G z‖ ^ 2) * w z ≤ A := by
  have hUconst : (⋃ _ : ℕ, U) = U := iUnion_const U
  obtain ⟨ψ, G, hψ, hG, hconv, -, hGint⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds
      (U := fun _ : ℕ => U) (w := fun _ : ℕ => w) (α := Empty)
      (ι := fun e : Empty => e.elim) (g := fun e : Empty => e.elim)
      (fun _ => hU) (fun _ _ _ => subset_rfl)
      (fun _ _ => monotone_const) (fun _ => by rw [hUconst]; exact hwmeas)
      (by rw [hUconst]; exact hwlow) (fun _ => hF _) (fun _ e _ => e.elim) hA
      hbound
  refine ⟨ψ, G, hψ, ?_, ?_, ?_⟩
  · rw [← hUconst]; exact hG
  · rw [← hUconst]; exact hconv
  · have := hGint
    rw [hUconst] at this
    simpa using this


/-- **Value-preserving `L²` extension from a point, with a weight-independent constant**
(Copy-4, `lem:regularization`, Step 2).

`F` is holomorphic on `K`, takes the value `f x` at `x`, and its weighted `L²` norm on `K` is
bounded by `pointExtensionConst d r Mθ R S` times the weighted norm of `f` on `tsupport θ`.
The constant involves only the dimension, the cut-off data and the size of `K`: it does not
depend on the weight `ϕ`, which is what makes Copy-4's overlap constant independent of the
background form. -/
theorem exists_pointExtension_of_smooth_weight (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W) (htsD : tsupport θ ⊆ D)
    {f : ComplexModel d → ℂ} (hf : DifferentiableOn ℂ f W)
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {K Kc : Set (ComplexModel d)} (hKo : IsOpen K) (hKKc : K ⊆ Kc) (hKc : IsCompact Kc)
    (hKcD : Kc ⊆ D) (hxK : x ∈ K)
    {B R S : ℝ} (hϕupper : ∀ z ∈ K, ϕ z ≤ B) (hnormR : ∀ z ∈ K, ‖z - x‖ ≤ R)
    (hnormS : ∀ z ∈ K, ‖z‖ ≤ S) :
    ∃ F : ComplexModel d → ℂ, DifferentiableOn ℂ F K ∧ F x = f x ∧
      ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) ≤
        ENNReal.ofReal (pointExtensionConst d r Mθ R S *
          ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-ϕ z)) := by
  classical
  have hKD : K ⊆ D := hKKc.trans hKcD
  have hϕK : ContinuousOn ϕ K := hϕ.continuousOn.mono hKD
  -- the weight `e^{-ϕ}` on `K`
  set wϕ : ComplexModel d → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-ϕ z)) with hwϕ
  -- the right-hand side of the Hörmander bound
  set Iθ : ℝ := ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-ϕ z) with hIθ
  set A : ℝ≥0∞ := ENNReal.ofReal (2 * (Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹) * Iθ) with hAdef
  have hAtop : A ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the Hörmander family at the canonical radii
  obtain ⟨G, hGdiff, hGbound⟩ :=
    QuantitativeRegularizationCanonicalExtensions.exists_canonical_poleExtension_residual_family
      (p := d + 1) (hormanderL2Estimate d) hDo hDc hDb hr hϕ hϕL hBϕ x hθ hθcs hθ1 hW hts
      htsD hf hMθ hKo hKKc hKc hKcD
  -- the `∂̄`-solutions, holomorphic on the small ball where `θ = 1`
  set u : ℕ → ComplexModel d → ℂ := fun i z => PointPole.cutProd θ f z - G i z with hu
  set K₀ : Set (ComplexModel d) := K ∩ ball x r with hK₀
  have hK₀o : IsOpen K₀ := hKo.inter isOpen_ball
  have hxK₀ : x ∈ K₀ := ⟨hxK, mem_ball_self hr⟩
  have hballW : ball x r ⊆ W := by
    intro z hz
    refine hts (subset_tsupport θ ?_)
    simp only [Function.mem_support, hθ1 z hz]
    exact one_ne_zero
  have hcutEq : ∀ z ∈ ball x r, PointPole.cutProd θ f z = f z := by
    intro z hz
    simp [PointPole.cutProd, hθ1 z hz]
  have hcutDiff : DifferentiableOn ℂ (PointPole.cutProd θ f) K₀ :=
    (hf.mono (fun z hz => hballW hz.2)).congr (fun z hz => hcutEq z hz.2)
  have hudiff : ∀ i, DifferentiableOn ℂ (u i) K₀ := fun i =>
    hcutDiff.sub ((hGdiff i).mono inter_subset_left)
  have hubound : ∀ i, ∫⁻ z in K₀, ENNReal.ofReal (‖u i z‖ ^ 2) *
      canonicalWeight (d + 1) ϕ x i z ≤ A :=
    fun i => (lintegral_mono_set inter_subset_left).trans (hGbound i)
  obtain ⟨ψ, uLim, hψ, huLimdiff, huLimconv, huLimx, -⟩ :=
    QuantitativeRegularizationCanonicalLimit.exists_subseq_differentiableOn_vanishing_limit_of_canonical_weighted_bounds
      hK₀o hxK₀ (hϕK.mono inter_subset_left) hudiff hAtop hubound hd
      (fun z hz => hϕupper z hz.1) (fun z hz => hnormR z hz.1)
  -- the weight comparison on `K`
  set κ : ℝ := ((R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2))⁻¹ with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    positivity
  have hwle : ∀ (i : ℕ), ∀ z ∈ K,
      wϕ z ≤ ENNReal.ofReal κ⁻¹ * canonicalWeight (d + 1) ϕ x i z := by
    intro i z hz
    have h1 : ENNReal.ofReal (κ * Real.exp (-ϕ z)) ≤ canonicalWeight (d + 1) ϕ x i z := by
      rw [hκ]
      exact le_canonicalWeight (hnormR z hz) (hnormS z hz) i
    have h2 : wϕ z = ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (κ * Real.exp (-ϕ z)) := by
      rw [hwϕ, ← ENNReal.ofReal_mul (by positivity)]
      field_simp
    rw [h2]
    exact _root_.mul_le_mul_right h1 _
  -- measurability data
  have hcutCD : ContDiff ℝ ∞ (PointPole.cutProd θ f) := PointPole.contDiff_cutProd hW hθ hf hts
  have hwmeas : AEMeasurable wϕ (volume.restrict K) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact ContinuousOn.aemeasurable
      (Real.continuous_exp.comp_continuousOn hϕK.neg) hKo.measurableSet
  have hcutmeas : AEMeasurable (fun z => ENNReal.ofReal
      (‖PointPole.cutProd θ f z‖ ^ 2) * wϕ z) (volume.restrict K) :=
    ((ENNReal.measurable_ofReal.comp
      ((hcutCD.continuous.norm.pow 2).measurable)).aemeasurable).mul hwmeas
  -- the `L²` bound of the `∂̄`-solutions in the plain weight `e^{-ϕ}`
  have huwbound : ∀ i, ∫⁻ z in K, ENNReal.ofReal (‖u i z‖ ^ 2) * wϕ z ≤
      ENNReal.ofReal κ⁻¹ * A := by
    intro i
    calc ∫⁻ z in K, ENNReal.ofReal (‖u i z‖ ^ 2) * wϕ z
        ≤ ∫⁻ z in K, ENNReal.ofReal κ⁻¹ *
            (ENNReal.ofReal (‖u i z‖ ^ 2) * canonicalWeight (d + 1) ϕ x i z) := by
          refine setLIntegral_mono' hKo.measurableSet fun z hz => ?_
          calc ENNReal.ofReal (‖u i z‖ ^ 2) * wϕ z
              ≤ ENNReal.ofReal (‖u i z‖ ^ 2) *
                  (ENNReal.ofReal κ⁻¹ * canonicalWeight (d + 1) ϕ x i z) :=
                _root_.mul_le_mul_right (hwle i z hz) _
            _ = ENNReal.ofReal κ⁻¹ *
                  (ENNReal.ofReal (‖u i z‖ ^ 2) * canonicalWeight (d + 1) ϕ x i z) := by
                ring
      _ = ENNReal.ofReal κ⁻¹ * ∫⁻ z in K, ENNReal.ofReal (‖u i z‖ ^ 2) *
            canonicalWeight (d + 1) ϕ x i z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal κ⁻¹ * A := by
          refine _root_.mul_le_mul_right ?_ _
          simpa only [hu] using hGbound i
  -- the weighted norm of the cut-off product
  have hIθint : IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-ϕ z)) (tsupport θ) := by
    refine ContinuousOn.integrableOn_compact hθcs ?_
    exact ((hf.continuousOn.mono hts).norm.pow 2).mul
      (Real.continuous_exp.comp_continuousOn (hϕ.continuousOn.mono htsD).neg)
  have hIθlint : ∫⁻ z in tsupport θ, ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-ϕ z)) =
      ENNReal.ofReal Iθ := by
    rw [hIθ]
    exact (ofReal_integral_eq_lintegral_ofReal hIθint
      (Eventually.of_forall fun z => by positivity)).symm
  have hcutbound : ∫⁻ z in K, ENNReal.ofReal (‖PointPole.cutProd θ f z‖ ^ 2) * wϕ z ≤
      ENNReal.ofReal Iθ := by
    rw [← hIθlint, ← lintegral_indicator hKo.measurableSet,
      ← lintegral_indicator (isClosed_tsupport θ).measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hzK : z ∈ K
    · by_cases hzt : z ∈ tsupport θ
      · rw [indicator_of_mem hzK, indicator_of_mem hzt, hwϕ,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ‖PointPole.cutProd θ f z‖ ^ 2 ≤ ‖f z‖ ^ 2 := by
          have hnorm : ‖PointPole.cutProd θ f z‖ = |θ z| * ‖f z‖ := by
            simp [PointPole.cutProd]
          have hθ2 : |θ z| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (θ z), hθle z]
          rw [hnorm, mul_pow]
          nlinarith [hθ2, sq_nonneg ‖f z‖]
        nlinarith [Real.exp_pos (-ϕ z), norm_nonneg (PointPole.cutProd θ f z)]
      · rw [indicator_of_mem hzK, indicator_of_notMem hzt]
        have hz0 : θ z = 0 := image_eq_zero_of_notMem_tsupport hzt
        simp [PointPole.cutProd, hz0]
    · rw [indicator_of_notMem hzK]
      exact zero_le
  -- the uniform bound for the holomorphic corrections themselves
  set A' : ℝ≥0∞ := 2 * ENNReal.ofReal Iθ + 2 * (ENNReal.ofReal κ⁻¹ * A) with hA'
  have hA'top : A' ≠ ⊤ := by
    rw [hA']
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top, ?_⟩
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop)
  have hGwbound : ∀ i, ∫⁻ z in K, ENNReal.ofReal (‖G i z‖ ^ 2) * wϕ z ≤ A' := by
    intro i
    have hstep : ∫⁻ z in K, ENNReal.ofReal (‖G i z‖ ^ 2) * wϕ z ≤
        ∫⁻ z in K, (2 * (ENNReal.ofReal (‖PointPole.cutProd θ f z‖ ^ 2) * wϕ z) +
          2 * (ENNReal.ofReal (‖u i z‖ ^ 2) * wϕ z)) := by
      refine lintegral_mono fun z => ?_
      have hsq : ‖G i z‖ ^ 2 ≤
          2 * ‖PointPole.cutProd θ f z‖ ^ 2 + 2 * ‖u i z‖ ^ 2 := by
        have hG' : G i z = PointPole.cutProd θ f z - u i z := by
          simp only [hu]
          ring
        rw [hG']
        have h1 := norm_sub_le (PointPole.cutProd θ f z) (u i z)
        have h0 : (0:ℝ) ≤ ‖PointPole.cutProd θ f z - u i z‖ := norm_nonneg _
        nlinarith [norm_nonneg (PointPole.cutProd θ f z), norm_nonneg (u i z),
          sq_nonneg (‖PointPole.cutProd θ f z‖ - ‖u i z‖), h0, h1]
      calc ENNReal.ofReal (‖G i z‖ ^ 2) * wϕ z
          ≤ ENNReal.ofReal (2 * ‖PointPole.cutProd θ f z‖ ^ 2 + 2 * ‖u i z‖ ^ 2) * wϕ z := by
            gcongr
        _ = (2 * ENNReal.ofReal (‖PointPole.cutProd θ f z‖ ^ 2) +
              2 * ENNReal.ofReal (‖u i z‖ ^ 2)) * wϕ z := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            norm_num
        _ = 2 * (ENNReal.ofReal (‖PointPole.cutProd θ f z‖ ^ 2) * wϕ z) +
              2 * (ENNReal.ofReal (‖u i z‖ ^ 2) * wϕ z) := by ring
    refine hstep.trans ?_
    rw [lintegral_add_left' (hcutmeas.const_mul 2)]
    rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
      lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), hA']
    exact add_le_add (_root_.mul_le_mul_right hcutbound 2)
      (_root_.mul_le_mul_right (huwbound i) 2)
  -- Montel for the corrections on all of `K`
  have hIθ0 : 0 ≤ Iθ := by
    rw [hIθ]
    exact integral_nonneg fun z => by positivity
  have hwlow : ∀ z ∈ K, ∃ ρ > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball z ρ, ENNReal.ofReal δ ≤ wϕ y := by
    intro z hz
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hKo z hz
    refine ⟨ρ, hρ, Real.exp (-B), Real.exp_pos _, fun y hy => ?_⟩
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have := hϕupper y (hball hy)
    linarith
  obtain ⟨ψ', F, hψ', hFdiff, hFconv, hFbound⟩ :=
    exists_subseq_locallyUniform_limit_of_weighted_bounds (U := K) hKo hwmeas hwlow
      (F := fun i => G (ψ i)) (fun i => hGdiff (ψ i)) hA'top (fun i => hGwbound (ψ i))
  refine ⟨F, hFdiff, ?_, ?_⟩
  · -- the value at `x`
    have h1 : Filter.Tendsto (fun i => G (ψ (ψ' i)) x) atTop (𝓝 (F x)) :=
      hFconv.tendsto_at hxK
    have h2 : Filter.Tendsto (fun i => u (ψ (ψ' i)) x) atTop (𝓝 (uLim x)) :=
      (huLimconv.tendsto_at hxK₀).comp hψ'.tendsto_atTop
    have h3 : Filter.Tendsto (fun i => G (ψ (ψ' i)) x) atTop
        (𝓝 (PointPole.cutProd θ f x - uLim x)) := by
      have heq : (fun i => G (ψ (ψ' i)) x) =
          fun i => PointPole.cutProd θ f x - u (ψ (ψ' i)) x := by
        funext i
        simp only [hu]
        ring
      rw [heq]
      exact tendsto_const_nhds.sub h2
    have h4 : F x = PointPole.cutProd θ f x - uLim x := tendsto_nhds_unique h1 h3
    rw [h4, huLimx, sub_zero]
    exact hcutEq x (mem_ball_self hr)
  · -- the `L²` bound
    refine hFbound.trans (le_of_eq ?_)
    have hκinv : κ⁻¹ = (R ^ 2 + 1) ^ (d + 1) * Real.exp (S ^ 2) := by
      rw [hκ]; exact inv_inv _
    have hcnn : (0:ℝ) ≤ 2 * (Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹) * Iθ :=
      mul_nonneg (by positivity) hIθ0
    have hκinvnn : (0:ℝ) ≤ κ⁻¹ := le_of_lt (inv_pos.mpr hκpos)
    have e0 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
    have e1 : (2 : ℝ≥0∞) * ENNReal.ofReal Iθ = ENNReal.ofReal (2 * Iθ) := by
      rw [e0, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    have e2 : (2 : ℝ≥0∞) * (ENNReal.ofReal κ⁻¹ * A) =
        ENNReal.ofReal (2 * (κ⁻¹ * (2 * (Mθ ^ 2 * ((r ^ 2) ^ (d + 1))⁻¹) * Iθ))) := by
      rw [hAdef, ← ENNReal.ofReal_mul hκinvnn, e0,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [hA', e1, e2, ← ENNReal.ofReal_add (by linarith) (by positivity)]
    congr 1
    rw [pointExtensionConst, hκinv]
    ring


/-- The same extension with both sides written as lower Lebesgue integrals — the shape the
Bergman-kernel comparison consumes, since the weighted Bergman unit ball is defined by an
`lintegral` bound. -/
theorem exists_pointExtension_lintegral_of_smooth_weight (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W) (htsD : tsupport θ ⊆ D)
    {f : ComplexModel d → ℂ} (hf : DifferentiableOn ℂ f W)
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {K Kc : Set (ComplexModel d)} (hKo : IsOpen K) (hKKc : K ⊆ Kc) (hKc : IsCompact Kc)
    (hKcD : Kc ⊆ D) (hxK : x ∈ K)
    {B R S : ℝ} (hϕupper : ∀ z ∈ K, ϕ z ≤ B) (hnormR : ∀ z ∈ K, ‖z - x‖ ≤ R)
    (hnormS : ∀ z ∈ K, ‖z‖ ≤ S) :
    ∃ F : ComplexModel d → ℂ, DifferentiableOn ℂ F K ∧ F x = f x ∧
      ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) ≤
        ENNReal.ofReal (pointExtensionConst d r Mθ R S) *
          ∫⁻ z in tsupport θ, ENNReal.ofReal (‖f z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-ϕ z)) := by
  obtain ⟨F, hF1, hF2, hF3⟩ :=
    exists_pointExtension_of_smooth_weight hd hDo hDc hDb hϕ hϕL hBϕ x hr hθ hθcs hθ1 hθle
      hW hts htsD hf hMθ hKo hKKc hKc hKcD hxK hϕupper hnormR hnormS
  refine ⟨F, hF1, hF2, hF3.trans ?_⟩
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-ϕ z)) (tsupport θ) := by
    refine ContinuousOn.integrableOn_compact hθcs ?_
    exact ((hf.continuousOn.mono hts).norm.pow 2).mul
      (Real.continuous_exp.comp_continuousOn (hϕ.continuousOn.mono htsD).neg)
  have hIeq : ENNReal.ofReal (∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-ϕ z)) =
      ∫⁻ z in tsupport θ, ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z => by positivity)]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul (pointExtensionConst_nonneg (d := d) (Mθ := Mθ) (R := R) (S := S) hr),
    hIeq]

end

end Hironaka.QuantitativeRegularizationPointExtension
