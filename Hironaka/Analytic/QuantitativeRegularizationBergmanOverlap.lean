import Hironaka.Analytic.QuantitativeRegularizationPointExtension
import Hironaka.Analytic.BergmanSupWeight
import Hironaka.Analytic.BergmanHolomorphicMultiplier

set_option autoImplicit false

/-!
# The overlap comparison of two Bergman sup-weights

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`).

Copy-4 compares the Bergman weights of two overlapping coordinate balls `B_j`, `B_l` computed
against the **same** weight `Ψ` — the common potential of the two balls, obtained from the
local potentials `h_j`, `h_l` by the holomorphic multipliers `e^{m a_j / 2}`, which are
*isometries* of the weighted spaces.  That common-weight formulation is what removes the
background form `ζ` from the comparison constant.

`bergmanSup_le_of_pointExtension` is that comparison: with a cut-off `θ` equal to `1` near the
point, supported in `B_j`, and a `∂̄`-solve on `B_l`,

  `bergmanSup B_j w x ≤ C · bergmanSup B_l w x`,   `w = e^{-ϕ}`,

with `C = pointExtensionConst d r Mθ R S` independent of `ϕ`.  Dividing by `m` and taking
logarithms — `ϕ = m Ψ`, `bergmanLog = log ∘ bergmanSup` — this is Copy-4's
`ψ_{j,m} ≤ ψ_{l,m} + C_B/m` with `C_B = log C` fixed by the cover alone.

**Scope.**  The weight here is a *smooth* psh `ϕ`, which is what Hörmander's estimate consumes.
The regularization lemma applies this with `ϕ = m Ψ` for a genuinely singular psh `Ψ`; the
passage from smooth to singular weights is the truncation/mollification reduction of
`Hironaka.OhsawaTakegoshiRegularReduction`, and is not carried out here.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Hironaka.QuantitativeRegularizationBergmanOverlap

noncomputable section

open BergmanSupWeight
open QuantitativeRegularizationPointExtension
open BergmanHolomorphicMultiplier

variable {d : ℕ}

/-- **The overlap comparison of two Bergman sup-weights** (Copy-4, `lem:regularization`,
Step 2).  The constant does not depend on the weight `ϕ`. -/
theorem bergmanSup_le_of_pointExtension (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {Bj : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hts : tsupport θ ⊆ Bj)
    (htsD : tsupport θ ⊆ D) {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bl Blc : Set (ComplexModel d)} (hBlo : IsOpen Bl) (hBlBlc : Bl ⊆ Blc)
    (hBlc : IsCompact Blc) (hBlcD : Blc ⊆ D) (hxBl : x ∈ Bl)
    {B R S : ℝ} (hϕupper : ∀ z ∈ Bl, ϕ z ≤ B) (hnormR : ∀ z ∈ Bl, ‖z - x‖ ≤ R)
    (hnormS : ∀ z ∈ Bl, ‖z‖ ≤ S) :
    bergmanSup Bj (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
      ENNReal.ofReal (pointExtensionConst d r Mθ R S) *
        bergmanSup Bl (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x := by
  refine bergmanSup_le fun f hf => ?_
  obtain ⟨hfdiff, hfnorm⟩ := hf
  obtain ⟨F, hF1, hF2, hF3⟩ :=
    exists_pointExtension_lintegral_of_smooth_weight hd hDo hDc hDb hϕ hϕL hBϕ x hr hθ hθcs
      hθ1 hθle hBjo hts htsD hfdiff hMθ hBlo hBlBlc hBlc hBlcD hxBl hϕupper hnormR hnormS
  have hsmall : ∫⁻ z in tsupport θ, ENNReal.ofReal (‖f z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-ϕ z)) ≤ 1 := (lintegral_mono_set hts).trans hfnorm
  have hFbound : ∫⁻ z in Bl, ENNReal.ofReal (‖F z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-ϕ z)) ≤
        ENNReal.ofReal (pointExtensionConst d r Mθ R S) := by
    refine hF3.trans ?_
    calc ENNReal.ofReal (pointExtensionConst d r Mθ R S) *
          ∫⁻ z in tsupport θ, ENNReal.ofReal (‖f z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-ϕ z))
        ≤ ENNReal.ofReal (pointExtensionConst d r Mθ R S) * 1 := by gcongr
      _ = ENNReal.ofReal (pointExtensionConst d r Mθ R S) := mul_one _
  have hC0 : ENNReal.ofReal (pointExtensionConst d r Mθ R S) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pointExtensionConst_pos hr)).ne'
  have hkey := bergmanSup_extremal hF1 hC0 ENNReal.ofReal_ne_top hFbound x
  rwa [hF2] at hkey


/-- **The logarithmic form of the common-weight comparison.**  The two Bergman weights for the
same weight `ϕ` differ by at most `log C`, with `C` independent of `ϕ`.  With `ϕ = m Ψ` and
`Ψ_{•,m} = m⁻¹ · bergmanLog` this is `Ψ_{j,m} ≤ Ψ_{l,m} + (log C)/m`; see the module docstring
for what still separates it from Copy-4's `eq:reg-overlap`. -/
theorem bergmanLog_le_add_log_of_pointExtension (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {Bj : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hts : tsupport θ ⊆ Bj)
    (htsD : tsupport θ ⊆ D) {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bl Blc : Set (ComplexModel d)} (hBlo : IsOpen Bl) (hBlBlc : Bl ⊆ Blc)
    (hBlc : IsCompact Blc) (hBlcD : Blc ⊆ D) (hxBl : x ∈ Bl)
    {B R S : ℝ} (hϕupper : ∀ z ∈ Bl, ϕ z ≤ B) (hnormR : ∀ z ∈ Bl, ‖z - x‖ ≤ R)
    (hnormS : ∀ z ∈ Bl, ‖z‖ ≤ S) :
    bergmanLog Bj (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
      bergmanLog Bl (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x +
        (Real.log (pointExtensionConst d r Mθ R S) : EReal) := by
  have hcmp := bergmanSup_le_of_pointExtension hd hDo hDc hDb hϕ hϕL hBϕ x hr hθ hθcs hθ1
    hθle hBjo hts htsD hMθ hBlo hBlBlc hBlc hBlcD hxBl hϕupper hnormR hnormS
  calc bergmanLog Bj (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x
      ≤ ENNReal.log (ENNReal.ofReal (pointExtensionConst d r Mθ R S) *
          bergmanSup Bl (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x) :=
        ENNReal.log_monotone hcmp
    _ = (Real.log (pointExtensionConst d r Mθ R S) : EReal) +
          bergmanLog Bl (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x := by
        rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (pointExtensionConst_pos hr)]
        rfl
    _ = bergmanLog Bl (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x +
          (Real.log (pointExtensionConst d r Mθ R S) : EReal) := add_comm _ _


/-- **Copy-4 `eq:reg-overlap`, transported to the own weights of the two balls.**

Each ball carries its own weight `e^{-2 Re a_•} · w`, obtained from the common `w = e^{-ϕ}` by
the holomorphic multiplier of `Hironaka.BergmanHolomorphicMultiplier`.  The two correction
factors `e^{-2 Re a_•(x)}` are exactly Copy-4's `φ_{•,m} = Ψ_{•,m} + H_{jl}`: in the
regularization lemma one takes `ϕ = m Ψ` and `-2 Re a_• = m (h_• - H_{jl})`, so both sides
acquire the *same* `m H_{jl}(x)`, which cancels, and this inequality becomes

  `φ_{j,m} ≤ φ_{l,m} + (log C)/m`,

which is `eq:reg-overlap` with `C_B = log C`.  Copy-4 also needs the symmetric statement; it is
this theorem with `j` and `l` exchanged and a second cut-off. -/
theorem bergmanSup_le_of_pointExtension_ownWeights (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {Bj : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hts : tsupport θ ⊆ Bj)
    (htsD : tsupport θ ⊆ D) {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bl Blc : Set (ComplexModel d)} (hBlo : IsOpen Bl) (hBlBlc : Bl ⊆ Blc)
    (hBlc : IsCompact Blc) (hBlcD : Blc ⊆ D) (hxBl : x ∈ Bl)
    {B R S : ℝ} (hϕupper : ∀ z ∈ Bl, ϕ z ≤ B) (hnormR : ∀ z ∈ Bl, ‖z - x‖ ≤ R)
    (hnormS : ∀ z ∈ Bl, ‖z‖ ≤ S)
    {aj al : ComplexModel d → ℂ} (haj : DifferentiableOn ℂ aj Bj)
    (hal : DifferentiableOn ℂ al Bl) :
    ENNReal.ofReal (Real.exp (-(2 * (aj x).re))) *
        bergmanSup Bj (fun z => ENNReal.ofReal (Real.exp (-(2 * (aj z).re))) *
          ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
      ENNReal.ofReal (pointExtensionConst d r Mθ R S) *
        (ENNReal.ofReal (Real.exp (-(2 * (al x).re))) *
          bergmanSup Bl (fun z => ENNReal.ofReal (Real.exp (-(2 * (al z).re))) *
            ENNReal.ofReal (Real.exp (-ϕ z))) x) := by
  have hcancel : ∀ b : ComplexModel d → ℂ, ∀ S' : ℝ≥0∞,
      ENNReal.ofReal (Real.exp (-(2 * (b x).re))) *
        (ENNReal.ofReal (Real.exp (2 * (b x).re)) * S') = S' := by
    intro b S'
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  rw [bergmanSup_exp_weight haj, bergmanSup_exp_weight hal, hcancel aj, hcancel al]
  exact bergmanSup_le_of_pointExtension hd hDo hDc hDb hϕ hϕL hBϕ x hr hθ hθcs hθ1 hθle
    hBjo hts htsD hMθ hBlo hBlBlc hBlc hBlcD hxBl hϕupper hnormR hnormS

end

end Hironaka.QuantitativeRegularizationBergmanOverlap
